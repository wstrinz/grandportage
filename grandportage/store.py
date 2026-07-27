"""The graph store: an append-only event log, folded deterministically.

The graph is the state.  Not the transcript, not the chat history, not a
directory of markdown -- the graph.  After three weeks a fresh agent reads a
typed artifact instead of reconstructing intent from 400 messages.

Two properties earn the append-only-log shape, and neither is decoration:

RESUMABILITY.  `.portage/graph.jsonl` is the whole of the campaign state.
Folding it is deterministic and total: same log, same graph, every time.

SAFE FAN-OUT.  Merging two branches is CONCATENATING their logs and folding
again.  Re-declaring an entity with byte-identical content is idempotent, so
branches that share a common prefix merge silently; re-declaring it with
DIFFERENT content is a hard error naming both versions.  So a merge of twenty
agent branches either composes or fails loudly, which is the failure mode you
want when the alternative is a silently blended graph.
"""

import json
import os

from . import kernel as K

GRAPH_DIR = ".portage"
GRAPH_FILE = "graph.jsonl"

# Event kinds, and the entity collection each one populates.
EV_CERTIFICATE = "certificate"
EV_MODEL = "model"
EV_EDGE = "edge"
EV_CLAIM = "claim"
EV_INFERENCE = "inference"
EV_BUILT_BY = "built_by"
EV_PARTITION = "partition"
EV_SAME_AS = "same_as"
EV_NOTE = "note"          # free-form, carried but never interpreted

EVENT_KINDS = (EV_CERTIFICATE, EV_MODEL, EV_EDGE, EV_CLAIM, EV_INFERENCE,
               EV_BUILT_BY, EV_PARTITION, EV_SAME_AS, EV_NOTE)

# Severities an inference may override to.  Named here rather than imported so
# the store stays the bottom layer with no dependency on the checker;
# `test_store.py` pins this against `check.SEVERITY_ORDER` so the two cannot
# drift, which is the same trick the CAS boundary uses to keep its identifier
# check and its program text derived from one source.
C_SEVERITIES = ("DEBT", "TRIAGE", "UNSOUND_PREMISE", "UNSOUND_CONCLUSION")


class GraphError(ValueError):
    """The log does not fold into a well-formed graph."""


def _require(cond, msg):
    if not cond:
        raise GraphError(msg)


def _canon(ev):
    """Canonical form of an event, for the idempotent-redeclaration test.

    Compared as sorted JSON so that key order and whitespace in the log cannot
    turn an identical redeclaration into a spurious conflict.
    """
    return json.dumps(ev, sort_keys=True, separators=(",", ":"))


class Graph(object):
    """The folded state.  Plain dicts throughout -- the checker walks this, the
    CLI prints it, and neither needs a class hierarchy to do so."""

    def __init__(self):
        self.certificates = dict(K.BUILTIN_CERTIFICATES)
        self.cert_source = {k: "builtin" for k in K.BUILTIN_CERTIFICATES}
        self.models = {}
        self.edges = {}
        self.claims = {}
        self.inferences = {}       # id -> inference dict
        self.inference_order = []  # declaration order, for stable reporting
        self.built_by = {}         # model id -> [inference id, ...]
        self.partitions = {}       # id -> {parent, branches, exhaustive}
        self.aliases = {}          # id -> {models: [...], why}
        self.notes = []
        self._seen = {}            # (kind, id) -> canonical event

    # -- fold ---------------------------------------------------------------
    def apply(self, ev, source="<log>", lineno=0):
        where = "%s:%d" % (source, lineno)
        _require(isinstance(ev, dict), "%s: event is not an object" % where)
        kind = ev.get("ev")
        _require(kind in EVENT_KINDS,
                 "%s: unknown event kind %r (known: %s)"
                 % (where, kind, ", ".join(EVENT_KINDS)))

        if kind == EV_NOTE:
            self.notes.append(ev)
            return

        if kind == EV_BUILT_BY:
            _require("model" in ev and "inference" in ev,
                     "%s: built_by needs `model` and `inference`" % where)
            builders = self.built_by.setdefault(ev["model"], [])
            if ev["inference"] not in builders:
                builders.append(ev["inference"])
            return

        eid = ev.get("id")
        _require(eid, "%s: %s event has no `id`" % (where, kind))

        # Idempotent redeclaration; loud conflict.  This is the whole of the
        # merge story.
        key = (kind, eid)
        canon = _canon(ev)
        if key in self._seen:
            if self._seen[key] == canon:
                return
            raise GraphError(
                "%s: conflicting redeclaration of %s %r.\n"
                "  already: %s\n"
                "  now    : %s\n"
                "Two branches declared the same entity differently.  Resolve "
                "it in the source graphs; the fold will not blend them."
                % (where, kind, eid, self._seen[key], canon))
        self._seen[key] = canon

        getattr(self, "_apply_" + kind)(ev, where)

    def _apply_certificate(self, ev, where):
        # A BUILT-IN CANNOT BE REDEFINED FROM A GRAPH.
        #
        # The registry is seeded from BUILTIN_CERTIFICATES but the redeclaration
        # table starts empty, so the idempotent-redeclaration guard -- which is
        # the whole of the merge story -- never saw the built-ins.  A graph
        # event naming `UNIT_IDEAL_CERT` therefore overwrote it silently.
        #
        # That is the highest-leverage overwrite in the system: `derive_scope`
        # reads this dict to decide FIELD-INDEPENDENCE, so flipping one entry
        # to base_changes=false downgrades every SCHEME-scoped emptiness in the
        # campaign, and flipping one to true mints field-independence that was
        # never proved.  Neither produces a finding; both just change the answer.
        #
        # Restating a built-in with the SAME verdict stays legal, because
        # idempotent redeclaration is how branches merge.
        prior = K.BUILTIN_CERTIFICATES.get(ev["id"])
        if prior is not None and ev.get("base_changes") != prior:
            raise GraphError(
                "%s: certificate %r is a BUILT-IN declaring base_changes=%s, "
                "and this event redefines it to %r.  The certificate registry "
                "is what `derive_scope` reads to decide field-independence, so "
                "silently overriding a built-in changes the scope of every "
                "emptiness that cites it.  If the built-in is wrong, that is a "
                "kernel change with a test, not a graph event; if you need "
                "different semantics, register them under a NEW name."
                % (where, ev["id"], prior, ev.get("base_changes")))
        _require(isinstance(ev.get("base_changes"), bool),
                 "%s: certificate %r must declare `base_changes` as a boolean. "
                 "Does an emptiness proved by this certificate survive "
                 "enlarging the field?" % (where, ev["id"]))
        _require(ev.get("why"),
                 "%s: certificate %r must declare `why`.  An unexplained "
                 "base-change verdict is the assertion this system exists to "
                 "refuse." % (where, ev["id"]))
        self.certificates[ev["id"]] = ev["base_changes"]
        self.cert_source[ev["id"]] = where

    def _apply_same_as(self, ev, where):
        """Two model ids that denote ONE object.

        THE FAN-OUT RISK, and the first real merge produced it.  Two agents,
        working the same campaign in isolation, both had to construct the
        saturated system.  They agreed on a name for it -- so the fold raised a
        loud conflict on their differing descriptions, which is the case that
        was already unit-tested and works.

        The dangerous case is the other one: two ids for one object.  Nothing
        collides, the merge composes silently, and the graph now contains two
        models for one thing.  It folds cleanly and it is wrong, and no rule
        catches it, because from the inside a duplicate is indistinguishable
        from two genuinely different objects.

        `supersedes` is the wrong shape here and it is worth saying why:
        NEITHER BRANCH IS WRONG.  They described one object from two
        directions, and asking one to retract is asking it to lose the
        description that made sense of its own work.  An alias records the
        identity without either side giving anything up.

        What the tool can check is CONSISTENCY, not identity: two models
        declared to be one object must not disagree about their field or their
        chart.  Whether they really are the same object is mathematics.
        """
        models = ev.get("models") or []
        _require(isinstance(models, list) and len(models) >= 2,
                 "%s: same_as %r needs at least two `models`" % (where, ev["id"]))
        _require(ev.get("why"),
                 "%s: same_as %r must declare `why` -- what establishes that "
                 "these are one object?  Two agents naming the same thing "
                 "differently is the expected case; two agents naming DIFFERENT "
                 "things the same is the one this must not paper over."
                 % (where, ev["id"]))
        a = dict(ev)
        a["models"] = list(models)
        self.aliases[ev["id"]] = a

    def _apply_partition(self, ev, where):
        """A parent model split into branches, with its exhaustiveness stated.

        THE GAP TWO INDEPENDENT AGENTS WALKED INTO.  A model in this kernel IS
        its solution set, and an edge asserts V(src) subset V(dst).  A CASE
        BRANCH is neither: "the gamma=4 case of this object" is not a
        relaxation of the object, it is a PIECE of it, and the type system had
        no word for that.

        So branches got typed as total containments, and the graph asserted
        V(REDUCED) subset V(G2) AND subset V(G3) AND subset V(G4) for three
        mutually exclusive targets -- consistent only if V(REDUCED) is empty,
        which was the thing under proof.  A degree count covering ONE branch
        then licensed emptiness of the WHOLE parent, and the agent's own prose
        said "branch" while the graph said "everything".

        A partition declares:

            parent      the model being split
            branches    the pieces; each must be a declared model
            exhaustive  the id of a CLAIM asserting the branches cover the
                        parent

        `exhaustive` must name a claim IN THE GRAPH.  The checker cannot verify
        that gamma in {2,3,4} really matches three branches -- that is
        mathematics.  What it can do is refuse to let the completeness premise
        live in a note, which is exactly where it went last time: carried,
        never typed, and invisible to every rule while the conclusion resting
        on it was reported clean.

        Orientation follows from what a branch IS: branch = parent AND
        condition, so V(branch) subset V(parent) and the edge runs
        BRANCH -> PARENT.  `check_partition` flags the reverse, which is the
        direction the mistake actually took.
        """
        _require(ev.get("parent"),
                 "%s: partition %r needs `parent`" % (where, ev["id"]))
        branches = ev.get("branches") or []
        _require(isinstance(branches, list) and len(branches) >= 2,
                 "%s: partition %r needs at least two `branches`; a split into "
                 "one piece is just the parent" % (where, ev["id"]))
        _require(ev.get("exhaustive"),
                 "%s: partition %r needs `exhaustive`: the id of a claim "
                 "asserting these branches COVER the parent.  Without it the "
                 "split proves nothing jointly -- emptiness on every branch "
                 "would say nothing about the parent -- and a completeness "
                 "premise recorded as prose is one no rule can see."
                 % (where, ev["id"]))
        _require(ev.get("why"),
                 "%s: partition %r must declare `why` -- what distinguishes "
                 "the branches?" % (where, ev["id"]))
        p = dict(ev)
        p["branches"] = list(branches)
        self.partitions[ev["id"]] = p

    def _apply_model(self, ev, where):
        declares = ev.get("declares") or {}
        _require(isinstance(declares, dict),
                 "%s: model %r `declares` must be {axis: [values]}"
                 % (where, ev["id"]))
        m = dict(ev)
        m["declares"] = {a: list(v) for a, v in declares.items()}
        m["touches"] = list(ev.get("touches") or [])
        m["reads"] = list(ev.get("reads") or [])
        # Axes on which this model ASSERTS coverage, i.e. claims to constrain
        # the object.  Only these are subject to the coverage rule: a model
        # that never claimed to bound anything at a place is not leaking there,
        # it is simply silent by design.
        m["coverage_axes"] = list(ev.get("coverage_axes") or [])
        self.models[ev["id"]] = m

    def _apply_edge(self, ev, where):
        _require(ev.get("type") in K.DECLARABLE_TYPES,
                 "%s: edge %r has type %r; declarable types are %s"
                 % (where, ev["id"], ev.get("type"),
                    ", ".join(K.DECLARABLE_TYPES)))
        _require(ev.get("src") and ev.get("dst"),
                 "%s: edge %r needs `src` and `dst`" % (where, ev["id"]))
        _require(ev.get("why"),
                 "%s: edge %r must declare `why` -- what information does this "
                 "step lose?" % (where, ev["id"]))
        if ev["type"] == K.UNTYPED:
            _require(ev.get("debt_why"),
                     "%s: edge %r is declared UNTYPED, which is a recorded "
                     "modelling debt.  It needs `debt_why`: say what is not yet "
                     "known about this step." % (where, ev["id"]))
        mk = ev.get("map_kind", K.IDENTITY_MAP)
        _require(mk in K.MAP_KINDS,
                 "%s: edge %r has map_kind %r; known: %s"
                 % (where, ev["id"], mk, ", ".join(K.MAP_KINDS)))
        if ev.get("supersedes"):
            _require(ev.get("discharge_kind"),
                     "%s: edge %r supersedes %r without saying HOW. A "
                     "supersession must declare `discharge_kind`: DERIVE (the "
                     "missing mathematics now exists), RETYPE (the relation "
                     "was mis-stated) or ACCEPT. Supersession transfers the "
                     "older edge's obligations; it does not clear them, and an "
                     "obligation may have been recorded as dischargeable only "
                     "one way."
                     % (where, ev["id"], ev["supersedes"]))
        e = dict(ev)
        e["map_kind"] = mk
        e["support"] = list(ev.get("support") or [])
        e["drops"] = list(ev.get("drops") or [])
        e["refinement"] = bool(ev.get("refinement"))
        self.edges[ev["id"]] = e

    def _apply_claim(self, ev, where):
        _require(ev.get("kind") in K.CLAIM_KINDS,
                 "%s: claim %r has kind %r; known: %s"
                 % (where, ev["id"], ev.get("kind"), ", ".join(K.CLAIM_KINDS)))
        _require(ev.get("model"), "%s: claim %r needs `model`" % (where, ev["id"]))
        _require(ev.get("statement"),
                 "%s: claim %r needs `statement`" % (where, ev["id"]))
        c = dict(ev)
        # Scope derivation happens at fold time, not at check time: a claim
        # whose declared scope contradicts its certificate is a malformed
        # graph, not a finding.  Making the safe path the only path.
        c["scope"] = K.derive_scope(
            ev["kind"], ev.get("certificate"), ev.get("scope"),
            certificates=self.certificates, claim_id=ev["id"])
        c["declared_scope"] = ev.get("scope")
        # Same discipline, same place: an IDENTITY claim that does not say
        # where its rewriting is valid is a malformed graph, not a finding.
        # UNKNOWN is always available, so this is a required field with an
        # honest answer rather than a required field people must invent.
        c["identity_origin"] = K.derive_identity_origin(
            ev["kind"], ev.get("identity_origin"), claim_id=ev["id"])
        # Same discipline for the other direction: emptiness needs a
        # certificate, existence needs to say how the point is known.
        c["witness_kind"] = K.derive_witness_kind(
            ev["kind"], ev.get("witness_kind"), claim_id=ev["id"])
        self.claims[ev["id"]] = c

    def _apply_inference(self, ev, where):
        """An inference has one or more PREMISES, each with its own path.

        THE GRAPH USED TO RECORD CHAINS BUT NOT JOINS.  `claim` was a single id
        and `path` a single route, so an argument combining two facts could not
        be written down at all.

        That is not a missing convenience.  `GI-BRIDGE` -- the defect this whole
        project was built around -- is a BAD JOIN: two computations sharing no
        variable, welded by a sentence.  So the tool detected bad joins by
        making good joins inexpressible, and the overflow went where overflow
        goes: a live run put the completeness premise of its central case
        analysis into a `note`, where nothing types it, because there was
        nowhere else to put it.

        Multi-premise form:

            {"ev": "inference", "id": ...,
             "premises": [{"claim": "C1", "path": [["E1","AGAINST"]]},
                          {"claim": "C2", "path": []}],
             "concludes_kind": "PREDICATE",
             "asserted": "..."}

        Every premise must transport to the SAME model, and that model is the
        conclusion point.  A premise with an empty path is one already at the
        conclusion, which is how a side condition enters.

        WHAT THIS DOES NOT CLAIM.  The checker verifies that each premise
        legitimately REACHES the conclusion point.  It does not verify that the
        premises ENTAIL the conclusion -- that is mathematics, and the kernel
        has never pretended to do mathematics.  What changes is that the
        premises are now IN THE GRAPH, so a reader can see what the argument
        rests on and a missing premise is a visible absence rather than an
        unwritten assumption.
        """
        _require(ev.get("claim") or ev.get("premises"),
                 "%s: inference %r needs `claim` or `premises`"
                 % (where, ev["id"]))
        _require(not (ev.get("claim") and ev.get("premises")),
                 "%s: inference %r declares both `claim` and `premises`; use "
                 "one form or the other" % (where, ev["id"]))
        _require(ev.get("asserted"),
                 "%s: inference %r needs `asserted` -- the conclusion in words, "
                 "as it was actually used" % (where, ev["id"]))
        def _norm_path(path, label):
            _require(isinstance(path, list),
                     "%s: inference %r %s must be a list of [edge, direction]"
                     % (where, ev["id"], label))
            out = []
            for step in path:
                _require(isinstance(step, (list, tuple)) and len(step) == 2,
                         "%s: inference %r has malformed path step %r"
                         % (where, ev["id"], step))
                _require(step[1] in K.DIRECTIONS,
                         "%s: inference %r step %r: direction must be one of %s"
                         % (where, ev["id"], step, ", ".join(K.DIRECTIONS)))
                out.append((step[0], step[1]))
            return out

        # The single-premise form is the multi-premise form with one entry.
        # Normalising here rather than at every read site means the checker,
        # the CLI and the MCP printer never learn there were two shapes.
        if ev.get("premises"):
            _require(isinstance(ev["premises"], list) and ev["premises"],
                     "%s: inference %r `premises` must be a non-empty list of "
                     "{claim, path}" % (where, ev["id"]))
            premises = []
            for n, pr in enumerate(ev["premises"]):
                _require(isinstance(pr, dict) and pr.get("claim"),
                         "%s: inference %r premise %d needs a `claim`"
                         % (where, ev["id"], n))
                premises.append({"claim": pr["claim"],
                                 "path": _norm_path(pr.get("path") or [],
                                                    "premise %d `path`" % n)})
        else:
            premises = [{"claim": ev["claim"],
                         "path": _norm_path(ev.get("path") or [], "`path`")}]
        i = dict(ev)
        i["premises"] = premises
        # `claim` and `path` stay populated from the FIRST premise so that
        # everything reading an inference the old way keeps working.  The first
        # premise is the one carrying the conclusion's claim kind.
        i["claim"] = premises[0]["claim"]
        i["path"] = premises[0]["path"]
        sev = ev.get("severity_override")
        if sev:
            # An unknown severity used to reach `check.run`'s sort key and raise
            # KeyError there, so `gp check` and the hook CRASHED instead of
            # reporting a malformed graph -- and a crashing checker is
            # indistinguishable from a checker nobody ran.
            _require(sev in C_SEVERITIES,
                     "%s: inference %r overrides severity to %r; known "
                     "severities are %s"
                     % (where, ev["id"], sev, ", ".join(C_SEVERITIES)))
            _require(ev.get("severity_why"),
                     "%s: inference %r overrides the derived severity to %r "
                     "without `severity_why`.  A severity downgrade is a "
                     "judgement and must be visible as one."
                     % (where, ev["id"], sev))
        self.inferences[ev["id"]] = i
        self.inference_order.append(ev["id"])

    def apply_all(self, batch):
        """Fold a whole batch, CERTIFICATES FIRST.

        `batch` is [(event, source, lineno)].

        THE FOLD USED TO BE ORDER-DEPENDENT, which quietly falsified the
        property that earns the append-only shape.  `_apply_claim` derives an
        emptiness scope against `self.certificates` AS OF THAT LINE, so a claim
        citing a graph-registered certificate had to appear after it:

            merge [cert_branch, claim_branch]  -> folds, scope=SCHEME
            merge [claim_branch, cert_branch]  -> ScopeError, unknown certificate

        `load`'s own docstring says "Order does not matter for the result, only
        for which line number a conflict is reported at", and DESIGN.md sec.1.1
        sells merging as *concatenating logs and folding again*.  Neither was
        true across a certificate boundary, and the failure is not a warning: an
        unfoldable graph makes `hook.evaluate` fail CLOSED, so the wrong
        concatenation order blocks every subsequent tool call in the session.

        Two passes is the whole fix.  Certificates are the only event kind whose
        prior presence changes how a later event FOLDS -- every other
        cross-reference is checked in `validate()` after the fold, which is why
        models and edges have never needed ordering.
        """
        batch = list(batch)
        for want_cert in (True, False):
            for ev, source, lineno in batch:
                is_cert = (isinstance(ev, dict)
                           and ev.get("ev") == EV_CERTIFICATE)
                if is_cert is want_cert:
                    self.apply(ev, source=source, lineno=lineno)
        return self

    # -- referential integrity ---------------------------------------------
    def validate(self):
        """Every reference resolves, and every inference path is CONNECTED.

        Path continuity is not in the prototype and it matters: a path whose
        edges do not join is not a lossy inference, it is a nonexistent one,
        and typing it would produce a confident verdict about a route nobody
        can walk.
        """
        for cid, c in sorted(self.claims.items()):
            _require(c["model"] in self.models,
                     "claim %r lives in undeclared model %r" % (cid, c["model"]))
        for eid, e in sorted(self.edges.items()):
            for end in ("src", "dst"):
                _require(e[end] in self.models,
                         "edge %r has undeclared %s model %r"
                         % (eid, end, e[end]))
        for aid, a in sorted(self.aliases.items()):
            for m in a["models"]:
                _require(m in self.models,
                         "same_as %r names undeclared model %r" % (aid, m))
            fields = {self.models[m].get("field") for m in a["models"]
                      if self.models[m].get("field")}
            _require(len(fields) <= 1,
                     "same_as %r declares %s to be one object, but they "
                     "disagree about their field: %s.  Two models over "
                     "different fields are not the same object."
                     % (aid, ", ".join(a["models"]), ", ".join(sorted(fields))))
        for pid, p in sorted(self.partitions.items()):
            _require(p["parent"] in self.models,
                     "partition %r names undeclared parent model %r"
                     % (pid, p["parent"]))
            for b in p["branches"]:
                _require(b in self.models,
                         "partition %r names undeclared branch model %r"
                         % (pid, b))
                _require(b != p["parent"],
                         "partition %r lists its own parent %r as a branch"
                         % (pid, b))
            _require(p["exhaustive"] in self.claims,
                     "partition %r cites %r as its exhaustiveness claim, but "
                     "no such CLAIM is declared.  It must be a claim in the "
                     "graph, not a note and not prose: the whole point is that "
                     "the premise making the split valid can be seen by a rule."
                     % (pid, p["exhaustive"]))
        for mid, builders in sorted(self.built_by.items()):
            _require(mid in self.models,
                     "built_by names undeclared model %r" % mid)
            for b in builders:
                _require(b in self.inferences,
                         "built_by(%s) names undeclared inference %r" % (mid, b))
        for iid in self.inference_order:
            i = self.inferences[iid]
            lands = []
            for n, pr in enumerate(i["premises"]):
                _require(pr["claim"] in self.claims,
                         "inference %r premise %d cites undeclared claim %r"
                         % (iid, n, pr["claim"]))
                at = self.claims[pr["claim"]]["model"]
                for eid, direction in pr["path"]:
                    _require(eid in self.edges,
                             "inference %r cites undeclared edge %r"
                             % (iid, eid))
                    e = self.edges[eid]
                    frm, to = ((e["src"], e["dst"]) if direction == K.ALONG
                               else (e["dst"], e["src"]))
                    _require(at == frm,
                             "inference %r premise %d: path is not connected.  "
                             "The claim has reached model %r, but edge %r read "
                             "%s starts at %r."
                             % (iid, n, at, eid, direction, frm))
                    at = to
                lands.append(at)
            # A PARTITION-LICENSED INFERENCE is the one case where premises
            # legitimately live apart: the branch claims sit in their own
            # branches by construction, and it is the partition -- not any
            # edge -- that carries them jointly to the parent.
            if i.get("via_partition"):
                pid = i["via_partition"]
                _require(pid in self.partitions,
                         "inference %r cites undeclared partition %r"
                         % (iid, pid))
                i["concludes_at"] = self.partitions[pid]["parent"]
                kinds = [self.claims[pr["claim"]]["kind"]
                         for pr in i["premises"]]
                i["concludes_kind"] = (
                    K.check_conclusion_kind(i.get("concludes_kind"), kinds, iid)
                    or self.claims[i["premises"][0]["claim"]]["kind"])
                continue
            # EVERY OTHER PREMISE MUST ARRIVE AT THE SAME PLACE.  Premises that land
            # in different models are not a joint argument -- they are two
            # separate statements with a conjunction written between them,
            # which is exactly the shape of the join `GI-BRIDGE` exists to
            # refuse.  Enforcing co-location is what makes the multi-premise
            # form safe to offer at all.
            _require(len(set(lands)) == 1,
                     "inference %r: its premises do not meet.  They arrive at "
                     "%s respectively, so there is no single model at which "
                     "they can be combined.  Transport them to a common model "
                     "first, or they are separate statements joined by prose."
                     % (iid, ", ".join("%s -> %s" % (p["claim"], m)
                                       for p, m in zip(i["premises"], lands))))
            i["concludes_at"] = lands[0]
            # A DECLARED conclusion kind is CHECKED against the premises, not
            # trusted.  Undeclared, it is derived from the first premise, which
            # is the single-premise behaviour and cannot lie.
            kinds = [self.claims[pr["claim"]]["kind"] for pr in i["premises"]]
            i["concludes_kind"] = (
                K.check_conclusion_kind(i.get("concludes_kind"), kinds, iid)
                or self.claims[i["premises"][0]["claim"]]["kind"])
        return self


def load_events(path):
    """Yield (event, lineno) from a .jsonl file.  Blank lines and `#` comment
    lines are skipped so a graph stays human-editable."""
    with open(path, "r", encoding="utf-8") as fh:
        for n, line in enumerate(fh, 1):
            s = line.strip()
            if not s or s.startswith("#"):
                continue
            try:
                yield json.loads(s), n
            except ValueError as exc:
                raise GraphError("%s:%d: not valid JSON: %s" % (path, n, exc))


def load(*paths):
    """Fold one or more logs into a single validated Graph.

    Passing several paths IS the merge operation.  Order does not matter for
    the result, only for which line number a conflict is reported at.
    """
    g = Graph()
    batch = [(ev, p, n) for p in paths for ev, n in load_events(p)]
    return g.apply_all(batch).validate()


def graph_path(root="."):
    return os.path.join(root, GRAPH_DIR, GRAPH_FILE)


def append(events, root="."):
    """Append events to the working graph, after checking they still fold.

    Writing is transactional in the only sense that matters here: the new
    events are folded against the existing graph FIRST, and nothing is written
    if the result is not a well-formed graph.  A log you cannot fold is worse
    than a rejected write.
    """
    path = graph_path(root)
    d = os.path.dirname(path)
    if d and not os.path.isdir(d):
        os.makedirs(d)
    g = Graph()
    batch = []
    if os.path.exists(path):
        batch.extend((ev, path, n) for ev, n in load_events(path))
    batch.extend((ev, "<new>", k + 1) for k, ev in enumerate(events))
    g.apply_all(batch).validate()
    with open(path, "a", encoding="utf-8") as fh:
        for ev in events:
            fh.write(json.dumps(ev, sort_keys=True) + "\n")
    return g
