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
EV_NOTE = "note"          # free-form, carried but never interpreted

EVENT_KINDS = (EV_CERTIFICATE, EV_MODEL, EV_EDGE, EV_CLAIM, EV_INFERENCE,
               EV_BUILT_BY, EV_NOTE)

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
        self.claims[ev["id"]] = c

    def _apply_inference(self, ev, where):
        _require(ev.get("claim"),
                 "%s: inference %r needs `claim`" % (where, ev["id"]))
        _require(ev.get("asserted"),
                 "%s: inference %r needs `asserted` -- the conclusion in words, "
                 "as it was actually used" % (where, ev["id"]))
        path = ev.get("path") or []
        _require(isinstance(path, list),
                 "%s: inference %r `path` must be a list of [edge, direction]"
                 % (where, ev["id"]))
        norm = []
        for step in path:
            _require(isinstance(step, (list, tuple)) and len(step) == 2,
                     "%s: inference %r has malformed path step %r"
                     % (where, ev["id"], step))
            _require(step[1] in K.DIRECTIONS,
                     "%s: inference %r step %r: direction must be one of %s"
                     % (where, ev["id"], step, ", ".join(K.DIRECTIONS)))
            norm.append((step[0], step[1]))
        i = dict(ev)
        i["path"] = norm
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
        for mid, builders in sorted(self.built_by.items()):
            _require(mid in self.models,
                     "built_by names undeclared model %r" % mid)
            for b in builders:
                _require(b in self.inferences,
                         "built_by(%s) names undeclared inference %r" % (mid, b))
        for iid in self.inference_order:
            i = self.inferences[iid]
            _require(i["claim"] in self.claims,
                     "inference %r cites undeclared claim %r" % (iid, i["claim"]))
            at = self.claims[i["claim"]]["model"]
            for eid, direction in i["path"]:
                _require(eid in self.edges,
                         "inference %r cites undeclared edge %r" % (iid, eid))
                e = self.edges[eid]
                frm, to = ((e["src"], e["dst"]) if direction == K.ALONG
                           else (e["dst"], e["src"]))
                _require(at == frm,
                         "inference %r: path is not connected.  The claim has "
                         "reached model %r, but edge %r read %s starts at %r."
                         % (iid, at, eid, direction, frm))
                at = to
            i["concludes_at"] = at
            i["concludes_kind"] = self.claims[i["claim"]]["kind"]
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
