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
from .discharge import DISCHARGE_KINDS as D_KINDS

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
EV_FAMILY = "family"      # a finite INDEX of objects, not a variety
EV_NOTE = "note"          # free-form, carried but never interpreted

EVENT_KINDS = (EV_CERTIFICATE, EV_MODEL, EV_EDGE, EV_CLAIM, EV_INFERENCE,
               EV_BUILT_BY, EV_PARTITION, EV_SAME_AS, EV_FAMILY,
               EV_NOTE)

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
        self.families = {}         # id -> {count, enumeration, members?}
        self.groups = {}           # group id -> {of, settles, exhibited, ...}
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

    def _apply_disposition(self, ev, where):
        """A COUNT claim: how a GROUP of a family's members was settled.

        NOT A NEW RECORD KIND, and that was the second design to survive
        contact with real data.  A disposition needs an evidence grade, a
        citation, supersession, everything a claim already has -- one campaign
        split its groups by METHOD SOUNDNESS (a proof at one point versus
        sampling), another split by EVIDENCE PROVENANCE (a paper nobody in the
        campaign had read versus its own exact check).  Both axes matter and
        only one of them was new, so a disposition IS a claim and inherits the
        other for free.

        `splits` names what is being subdivided: the family, or a GROUP from an
        earlier disposition.  That is the tree, and it is a tree rather than a
        partition because a real triage is nested -- 1567 into 347 and 1220,
        then the 347 into 343 and 4.  A flat "the groups total the family" rule
        was the first thing written here and it is simply wrong.
        """
        # A COUNT CLAIM DOES ONE OF TWO JOBS, and conflating them was the first
        # thing the retrodiction fixture broke.  It either SPLITS a group into
        # dispositions, or it asserts a cardinality over the INTERSECTION of
        # two groups.  Both are counts; only the first is a triage step, and
        # requiring `groups` of both made a cross-cut claim inexpressible.
        splitting = bool(ev.get("splits") or ev.get("groups"))
        crossing = bool(ev.get("rests_on") and ev.get("counts_against"))
        _require(splitting != crossing,
                 "%s: COUNT claim %r must be exactly one of two things.\n"
                 "  A DISPOSITION splits a family or a group -- declare "
                 "`splits`, `groups`, `method`, `proves` and `why`.\n"
                 "  A CROSS-COUNT asserts how many members of one group lie in "
                 "another -- declare `rests_on`, `counts_against` and "
                 "`asserts_count`.\n"
                 "  Both are counts and only the first is a triage step."
                 % (where, ev["id"]))
        if crossing:
            return
        groups = ev.get("groups") or []
        _require(groups,
                 "%s: claim %r is a COUNT and must declare `groups`: how the "
                 "members it covers were disposed of." % (where, ev["id"]))
        _require(ev.get("splits"),
                 "%s: COUNT claim %r must declare `splits` -- the family or "
                 "the group it subdivides. A triage is a TREE: a split of 347 "
                 "does not have to total the 1567 above it."
                 % (where, ev["id"]))
        _require(ev.get("method"),
                 "%s: COUNT claim %r must declare the `method` that settled "
                 "these members." % (where, ev["id"]))
        gids = [g.get("id") for g in groups]
        _require(isinstance(ev.get("proves"), list),
                 "%s: COUNT claim %r must declare `proves`: the list of its "
                 "own group ids whose verdict this method ESTABLISHES. The "
                 "others are evidence.\n"
                 "  Full Jacobian rank at one rational point proves generic "
                 "full rank -- the witnessing minor is a nonzero polynomial. "
                 "Rank DEFICIENCY at that point is only evidence. One "
                 "computation, two verdicts, one of them not established.\n"
                 "  Declare it EMPTY if the method only screens. An empty list "
                 "is an answer; a missing one is a question nobody was asked."
                 % (where, ev["id"]))
        unknown = [g for g in ev["proves"] if g not in gids]
        _require(not unknown,
                 "%s: COUNT claim %r says it proves %s, which %s not among its "
                 "own groups (%s)."
                 % (where, ev["id"], ", ".join(unknown),
                    "are" if len(unknown) > 1 else "is", ", ".join(gids)))
        _require(ev.get("why"),
                 "%s: COUNT claim %r must say WHY the method proves what it "
                 "proves and not the rest. That sentence is the whole content "
                 "of `proves`." % (where, ev["id"]))
        for g in groups:
            _require(g.get("id") and g.get("verdict"),
                     "%s: every group of %r needs `id` and `verdict`"
                     % (where, ev["id"]))
            _require(isinstance(g.get("settles"), int) and g["settles"] >= 0,
                     "%s: group %r of %r needs an integer `settles`"
                     % (where, g.get("id"), ev["id"]))
            ex = list(g.get("exhibited") or [])
            _require(not ex or len(ex) <= g["settles"],
                     "%s: group %r exhibits %d members but settles %d"
                     % (where, g["id"], len(ex), g["settles"]))
            rec = dict(g)
            rec["of"] = ev["family"]
            rec["by"] = ev["id"]
            rec["exhibited"] = ex
            rec["proved"] = g["id"] in ev["proves"]
            rec["method"] = ev["method"]
            rec["why"] = ev["why"]
            _require(g["id"] not in self.groups,
                     "%s: group id %r is declared twice; group ids name a set "
                     "of members and two sets must not share a name."
                     % (where, g["id"]))
            self.groups[g["id"]] = rec

    def _apply_family(self, ev, where):
        """A finite INDEX of objects.  Emphatically NOT a variety.

        FOUR CONSECUTIVE SESSIONS ASKED FOR THIS and it is the only item that
        appeared in every report.  "4 of 1567 isomorphism classes are
        generically 2-to-1" is the deliverable of a census, and a model in this
        kernel IS its solution set, so there was no object for "the 1567
        classes".  The result lived in prose and the graph held one example of
        it.

        THE OBVIOUS ENCODING WAS TRIED AND CORRECTLY REJECTED.  A campaign
        considered a disjoint-union parent with a `partition` over verdict
        classes and declined: "the parent would have been an object nobody
        studies, invented to satisfy the tool."  That is right.  The disjoint
        union of 1567 varieties has geometry, and none of it is the geometry
        anybody is reasoning about.

        So a family is an INDEX and says so.  It has no points, nothing
        transports across it, and no edge may touch it.  What it has is a
        COUNT, which is an assertion somebody made and can get wrong, so it
        must name a claim establishing it.  That is where "orbit sizes sum to
        34,752" finally lives instead of in a note.

        Members may be NAMED or merely counted, and which one decides what is
        computable downstream: two decompositions of the same family can only
        be intersected if both name their members.  At 34 rows you name them;
        at 1567 you do not, and the cross-cut claims that error was made in are
        then correctly unavailable.
        """
        _require(isinstance(ev.get("count"), int) and ev["count"] >= 0,
                 "%s: family %r must declare an integer `count`. A family is "
                 "an index, and how many things it indexes is the one thing it "
                 "must say." % (where, ev["id"]))
        _require(ev.get("desc"),
                 "%s: family %r needs `desc` -- what is a member?"
                 % (where, ev["id"]))
        members = list(ev.get("members") or [])
        if members:
            _require(len(members) == ev["count"],
                     "%s: family %r lists %d members and declares count %d. "
                     "If the list is partial say so by omitting it; a list "
                     "that silently disagrees with the count is worse than no "
                     "list, because everything downstream trusts the names."
                     % (where, ev["id"], len(members), ev["count"]))
            _require(len(set(members)) == len(members),
                     "%s: family %r lists a member twice."
                     % (where, ev["id"]))
        f = dict(ev)
        f["members"] = members
        self.families[ev["id"]] = f

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
        self._reject_rule_names(ev, where)
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
        # A RESTRICTION IS A SUBSET INCLUSION, and its strongest cell depends
        # on that.  IDENTITY travels AGAINST unconditionally -- where a
        # NECESSARY_CONDITION needs a denominator-free map -- for exactly one
        # reason: nothing is substituted, because the coordinates are the same
        # ones.  A RESTRICTION declared over a coordinate change would keep
        # that licence and lose the argument for it.
        _require(not (ev.get("type") == K.RESTRICTION
                      and mk not in (K.IDENTITY_MAP,)),
                 "%s: edge %r is a RESTRICTION with map_kind %r. A RESTRICTION "
                 "cuts a subset out of a model IN THE SAME COORDINATES -- it "
                 "is an inclusion, not a map. If coordinates change, the step "
                 "is a change of variables composed with a restriction; "
                 "declare the two edges separately so each is typed for what "
                 "it does."
                 % (where, ev["id"], mk))
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

    # ---------------------------------------------------------------------
    # RULE NAMES THAT ARE NOT FIELD NAMES, and a silent ignore that a live
    # campaign hit.
    #
    # A refusal reports the RULE that blocked it -- `ring_isomorphism` -- and
    # the field you must actually set is `ring_iso`.  A campaign read the
    # refusal, read `gp table`'s conditions column (which prints rule names in
    # a list that reads like fields), declared `ring_isomorphism: true` on two
    # edges, and it was accepted and ignored.  Nothing false was licensed there
    # by luck; a graph relying on an EQUIVALENCE to carry an IDENTITY would
    # have been refused with no hint why.
    #
    # WHAT MAKES THE MISTAKE REASONABLE IS THAT IT IS SOMETIMES RIGHT.  Two of
    # the seven rule names -- `coefficients_in_base`, `zariski_dense` -- ARE
    # the field.  So a user who correctly learned one infers the other, and the
    # inference is sound about the vocabulary and wrong about this word.
    #
    # Renaming the rules to match would be the deeper fix and would rewrite
    # every recorded refusal reason in every campaign log.  Refusing the near
    # miss by name costs nothing and cannot silently do nothing.
    # ---------------------------------------------------------------------
    _NOT_A_FIELD = {
        "ring_isomorphism": ("ring_iso", "an EQUIVALENCE that is an "
                             "isomorphism of coordinate rings, not merely a "
                             "bijection on points"),
        "map_polynomial": ("map_kind", "one of %s" % (", ".join(K.MAP_KINDS),)),
        "ambient_identity": ("identity_origin", "%s, on the CLAIM rather than "
                             "the edge" % K.AMBIENT),
        "integral_identity": ("integral", "on the CLAIM rather than the edge"),
        "scheme_scope": ("certificate", "scope is DERIVED from the certificate "
                         "kind and is never declared"),
    }

    def _reject_rule_names(self, ev, where):
        for bad, (real, hint) in sorted(self._NOT_A_FIELD.items()):
            if bad in ev:
                raise GraphError(
                    "%s: %s %r carries %r, which is the name of a transport "
                    "RULE, not a field. It would have been stored and ignored.\n"
                    "  You want `%s`: %s.\n"
                    "  Refusals report the rule that blocked them, and for two "
                    "rules -- coefficients_in_base, zariski_dense -- that name "
                    "IS the field, which is what makes this worth refusing "
                    "rather than silently accepting."
                    % (where, ev.get("ev", "record"), ev.get("id"), bad,
                       real, hint))

    def _apply_claim(self, ev, where):
        self._reject_rule_names(ev, where)
        # A CLAIM SITS AT A MODEL OR AT A FAMILY, never both.
        #
        # A family is to its members as a model is to its points, so the claim
        # kinds carry over unchanged as quantifiers -- PREDICATE is "every
        # member", EMPTY is "no member", NONEMPTY is "at least one, exhibited".
        # That correspondence is why no new vocabulary was needed for the
        # ordinary cases and why COUNT is the only addition.
        at_family = bool(ev.get("family"))
        _require(bool(ev.get("model")) != at_family,
                 "%s: claim %r must sit at exactly one of `model` or `family`. "
                 "A family is an INDEX, not a variety: its members are objects, "
                 "a model's members are points, and a claim quantifies over one "
                 "or the other." % (where, ev["id"]))
        kinds = K.CLAIM_KINDS + ((K.COUNT,) if at_family else ())
        _require(ev.get("kind") in kinds,
                 "%s: claim %r has kind %r; %s: %s"
                 % (where, ev["id"], ev.get("kind"),
                    "at a family the kinds are" if at_family
                    else "at a model the kinds are", ", ".join(kinds)))
        _require(ev.get("statement"),
                 "%s: claim %r needs `statement`" % (where, ev["id"]))
        if ev.get("kind") == K.COUNT:
            self._apply_disposition(ev, where)
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
        # Evidence grading licenses nothing, so both fields are optional -- an
        # ungraded claim is merely ungraded.  What is refused is a grade that
        # is WRONG, including a pair that contradicts itself.
        K.check_evidence(ev.get("established_by"), ev.get("ladder"),
                         claim_id=ev["id"])
        self.claims[ev["id"]] = c

    # -----------------------------------------------------------------------
    # SUPERSESSION IS RESOLVED AFTER THE FOLD, NOT DURING IT.
    #
    # The first version checked it inside `_apply_claim`, which made the fold
    # ORDER-DEPENDENT and quietly falsified the property that earns the
    # append-only shape:
    #
    #     merge [old_branch, new_branch]  -> folds
    #     merge [new_branch, old_branch]  -> "supersedes X, which is not a
    #                                         claim in this graph"
    #
    # `load`'s docstring says order does not matter, DESIGN.md sells merging as
    # concatenate-and-fold-again, and `apply_all`'s own comment says
    # certificates are THE ONLY event kind whose prior presence changes how a
    # later event folds.  Supersession made that sentence false the day it
    # landed, in the same file that explains why it must not be.
    #
    # And the failure is not cosmetic: an unfoldable graph makes
    # `hook.evaluate` fail CLOSED, so the wrong concatenation order blocks
    # every tool call in a session.
    #
    # So it belongs here, with every other cross-reference.  Resolution is a
    # pass over all three registries once the fold is complete, which also
    # gives EDGES the treatment claims and inferences already had -- they were
    # carrying `supersedes` with no existence check, no self-check and no
    # back-pointer at all.
    # -----------------------------------------------------------------------
    _SUPERSEDABLE = ("claim", "inference", "edge")

    def _resolve_supersessions(self):
        for entity in self._SUPERSEDABLE:
            registry = {"claim": self.claims, "inference": self.inferences,
                        "edge": self.edges}[entity]
            kinds = (D_KINDS if entity == "edge" else K.SUPERSESSION_KINDS)
            for new_id in sorted(registry):
                new = registry[new_id]
                old_id = new.get("supersedes")
                if not old_id:
                    continue
                _require(old_id != new_id,
                         "%s %r supersedes itself." % (entity, new_id))
                _require(old_id in registry,
                         "%s %r supersedes %r, which is not a %s in this "
                         "graph. Supersession names the record being replaced; "
                         "if the older one lives in a log you have not folded "
                         "in, fold it too."
                         % (entity, new_id, old_id, entity))
                kind = new.get("discharge_kind")
                _require(kind, "%s %r supersedes %r without saying HOW. "
                               "Declare `discharge_kind`: %s."
                         % (entity, new_id, old_id, ", ".join(kinds)))
                _require(kind in kinds,
                         "%s %r supersedes %r with discharge_kind %r; for a %s "
                         "the kinds are %s.\n"
                         "  The two vocabularies are different on purpose. An "
                         "EDGE supersession says what happened to the "
                         "OBLIGATION the old edge carried; a CLAIM or "
                         "INFERENCE supersession says what CHANGED about the "
                         "record."
                         % (entity, new_id, old_id, kind, entity,
                            ", ".join(kinds)))
                old = registry[old_id]
                if entity == "edge":
                    # NO COMPUTED CHECK HERE, and the reason is a distinction
                    # worth keeping straight.
                    #
                    # A CLAIM's discharge_kind describes what CHANGED about the
                    # record, so AMEND is checkable by diffing the two records
                    # and is checked.  An EDGE's describes what happened to the
                    # OBLIGATION the old edge carried -- DERIVE the missing
                    # mathematics now exists, RETYPE the relation was
                    # mis-stated, ACCEPT carry it deliberately with a reason.
                    # Those live one level up from the record.
                    #
                    # A first version of this refused RETYPE when nothing in
                    # EDGE_LICENSING_FIELDS moved, by analogy with AMEND. It
                    # was wrong twice: it conflated the two levels, and it made
                    # a legitimate edit inexpressible -- restating an UNTYPED
                    # edge's `debt_why` more precisely changes no licensing and
                    # is not a repair that did not happen. It broke five
                    # well-reasoned tests and the tests were right.
                    pass
                else:
                    K.check_supersession_kind(old, new, kind,
                                              claim_id=new_id, entity=entity)
                old["superseded_by"] = new_id

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
                _require(isinstance(pr, dict), "%s: inference %r premise %d "
                         "must be an object" % (where, ev["id"], n))
                # AN OPEN SLOT: a premise the argument NEEDS and does not have.
                #
                # T5 pointed the tool at a campaign it had never seen, whose
                # headline finding was that a claim the published artifact
                # REQUIRES is absent -- nowhere in 529 files is there an "every
                # candidate is killed" statement, because five are not killed.
                # The graph could record claims, edges and inferences, and had
                # no way to record a claim that should exist and does not.
                #
                # Both escapes were bad.  Writing the missing claim enters a
                # falsehood into the graph; writing nothing loses the finding.
                # So the slot is declared and left open: the inference names
                # what it needs, the fold accepts it, and the checker refuses
                # to license the inference and says exactly which premise is
                # missing.
                if pr.get("required_kind"):
                    _require(pr["required_kind"] in K.CLAIM_KINDS,
                             "%s: inference %r premise %d requires kind %r; "
                             "known kinds are %s"
                             % (where, ev["id"], n, pr["required_kind"],
                                ", ".join(K.CLAIM_KINDS)))
                    _require(pr.get("at"),
                             "%s: inference %r premise %d is an open slot and "
                             "must say `at` which model the missing claim "
                             "belongs" % (where, ev["id"], n))
                    _require(pr.get("missing_why"),
                             "%s: inference %r premise %d is an open slot and "
                             "needs `missing_why` -- why is this claim absent? "
                             "An unexplained hole is indistinguishable from an "
                             "oversight." % (where, ev["id"], n))
                    premises.append({"claim": None, "path": [],
                                     "required_kind": pr["required_kind"],
                                     "at": pr["at"],
                                     "missing_why": pr["missing_why"]})
                    continue
                _require(pr.get("claim"),
                         "%s: inference %r premise %d needs a `claim`, or "
                         "`required_kind`+`at`+`missing_why` if the claim it "
                         "needs does not exist" % (where, ev["id"], n))
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
        self._resolve_supersessions()
        for cid, c in sorted(self.claims.items()):
            if c.get("family"):
                _require(c["family"] in self.families,
                         "claim %r lives at undeclared family %r"
                         % (cid, c["family"]))
                continue
            _require(c["model"] in self.models,
                     "claim %r lives in undeclared model %r" % (cid, c["model"]))
        for fid, f in sorted(self.families.items()):
            for m in f["members"]:
                # Members are NAMES, and need not be declared models.  At 1567
                # classes nobody declares a model per member, and at 34 rows
                # the names are row labels from an atlas.  What they must be is
                # consistent: a group may only exhibit members the family has.
                pass
        for gid, g in sorted(self.groups.items()):
            fam = self.families.get(g["of"])
            if fam and fam["members"]:
                unknown = [m for m in g["exhibited"] if m not in fam["members"]]
                _require(not unknown,
                         "group %r exhibits %s, which %s does not list as a "
                         "member. A cross-cut is computed from these names, so "
                         "a name that is not in the family silently changes an "
                         "intersection." % (gid, ", ".join(unknown), g["of"]))
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
                if pr.get("required_kind"):
                    _require(pr["at"] in self.models,
                             "inference %r premise %d needs a %s claim at %r, "
                             "which is not a declared model"
                             % (iid, n, pr["required_kind"], pr["at"]))
                    continue
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
                         if pr.get("claim") else pr["required_kind"]
                         for pr in i["premises"]]
                i["concludes_kind"] = (
                    K.check_conclusion_kind(i.get("concludes_kind"), kinds, iid)
                    or kinds[0])
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
            kinds = [self.claims[pr["claim"]]["kind"]
                     if pr.get("claim") else pr["required_kind"]
                     for pr in i["premises"]]
            i["concludes_kind"] = (
                K.check_conclusion_kind(i.get("concludes_kind"), kinds, iid)
                or kinds[0])
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


def merge_report(paths):
    """Fold several logs and collect EVERY conflict instead of raising on the first.

    T4 -- the first merge of two logs written by agents working in isolation --
    failed its declared pass condition on this. The fold refused correctly and
    named both versions, which is the half that worked; but `TESTPLAN.md` also
    said **fail** if "resolving it means hand-editing an append-only log", and
    there was no guided path at all. You got one conflict, edited, re-ran, got
    the next.

    So this reports all of them at once, and distinguishes the two cases,
    because they have opposite resolutions:

      SAME OBJECT, described differently -- what T4 produced. Both branches are
      right; the descriptions need reconciling into one, and whoever merges
      picks the wording.

      DIFFERENT OBJECTS that collided on a name -- rename one, and if they are
      related, say how with an edge.

    The tool cannot tell these apart; that is mathematics. What it can do is
    put both versions side by side, name exactly which fields differ, and stop
    the reader diffing two JSON blobs by eye.

    Returns (graph_or_None, conflicts). `graph` is None when conflicts exist,
    because a partially-folded graph is not a thing anyone should reason from.
    """
    seen, conflicts, events = {}, [], []
    for p in paths:
        for ev, n in load_events(p):
            kind, eid = ev.get("ev"), ev.get("id")
            if kind in (EV_NOTE, EV_BUILT_BY) or not eid:
                events.append((ev, p, n))
                continue
            key, canon = (kind, eid), _canon(ev)
            if key in seen and seen[key][0] != canon:
                prior_ev, prior_p, prior_n = seen[key][1]
                differing = sorted(
                    k for k in set(prior_ev) | set(ev)
                    if prior_ev.get(k) != ev.get(k))
                conflicts.append({
                    "kind": kind, "id": eid, "fields": differing,
                    "a": {"path": prior_p, "line": prior_n, "event": prior_ev},
                    "b": {"path": p, "line": n, "event": ev}})
                continue
            if key not in seen:
                seen[key] = (canon, (ev, p, n))
                events.append((ev, p, n))
    if conflicts:
        return None, conflicts
    return Graph().apply_all(events).validate(), []


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
