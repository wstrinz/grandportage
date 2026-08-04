"""The checker: reads a folded graph, emits findings, decides.

Deterministic, no model in the loop, no solver, no network.  Given a graph it
returns the same findings every time, and `gp check` exits 0 iff there are
none above the configured severity floor.

The checker never grades evidence and the ladder never licenses a transport.
Those are orthogonal axes and conflating them is how a project ends up with an
`independently-audited` predicate imported across an edge that forbids it.
"""

import hashlib

from . import format as F
from . import groebner as G
from . import kernel as K
from . import store as S
from .cas import foreign_symbols as cas_foreign_symbols
from .cas import non_integral_denominators as cas_non_integral_denominators
from .discharge import discharge_for

# Severities.  Not every finding is an accusation.
UNSOUND_CONCLUSION = "UNSOUND_CONCLUSION"  # a statement was recorded that the
                                           # graph itself contradicts
UNSOUND_PREMISE = "UNSOUND_PREMISE"        # the conclusion may hold; the route
                                           # does not
TRIAGE = "TRIAGE"                          # nothing was claimed wrongly; the
                                           # type layer only routes the result
DEBT = "DEBT"                              # a hole recorded as a hole

SEVERITY_ORDER = [DEBT, TRIAGE, UNSOUND_PREMISE, UNSOUND_CONCLUSION]
SEVERITY_RANK = {s: i for i, s in enumerate(SEVERITY_ORDER)}

# Rule codes.
R_TRANSPORT = "TRANSPORT"
R_TAINT = "TAINT"
R_COVERAGE = "COVERAGE"
R_UNTYPED = "UNTYPED-EDGE"
R_REFINEMENT = "REFINEMENT-TYPE"
R_IDENTITY_ORIGIN = "UNKNOWN-IDENTITY-ORIGIN"
R_PARALLEL = "PARALLEL-EDGE"
R_PARTITION = "PARTITION"
R_SUPERSEDE = "SUPERSESSION"
R_WITNESS = "ASSERTED-WITNESS"
R_ALIAS = "ALIAS"
R_VACUOUS = "VACUOUS-CONCLUSION"
R_SELF_BUILT = "SELF-BUILT-MODEL"
R_STALE_PREMISE = "STALE-PREMISE"
R_STALE_PATH = "STALE-PATH"
R_FAMILY = "FAMILY"
R_DIRECTION = "EVIDENCE-DIRECTION"
R_CROSSCUT = "CROSS-CUT"
R_CONTAINMENT = "CONTAINMENT"
R_PENDING_IDEAL = "PENDING-IDEAL"
R_INEXPRESSIBLE = "INEXPRESSIBLE-CONCLUSION"
R_REFUTED_EVIDENCE = "REFUTED-EVIDENCE"
R_IDENTITY = "UNTESTED-IDENTITY"
R_SIBLING = "SIBLING-EDGE"
R_STALE_MODEL = "STALE-MODEL"
R_STALE_REF = "STALE-REFERENCE"
R_BASE_COEFFS = "FOREIGN-COEFFICIENT"
R_INTEGRAL = "NON-INTEGRAL-COEFFICIENT"
R_ORIGIN_CONFLICT = "ORIGIN-CONTRADICTED"
R_CITATION = "AMBIGUOUS-CITATION"
R_DOUBT = "DOUBT"
R_EVIDENCE = "EVIDENCE-GRADE"

EXISTENCE_OPPOSITE = {K.EMPTY: K.NONEMPTY, K.NONEMPTY: K.EMPTY}


class Finding(object):
    __slots__ = ("rule", "fid", "severity", "subject", "detail", "discharge",
                 "trace", "derived_severity", "severity_why", "semantic_key")

    def __init__(self, rule, fid, severity, subject, detail, discharge,
                 trace=(), derived_severity=None, severity_why=None,
                 semantic_key=""):
        self.rule = rule
        self.fid = fid
        self.severity = severity
        self.subject = subject
        self.detail = detail
        self.discharge = discharge
        self.trace = list(trace)
        self.derived_severity = derived_severity or severity
        self.severity_why = severity_why
        # What the finding is ABOUT, beyond what `detail` happens to render.
        # `detail` only names the FIRST refusal, so retyping or redirecting a
        # LICENSED leg of the path moved neither it nor the trace, and an
        # acceptance survived the inference concluding about a different model
        # across a different relaxation type.
        self.semantic_key = semantic_key

    @property
    def overridden(self):
        return self.severity != self.derived_severity

    @property
    def fingerprint(self):
        """A short hash of what this finding MEANS, not of where it sits.

        The baseline was keyed by `fid` alone, and `fid` is "RULE:subject" --
        stable by construction.  So an acceptance recorded against
        `TRANSPORT:GI-BRIDGE` went on suppressing that finding after the edge it
        rides was retyped, redirected, or pointed at a different claim.  The
        obligation a reviewer agreed to carry and the obligation still being
        carried had drifted apart, silently, in the one file humans read as the
        authoritative record of what a campaign knows it is holding.

        That is the same defect as the `--only` baseline wipe (see
        `hook.save_baseline`): quiet damage to the record of what is knowingly
        carried.  The repair is the same in kind -- make the change visible.

        The digest covers the rule, the subject, the rendered detail (which
        carries the claim statement, the assertion, and the refusal reason, so
        it moves when the transport cell moves), the derived severity, and the
        path with its per-step licensing.  It does NOT cover the accepted
        severity, which a human may legitimately override without the
        mathematics changing.
        """
        payload = "\x1f".join([
            self.rule, self.subject, self.detail, self.derived_severity,
            self.semantic_key,
            "|".join("%s/%s/%s" % (e, d, lic) for e, d, lic, _ in self.trace)])
        return hashlib.sha256(payload.encode("utf-8")).hexdigest()[:16]

    def as_dict(self):
        d = {"rule": self.rule, "id": self.fid, "severity": self.severity,
             "subject": self.subject, "detail": self.detail,
             "discharge": self.discharge}
        if self.trace:
            d["trace"] = [{"edge": e, "direction": dr, "licensed": lic,
                           "reason": rsn} for e, dr, lic, rsn in self.trace]
        if self.overridden:
            d["derived_severity"] = self.derived_severity
            d["severity_why"] = self.severity_why
        return d

    def __repr__(self):
        return "<%s %s %s>" % (self.rule, self.fid, self.severity)


def audit_inference(graph, iid):
    """Walk an inference's path through the kernel.

    Returns (licensed, trace) where trace is [(edge, direction, ok, reason)].
    Every step is recorded, licensed or not, so a report can show the whole
    route rather than only the step that failed.
    """
    inf = graph.inferences[iid]
    trace, ok = [], True
    # A CASE SPLIT IS NOT TRANSPORT.  No single edge licenses it -- each leg
    # taken alone is correctly refused, since one branch dying says nothing
    # about the parent.  It is the declared partition that carries the claim.
    if inf.get("via_partition"):
        p = graph.partitions[inf["via_partition"]]
        kind = inf["concludes_kind"]
        # AN OPEN SLOT HAS NO `claim`, and this comprehension used it as a dict
        # key -- so a case split that admits it has not settled a branch, which
        # is the single most honest thing a partition can say, raised
        # KeyError: None.  `store` handles the same field correctly two files
        # away; only the checker did not.
        #
        # A slot contributes NOTHING to coverage, deliberately: it is a
        # declaration that the branch is unsettled, so the branch stays
        # uncovered and the partition is correctly refused.
        carried = {
            graph.claims[pr["claim"]]["model"] for pr in inf["premises"]
            if pr.get("claim")
            and graph.claims[pr["claim"]]["kind"] == kind
            and (kind != K.EMPTY
                 or effective_certificate(graph.claims[pr["claim"]])
                    is not None)
        }
        covered = all(b in carried for b in p["branches"])
        cites_exhaustive = any(pr.get("claim") == p["exhaustive"]
                               for pr in inf["premises"])
        cover_verified = p.get("exhaustive_verdict") == "VERIFIED"
        r = K.transport_over_partition(
            kind, covered, cites_exhaustive and cover_verified)
        missing = [b for b in p["branches"] if b not in carried]
        detail = r.reason
        if missing:
            detail += " (no %s premise from: %s)" % (kind, ", ".join(missing))
        slots = [pr for pr in inf["premises"] if pr.get("required_kind")]
        for pr in slots:
            detail += ("\n  and the argument itself declares %s at %s is not "
                       "settled: %s"
                       % (pr["required_kind"], pr.get("at"),
                          pr.get("missing_why")))
        if not cites_exhaustive:
            detail += (" (the exhaustiveness claim %s is not among the "
                       "premises)" % p["exhaustive"])
        if not cover_verified:
            detail += (
                " (partition exhaustiveness has no current VERIFIED verdict; "
                "a declaration alone does not license a case split in "
                "kernel epoch %d)" % F.KERNEL_EPOCH)
        return r.licensed, [(UNCOVERED_PARTITION, "COVERS", r.licensed, detail)]
    # EVERY premise, not just the first.  An argument is only as licensed as
    # its weakest leg, and before the multi-premise form existed the extra legs
    # were not in the graph to be audited at all.
    for pr in inf["premises"]:
        # AN OPEN SLOT licenses nothing and says exactly what is missing.
        # This is how "the artifact needs a claim that does not exist" becomes
        # recordable without entering the missing claim as though it held.
        if pr.get("required_kind"):
            ok = False
            trace.append((
                "(missing)", "PREMISE", False,
                "this argument needs a %s claim at %s and the graph has none: "
                "%s" % (pr["required_kind"], pr["at"], pr["missing_why"])))
            continue
        claim = graph.claims[pr["claim"]]
        if (claim.get("certificate") == "LOCALIZED_UNIT_IDEAL_CERT"
                and effective_certificate(claim) is None
                and pr["path"]):
            ok = False
            trace.append((
                "(localized-unit certificate)", "PREMISE", False,
                "LOCALIZED_UNIT_IDEAL_CERT has no current VERIFIED verdict. "
                "The declaration remains unfinished mathematics and grants "
                "no downstream transport until its exact proof replays."))
            continue
        current_condition = claim.get("condition")
        for step_index, (eid, direction) in enumerate(pr["path"]):
            e = graph.edges[eid]
            target_expressible = (
                current_condition is not None and direction == K.ALONG
                and e["type"] == K.IMAGE_CLOSURE
                and e.get("built_by_operation") == "Eliminate"
                and condition_expressible_at(
                    graph, current_condition, e["dst"]))
            if claim.get("condition") is not None:
                zariski_closed = (
                    target_expressible
                    and structured_condition_closed(current_condition))
            else:
                zariski_closed = claim.get("zariski_closed")
            r = K.transport(
                e["type"], direction, claim["kind"],
                scope=claim.get("scope"),
                certificate=effective_certificate(claim),
                map_kind=e["map_kind"],
                zariski_closed=zariski_closed,
                identity_origin=effective_origin(claim),
                integral=claim.get("integral"),
                ring_iso=effective_ring_iso(e),
                coefficients_in_base=claim.get("coefficients_in_base"),
                zariski_dense=e.get("zariski_dense"),
                existential=claim.get("existential"),
                exact_contraction=effective_exact_contraction(e),
                geometric_closure=effective_geometric_closure(e),
                point_surjective=effective_point_surjective(e),
                target_expressible=target_expressible)
            trace_reason = r.reason
            next_condition = None
            rewrite_why = None
            if current_condition is not None and r.licensed:
                if e["type"] == K.EQUIVALENCE:
                    next_condition, rewrite_why = (
                        rewrite_condition_across_equivalence(
                            graph, current_condition, e, direction))
                elif direction == K.AGAINST:
                    next_condition, rewrite_why = pullback_condition_across_edge(
                        graph, current_condition, e, direction)
                elif target_expressible:
                    next_condition = current_condition
                    rewrite_why = (
                        "structured condition is expressed in the retained "
                        "elimination target")
                elif step_index + 1 < len(pr["path"]):
                    rewrite_why = (
                        "structured condition typing stops here: this pilot "
                        "has no rewrite contract for %s" % e["type"])
            if rewrite_why:
                trace_reason += "; " + rewrite_why
            current_condition = next_condition
            trace.append((eid, direction, r.licensed, trace_reason))
            if not r.licensed:
                ok = False
    return ok, trace


def probe(graph, claim_id, edge_id, direction, etype=None, map_kind=None,
          zariski_closed=None):
    """What WOULD happen if this claim crossed this edge in this direction.

    A probe is not an inference: nothing asserts that anyone took this step.
    It exists because the sharpest credibility checks are counterfactual, and
    the prototypes both needed it without naming it.  Two examples, and they
    are the load-bearing controls in their respective domains:

      CONTRAST PAIR.  Push two emptiness claims -- both computed over the same
      small field -- across the SAME edge in the SAME direction.  One is
      licensed and one is not, and the only thing that differs is the
      certificate.  As recorded inferences these two claims travel over
      different edges, so the discrimination is invisible; only the probe
      isolates the certificate as the sole cause.

      NON-VACUITY.  Retype an EQUIVALENCE as NECESSARY_CONDITION and check that
      it would now forbid a transport the equivalence licenses.  If it would
      not, the positive control on that edge proves nothing, because the edge's
      type was never load-bearing for it.

    `etype`, `map_kind` and `zariski_closed` override the declared values, so a
    probe can ask the retyping question without mutating the graph.
    """
    claim = graph.claims[claim_id]
    edge = graph.edges[edge_id]
    target_expressible = (
        direction == K.ALONG
        and edge["type"] == K.IMAGE_CLOSURE
        and edge.get("built_by_operation") == "Eliminate"
        and claim.get("model") == edge["src"]
        and condition_expressible_at(graph, claim, edge["dst"]))
    if zariski_closed is None:
        if claim.get("condition") is not None:
            effective_closed = (
                target_expressible and structured_condition_closed(claim))
        else:
            effective_closed = claim.get("zariski_closed")
    else:
        effective_closed = zariski_closed
    return K.transport(
        etype or edge["type"], direction, claim["kind"],
        scope=claim.get("scope"),
        certificate=effective_certificate(claim),
        map_kind=map_kind or edge["map_kind"],
        zariski_closed=effective_closed,
        identity_origin=effective_origin(claim),
        integral=claim.get("integral"), ring_iso=effective_ring_iso(edge),
        coefficients_in_base=claim.get("coefficients_in_base"),
        zariski_dense=edge.get("zariski_dense"),
        existential=claim.get("existential"),
        exact_contraction=effective_exact_contraction(edge),
        geometric_closure=effective_geometric_closure(edge),
        point_surjective=effective_point_surjective(edge),
        target_expressible=target_expressible)


def contradicting_claims(graph, model_id, kind, exclude=()):
    """Claims at `model_id` asserting the opposite existence statement.

    This is what upgrades a refused transport from "the route does not hold" to
    "the conclusion is FALSE" -- and it is derived from the graph rather than
    graded by hand.  Note it turns on MODEL identity: placing a NONEMPTY claim
    on the model an inference concludes about is itself the modelling act that
    makes the contradiction visible.  No scope lattice is involved and none is
    wanted; the field lives in the model.
    """
    opposite = EXISTENCE_OPPOSITE.get(kind)
    if opposite is None:
        return []
    return sorted(cid for cid, c in graph.claims.items()
                  if c.get("model") == model_id and c["kind"] == opposite
                  and cid not in exclude)


MISSING_PREMISE = "(missing)"     # the sentinel audit_inference emits for an
                                  # open slot; it is not an edge id
UNCOVERED_PARTITION = "(partition)"   # ditto, for a case split that does not
                                      # cover its parent


# The two trace positions that are NOT edge ids.  Kept as a lookup rather than
# an `if` chain so that adding a third sentinel cannot silently fall through to
# a transport discharge -- naming a requirement about an edge nobody crossed is
# how a refusal sends someone to fix the wrong thing.
_SENTINEL_MOVES = {MISSING_PREMISE: MISSING_PREMISE,
                   UNCOVERED_PARTITION: UNCOVERED_PARTITION}


def _refused_on(trace):
    """The id in the edge position of the first refused step, or None."""
    for eid, _direction, ok, _reason in trace:
        if not ok:
            return eid
    return None


def _first_refusal(graph, trace):
    """The first refused step, and the edge it happened on IF there is one.

    THERE IS NOT ALWAYS ONE.  An OPEN PREMISE SLOT refuses with the sentinel
    `(missing)` in the edge position, because nothing was traversed -- the
    argument names a claim the graph does not contain.  This used `graph.edges[
    eid]` and raised KeyError on that sentinel, so `gp check` CRASHED on any
    graph declaring the construct.

    That is worse than it sounds twice over.  Open slots were built for a live
    campaign's central finding -- that a published artifact requires a claim
    which does not exist anywhere -- so the construct with the strongest claim
    to being the point of the tool was the one that could not be checked.  And
    a crashing checker is indistinguishable from a checker nobody ran, which is
    the failure mode `store` already has a comment about.

    IT SURVIVED A TEST WRITTEN SPECIFICALLY FOR IT.  The open-slot regression
    calls `audit_inference` directly and never `run`, so it exercised the
    function and not the path a user takes.  The construct was correct
    everywhere except in being reachable.
    """
    for eid, direction, ok, reason in trace:
        if not ok:
            return graph.edges.get(eid), direction, reason
    return None, None, None


def check_transport(graph):
    findings = []
    for iid in graph.inference_order:
        inf = graph.inferences[iid]
        # A WITHDRAWN INFERENCE IS NOT DEBT.  Before supersession existed, a
        # campaign that had to remint an id left the old inference in the graph
        # forever, and its findings kept reporting as live -- so the baseline
        # grew an entry meaning "superseded, not carried on its merits", which
        # is a lie about what a baseline entry is for.  Nothing is hidden by
        # skipping it: the superseding inference is audited in its own right,
        # so a defect that survived the rewrite is still found, and one that
        # did not was genuinely repaired.
        if inf.get("superseded_by"):
            continue
        ok, trace = audit_inference(graph, iid)
        if ok:
            continue
        edge, direction, reason = _first_refusal(graph, trace)
        # AN ARGUMENT WHOSE FIRST PREMISE IS AN OPEN SLOT CARRIES NO CLAIM.
        # `claim` is the legacy singular field and the fold fills it from the
        # first premise, so it is None exactly when that premise is a slot --
        # and two lines below used it as a dict key.
        carried = graph.claims.get(inf.get("claim")) if inf.get("claim") else None
        counter = contradicting_claims(graph, inf["concludes_at"],
                                       inf["concludes_kind"],
                                       exclude=(inf.get("claim"),))
        # An UNTYPED EDGE is a hole, and a hole you have recorded is DEBT.
        # DRAWING A CONCLUSION ACROSS ONE is not: it asserts something no
        # declared relation supports, which is the definition of an unsound
        # premise.  Grading it DEBT would put it below the blocking floor, so
        # the untyped steps -- the very thing the type is for -- would be the
        # ones that never stop anybody.  The UNTYPED-EDGE rule still reports
        # the hole itself at DEBT; this is about the traffic over it.
        if counter:
            derived = UNSOUND_CONCLUSION
        else:
            derived = UNSOUND_PREMISE
        severity = inf.get("severity_override") or derived
        detail = "%s\n  asserted: %s\n  refused : %s" % (
            carried["statement"] if carried else
            "(this argument names no claim it actually has -- its leading "
            "premise is an open slot)",
            inf["asserted"], reason)
        if counter:
            detail += ("\n  contradicted by: %s\n    (%s)"
                       % (", ".join(counter),
                          graph.claims[counter[0]]["statement"]))
        # EVERY step's type and endpoints, plus where the inference lands and
        # which claim it carries -- not just the leg that failed.
        key = "|".join(
            ["claim=%s" % inf["claim"], "at=%s" % inf["concludes_at"],
             "kind=%s" % inf["concludes_kind"]]
            + ["%s:%s:%s->%s:%s" % (eid, d, graph.edges[eid]["src"],
                                    graph.edges[eid]["dst"],
                                    graph.edges[eid]["type"])
               for eid, d in inf["path"]])
        findings.append(Finding(
            R_TRANSPORT, "%s:%s" % (R_TRANSPORT, iid), severity, iid, detail,
            # NO EDGE MEANS NO TRANSPORT CELL, so there is no cell-specific
            # remedy to offer.  Nothing was traversed: the argument names a
            # claim the graph does not have, and the only moves are to supply
            # it or to stop asserting the conclusion.  Handing back a transport
            # discharge here would name a requirement about an edge that was
            # never crossed.
            discharge_for(_SENTINEL_MOVES.get(_refused_on(trace))
                          or (MISSING_PREMISE if edge is None
                              else edge["type"]),
                          direction, inf["concludes_kind"],
                          graph=graph, edge=edge,
                          fid="%s:%s" % (R_TRANSPORT, iid),
                          traffic=True,
                          hints=collect_hints(
                              graph, claim=inf.get("claim"),
                              model=inf.get("concludes_at"))),
            trace=trace, derived_severity=derived,
            severity_why=inf.get("severity_why"), semantic_key=key))
    return findings


def propagate_taint(graph, refused):
    """Models reachable from a refused inference, to a FIXED POINT.

    Returns {model id: (direct builders, inherited builders)}.

    The first version was one pass over `built_by`, so it caught only models
    built DIRECTLY by a refused inference.  Taint is transitive and one pass
    does not close it: if a refused inference builds M1, and a perfectly
    licensed inference reasons FROM a claim in M1 to build M2, then M2 rests on
    the same defect and the single pass reported M1 only.  The second
    generation is exactly where a reader stops looking, because the step that
    produced it is clean.

    So iterate.  A model is tainted when one of its builders is refused, or
    when one of its builders draws on a claim that lives in a model already
    tainted.  Termination is immediate -- the tainted set only grows and is
    bounded by the models -- but the loop is written as one because the
    dependency order of `built_by` is not guaranteed to be topological.
    """
    tainted = {}
    changed = True
    while changed:
        changed = False
        for mid in sorted(graph.built_by):
            if mid in tainted:
                continue
            direct, inherited = [], []
            for b in graph.built_by[mid]:
                if b in refused:
                    direct.append(b)
                    continue
                inf = graph.inferences.get(b)
                if inf is None:
                    continue
                premise = graph.claims[inf["claim"]]["model"]
                if premise in tainted:
                    inherited.append("%s (from %s)" % (b, premise))
            if direct or inherited:
                tainted[mid] = (direct, inherited)
                changed = True
    return tainted


def check_taint(graph, transport_findings):
    """A licensed conclusion drawn in an illegitimately-constructed model is
    still unsound.  Provenance has to be tracked separately from transport."""
    refused = {f.subject for f in transport_findings if f.rule == R_TRANSPORT}
    findings = []
    tainted = propagate_taint(graph, refused)
    for mid in sorted(tainted):
        direct, inherited = tainted[mid]
        downstream = sorted(cid for cid, c in graph.claims.items()
                            if c.get("model") == mid)
        if direct:
            how = ("was BUILT BY a refused inference (%s)"
                   % ", ".join(direct))
        else:
            how = ("was built by an inference that is itself LICENSED, but "
                   "which reasons from a claim in a model that is already "
                   "tainted (%s).  The step is clean and the ground it stands "
                   "on is not" % ", ".join(inherited))
        findings.append(Finding(
            R_TAINT, "%s:%s" % (R_TAINT, mid), UNSOUND_PREMISE, mid,
            "model %s %s.  Every claim drawn in it inherits the defect even "
            "where its own transport is licensed.\n  affected claims: %s"
            % (mid, how, ", ".join(downstream) or "(none)"),
            discharge_for(R_TAINT, None, None, graph=graph)))
    return findings


def coverage_gaps(graph, model):
    """`touched(axis) \\ declared(model, axis)`, per axis the model claims to cover.

    Ten lines, readable by a human, over an inventory whose every row is
    independently checkable.  Structurally this is a CEGAR signature-closure
    rule: the abstraction's vocabulary must contain every index appearing in
    the concrete object's own impositions and read sites.  It fires on ABSENT
    structure only -- a declared-but-too-weak component is invisible to it, and
    that limitation is a property of the whole coverage tradition, not a bug
    here.
    """
    gaps = {}
    for axis in model.get("coverage_axes", []):
        touched = set()
        for row in model["touches"] + model["reads"]:
            if row.get("axis") == axis:
                touched.update(row.get("at") or [])
        missing = _natural(touched - set(model["declares"].get(axis, [])))
        if missing:
            gaps[axis] = missing
    return gaps


def _natural(values):
    """Sort index labels so embedded integers order numerically.

    Purely cosmetic, and worth the four lines: an order-axis gap reported as
    M=-4, M=0, M=1, M=10, M=11, M=12, M=2 ... reads as noise, while the same
    gap reported in order reads as "one interior rung, then a half-line", which
    is the actual shape of the finding.
    """
    import re

    def key(v):
        return [int(p) if p.lstrip("-").isdigit() else p
                for p in re.split(r"(-?\d+)", str(v)) if p != ""]
    return sorted(values, key=key)


def check_coverage(graph):
    findings = []
    for mid in sorted(graph.models):
        m = graph.models[mid]
        for axis, missing in sorted(coverage_gaps(graph, m).items()):
            imposing = sorted({r["name"] for r in m["touches"]
                               if r.get("axis") == axis
                               and set(r.get("at") or []) & set(missing)})
            reading = sorted({r["name"] for r in m["reads"]
                              if r.get("axis") == axis
                              and set(r.get("at") or []) & set(missing)})
            detail = (
                "model %s asserts coverage on axis %r but declares nothing at "
                "%s.\n  declared: %s\n  touches there: %s\n  reads there   : %s\n"
                "  Where nothing is declared the relaxation is UNBOUNDED: the "
                "model constrains literally nothing at those indices."
                % (mid, axis, ", ".join(missing),
                   ", ".join(m["declares"].get(axis, [])) or "(nothing)",
                   "; ".join(imposing) or "(none)",
                   "; ".join(reading) or "(none)"))
            findings.append(Finding(
                R_COVERAGE, "%s:%s:%s" % (R_COVERAGE, mid, axis),
                UNSOUND_PREMISE, mid, detail,
                discharge_for(R_COVERAGE, None, None, graph=graph,
                              axis=axis, missing=missing)))
    return findings


def withdrawn_edges(graph):
    """Edge ids a LIVE edge declares it has replaced.

    Edges DO carry `superseded_by` now -- `store._resolve_supersessions` stamps
    all three entity kinds -- AND THE STAMP IS STILL NOT ENOUGH HERE.  It marks
    every record some other record claims to replace, which in a CYCLE is both
    of them: E-A names E-B, E-B names E-A, both get stamped, and reading the
    stamp alone would call both dead in a graph where nothing is current.  So
    deadness is computed from the successors rather than read off the record,
    and the stamp is used only as a cross-check.

    THE WORD `LIVE` IS DOING WORK, and it is the whole reason this is a walk
    rather than a set comprehension.  Nothing in the fold refuses a supersession
    CYCLE for edges: two edges may each name the other, and under
    `{e["supersedes"] for e in edges}` both would come out dead and both of
    their findings would vanish, from a graph in which nothing was replaced by
    anything and no current edge exists at all.  That is precisely the move
    this rule must not permit -- supersession is a way to record that a defect
    was repaired, never a way to make a finding go away.

    So the walk starts from the HEADS -- the edges nothing claims to replace,
    which are live by construction -- and marks what they reach backwards along
    `supersedes`.  An edge in a closed cycle is reachable from no head, so it
    stays live and keeps its findings.  A dangling `supersedes` withdraws
    nothing either; `check_supersession` reports that one on its own.
    """
    replaced = {}
    for eid in sorted(graph.edges):
        old = graph.edges[eid].get("supersedes")
        if old and old in graph.edges:
            replaced[eid] = old
    tombstone_targets = {
        tomb["supersedes"]
        for (entity, _tid), tomb in graph.retractions.items()
        if entity == "edge" and tomb.get("discharge_kind") == "WITHDRAW"
        and tomb.get("supersedes") in graph.edges}
    dead = set(tombstone_targets)
    frontier = ([eid for eid in sorted(graph.edges)
                 if eid not in set(replaced.values())]
                + sorted(tombstone_targets))
    while frontier:
        old = replaced.get(frontier.pop())
        if old and old not in dead:
            dead.add(old)
            frontier.append(old)
    return dead


def live_crossings(graph, eids):
    """Inferences that still ride any of `eids` and have not been withdrawn.

    A superseded inference is not traffic.  Counting it as such would let a
    campaign that reminted an argument keep the old route looking load-bearing
    forever, which is the same dilution in a different place.
    """
    eids = set(eids)
    return sorted(iid for iid in graph.inference_order
                  if not graph.inferences[iid].get("superseded_by")
                  and any(s[0] in eids for s in graph.inferences[iid]["path"]))


def check_untyped(graph):
    dead = withdrawn_edges(graph)
    findings = []
    for eid in sorted(graph.edges):
        e = graph.edges[eid]
        if e["type"] != K.UNTYPED:
            continue
        # A RETYPED EDGE IS NOT DEBT, for the reason `check_transport` already
        # gives about withdrawn inferences.  The live case, and it cost a
        # campaign a permanent entry: `E-IV-PD` was UNTYPED and carried this
        # debt, `E-IV-PD-RESTRICT` superseded it with a RESTRICTION, the debt
        # was genuinely discharged BY the retyping -- and this rule went on
        # reporting it every run, forever, so the baseline grew a line whose
        # stated reason was "this cannot be discharged, only carried".  That
        # sentence is false about this debt, and one false line makes every
        # true line in a file whose entire value is deliberateness weaker.
        #
        # Nothing goes quiet.  The replacement is audited in its own right, so
        # a successor that is ALSO untyped gets its own finding below -- and
        # traffic still riding the withdrawn edge is refused by
        # `check_transport` against the type that edge actually declares, at
        # UNSOUND_PREMISE, which is louder than this line rather than quieter.
        if eid in dead:
            continue
        downstream = live_crossings(graph, [eid])
        findings.append(Finding(
            R_UNTYPED, "%s:%s" % (R_UNTYPED, eid), DEBT, eid,
            "edge %s (%s -> %s) has no declared relaxation type.\n  debt: %s\n"
            "  inferences crossing it: %s"
            % (eid, e["src"], e["dst"], e.get("debt_why"),
               ", ".join(downstream) or "(none yet)"),
            discharge_for(K.UNTYPED, None, None, graph=graph, edge=e)))
    return findings


def _withdrawn_and_unridden(graph, eid, dead=None):
    """Is this edge dead AND carrying no live traffic?

    THE GUARD ON EVERY RULE THAT REPORTS AN EDGE'S OWN ATTRIBUTES.  Four rules
    besides UNTYPED-EDGE report a defect in what an edge DECLARES -- a
    refinement typed wrong, an EQUIVALENCE resting on nothing, a self-refuting
    one, a partition branch pointing the wrong way -- and none of them asked
    whether the edge was still current.  So a defect repaired by superseding
    the edge reported forever, exactly as UNTYPED-EDGE did.

    Confirmed on a live graph: both of its above-floor findings sat on
    withdrawn edges, and the campaign had EARNED them by doing the right thing
    -- adding a `converse_witness` requires superseding, so discharging
    UNJUSTIFIED-EQUIVALENCE minted a permanent UNJUSTIFIED-EQUIVALENCE plus a
    permanent PARALLEL-EDGE.

    THE TRAFFIC HALF IS NOT OPTIONAL, and matters more here than it did for
    UNTYPED-EDGE.  A dead UNTYPED edge licenses nothing, so traffic over it is
    refused loudly elsewhere.  These edges carry PERMISSIVE types: a withdrawn
    EQUIVALENCE that a live inference still rides goes on licensing silently,
    and this finding is the only thing that would say so.  Three of the four
    report above the blocking floor, so going quiet on one that is still
    load-bearing would be a strictly worse trade than the noise it removes.
    """
    if dead is None:
        dead = withdrawn_edges(graph)
    return eid in dead and not live_crossings(graph, [eid])


def check_refinement(graph):
    """Monotonicity is not a fourth type.

    Adding equations gives V(new) subset V(old), which is a NECESSARY_CONDITION
    edge new -> old read AGAINST.  "A closed branch can never reopen under
    refinement" is therefore a theorem about ONE existing type, and a
    refinement edge typed as anything else is a modelling error.
    """
    findings = []
    dead = withdrawn_edges(graph)
    for eid in sorted(graph.edges):
        e = graph.edges[eid]
        if _withdrawn_and_unridden(graph, eid, dead):
            continue
        if not e["refinement"] or e["type"] == K.NECESSARY_CONDITION:
            continue
        findings.append(Finding(
            R_REFINEMENT, "%s:%s" % (R_REFINEMENT, eid), UNSOUND_PREMISE, eid,
            "edge %s is declared a refinement (src = dst + equations) but is "
            "typed %s.  A refinement is a NECESSARY_CONDITION edge read "
            "AGAINST the arrow; no other type states that adding equations "
            "cannot reopen a closed branch."
            % (eid, e["type"]),
            discharge_for(R_REFINEMENT, None, None, graph=graph, edge=e)))
    return findings


def check_unjustified_equivalence(graph):
    """An EQUIVALENCE asserted on nothing is the most dangerous row in a graph.

    Every other type forbids something; EQUIVALENCE forbids nothing, so one
    mistyped equivalence silently licenses every transport across that step.
    It is also the easiest type to reach for -- "this step should be
    reversible" is a feeling, not a converse.

    Reported at DEBT, not higher, when the edge offers none of a converse
    witness, a citation, or a complete structured forward/inverse map pair.

    Prompted by the first live run, which observed that `witness` is optional,
    was nearly skipped, and turned out to be where the best content went.  The
    stronger form of that suggestion -- require a witness on every
    NECESSARY_CONDITION -- was declined: most are obviously lossy, and a
    required field people cannot fill gets filled with noise, which is worse
    than an empty one.

    THE POLARITY BUG.  This rule used to accept `witness` as documentation, and
    `witness` is defined in the MCP schema as "explicit evidence that the step
    is NOT an equivalence -- e.g. a point of the target that is not in the
    source".  So a field whose entire purpose is to REFUTE an equivalence was
    accepted as grounds for asserting one, and the better the counterexample the
    more thoroughly it silenced the warning.  Two fields with opposite polarity
    had been collapsed into one name.

    They are now separate. A CONVERSE witness documents the point-level return
    construction; a complete mapped pair is the structured version. A strictness
    witness on an EQUIVALENCE instead exhibits the edge's own refutation.
    """
    findings = []
    dead = withdrawn_edges(graph)
    for eid in sorted(graph.edges):
        e = graph.edges[eid]
        if _withdrawn_and_unridden(graph, eid, dead):
            continue
        if e["type"] != K.EQUIVALENCE:
            continue
        if e.get("converse_witness") or e.get("cite") or K.is_mapped_equivalence(e):
            continue
        findings.append(Finding(
            "UNJUSTIFIED-EQUIVALENCE", "UNJUSTIFIED-EQUIVALENCE:%s" % eid,
            DEBT, eid,
            # THE FIELD THIS RULE TESTS, not a neighbouring one. It read
            # `converse_witness` and reported the absence of `witness`, and on
            # an EQUIVALENCE those two have OPPOSITE POLARITY -- `witness` is
            # about a point of the model, `converse_witness` about recovering
            # one across the edge. A live session wrote the field the message
            # named and got two findings CONTRADICTING EACH OTHER on the same
            # edge in the same run: one saying it carries a witness, this one
            # saying it carries none.
            #
            # The docstring above describes exactly this field-name collapse as
            # a bug already fixed. The code was split; the message was not.
            "edge %s (%s -> %s) is typed EQUIVALENCE with neither a "
            "`converse_witness` nor a `cite`.\n  EQUIVALENCE is the only type "
            "that forbids "
            "nothing, so this one row licenses every transport across the "
            "step, in both directions, unconditionally."
            % (eid, e["src"], e["dst"]),
            "Exhibit the converse -- the construction that recovers a point of "
            "%s from a point of %s -- or cite where it is proved. If you "
            "cannot do either, the step is a NECESSARY_CONDITION and should "
            "say so; nothing is lost by the weaker type except conclusions you "
            "were not entitled to." % (e["src"], e["dst"])))
    return findings


def check_supersession(graph, accepted=None):
    """A supersession must satisfy the obligation it inherits, not route round it.

    THE CEGAR STEP.  A refusal names the refinement that would legitimately
    resolve it; this makes only that refinement count.

    The pieces already existed and could not talk to each other.  The discharge
    recorded against the live obligation read, verbatim:

        "DISCHARGE BY DERIVING Delta'_4, not by naming a relaxation."

    That is exactly right and enforced nothing, because it is prose in a
    baseline file.  A blind run then discharged it by naming a relaxation --
    declaring a parallel edge with a permissive type -- and every check stayed
    green.

    A baseline entry may now pin `admits: ["DERIVE"]`.  A superseding edge
    declares `discharge_kind`.  If the kind is not admitted, the supersession
    is refused and the original obligation stays live, which is the whole
    point: the only exit is the one the obligation asked for.
    """
    accepted = accepted or {}
    findings = []
    for eid in sorted(graph.edges):
        e = graph.edges[eid]
        old = e.get("supersedes")
        if not old:
            continue
        if old not in graph.edges:
            findings.append(Finding(
                R_SUPERSEDE, "%s:%s" % (R_SUPERSEDE, eid), UNSOUND_PREMISE,
                eid,
                "edge %s supersedes %r, which is not an edge in this graph."
                % (eid, old),
                "Name the edge actually being replaced, or drop the field."))
            continue
        kind = e.get("discharge_kind")
        # Which obligations did the superseded edge carry?
        inherited = sorted(
            fid for fid in accepted
            if fid.endswith(":" + old)
            or any(s[0] == old
                   for iid in graph.inference_order
                   for s in graph.inferences[iid]["path"]
                   if fid == "%s:%s" % (R_TRANSPORT, iid)))
        blocked = [fid for fid in inherited
                   if (accepted[fid] or {}).get("admits")
                   and kind not in (accepted[fid] or {}).get("admits", [])]
        if blocked:
            findings.append(Finding(
                R_SUPERSEDE, "%s:%s" % (R_SUPERSEDE, eid), UNSOUND_PREMISE,
                eid,
                "edge %s supersedes %s with discharge_kind=%s, but %s was "
                "carrying an obligation that admits only %s.\n  %s\n"
                "  The obligation is INHERITED, not cleared: replacing the "
                "edge does not supply what the refusal was waiting for."
                % (eid, old, kind, old,
                   " / ".join(sorted({k for fid in blocked
                                      for k in accepted[fid]["admits"]})),
                   "; ".join("%s -- %s" % (fid, (accepted[fid] or {}).get("why")
                                           or "(no reason recorded)")
                             for fid in blocked)),
                "Supply the discharge the obligation actually asks for. If you "
                "believe the obligation was mis-stated -- that retyping really "
                "is the right move -- change what it admits explicitly and say "
                "why; that is a judgement, and it should be visible as one "
                "rather than routed around.",
                semantic_key="%s->%s:%s" % (eid, old, kind)))
    return findings


def check_partitions(graph):
    """Branch edges must run BRANCH -> PARENT, and a covered parent is derivable.

    A branch is `parent AND condition`, so V(branch) subset V(parent) and the
    branch is the TIGHTER model.  Drawn the other way, the graph asserts the
    parent is contained in each branch -- and since branches are mutually
    exclusive, that is consistent only if the parent is EMPTY, which is
    invariably the thing under investigation.

    The live consequence, twice: an EMPTY claim established on ONE branch rode
    `NECESSARY_CONDITION/AGAINST/EMPTY` and landed on the WHOLE parent, while
    the inference's own prose said "branch".  A result about one of three cases
    was recorded as a result about all of them, and nothing flagged it.

    This rule also reports the GOOD case: when every branch of a partition
    carries an EMPTY claim, emptiness of the parent is genuinely derivable --
    that is what a partition is FOR -- and saying so turns a piece of
    mathematics that previously lived in a note into a prompt to record it as
    an inference the checker can see.
    """
    findings = []
    for pid in sorted(graph.partitions):
        p = graph.partitions[pid]
        parent, branches = p["parent"], p["branches"]
        for eid in sorted(graph.edges):
            e = graph.edges[eid]
            if _withdrawn_and_unridden(graph, eid):
                continue
            if e["src"] != parent or e["dst"] not in branches:
                continue
            findings.append(Finding(
                R_PARTITION, "%s:%s:%s" % (R_PARTITION, pid, eid),
                UNSOUND_PREMISE, eid,
                "edge %s runs %s -> %s, from a partition PARENT to one of its "
                "BRANCHES, and is typed %s.\n"
                "  A branch is `parent AND condition`, so V(%s) is a SUBSET of "
                "V(%s) and the edge belongs the other way round. As drawn, the "
                "graph asserts the parent is contained in the branch -- and "
                "since the branches of %s are alternatives, that holds only if "
                "%s is empty, which is what a case split is normally trying to "
                "decide.\n"
                "  Consequence: a claim established on this one branch travels "
                "to the whole parent as though it covered every case."
                % (eid, parent, e["dst"], e["type"], e["dst"], parent, pid,
                   parent),
                "Reverse it: %s -> %s. Then a result on the branch reaches the "
                "parent only ALONG the arrow, where the cells that would "
                "wrongly generalise it are refused, and covering every case "
                "becomes a joint argument over all %d branches rather than a "
                "single hop." % (e["dst"], parent, len(branches))))
        # The payoff case, reported so it gets recorded rather than assumed.
        # A BRANCH IS COVERED BY A DERIVED CONCLUSION TOO, and reading only
        # claims made a real result unrecordable.
        #
        # A live session closed the last open branch of a three-way split with
        # a clean, licensed inference concluding EMPTY at that branch -- and it
        # contributed ZERO here, because this looked at where a premise LIVES
        # and never at where a path LANDS. Its two ways out were both worse
        # than the gap: duplicate the derived conclusion as a second claim,
        # double-counting one argument as two records, or inline the transport,
        # which the partition path does not accept. It accepted an obligation
        # instead, and the campaign's completed argument went unsigned.
        #
        # The graph reasoned about claims and edges and treated its own
        # conclusions as second-class. A conclusion the checker has LICENSED is
        # better evidence than a claim somebody declared, not worse.
        derived_at = {}
        for iid in graph.inference_order:
            inf = graph.inferences[iid]
            if inf.get("superseded_by"):
                continue
            if inf.get("concludes_kind") != K.EMPTY:
                continue
            at = inf.get("concludes_at")
            if at in branches:
                derived_at.setdefault(at, []).append(iid)
        empty_at = {b: sorted(
            [cid for cid, c in graph.claims.items()
             if c.get("model") == b and c["kind"] == K.EMPTY]
            + ["%s (derived)" % i for i in derived_at.get(b, [])])
            for b in branches}
        if all(empty_at[b] for b in branches):
            already = any(graph.inferences[i]["concludes_at"] == parent
                          and graph.inferences[i]["concludes_kind"] == K.EMPTY
                          for i in graph.inference_order)
            if not already:
                findings.append(Finding(
                    R_PARTITION, "%s:%s:covered" % (R_PARTITION, pid), DEBT,
                    pid,
                    "every branch of partition %s carries an EMPTY claim (%s), "
                    "and %s is asserted to cover %s -- so emptiness of %s "
                    "follows, and the graph does not record it.\n"
                    "  This is what the partition is for. Left unrecorded, the "
                    "step lives in whoever's head assembled it."
                    % (pid, "; ".join("%s: %s" % (b, ", ".join(empty_at[b]))
                                      for b in branches),
                       p["exhaustive"], parent, parent),
                    "Record it as one inference with %d premises -- the EMPTY "
                    "claim from each branch, plus %s -- all transported to %s. "
                    "That puts the completeness premise where a rule can see "
                    "it instead of in the prose around it."
                    % (len(branches), p["exhaustive"], parent)))
    return findings


def check_parallel_edges(graph):
    """Two edges joining the same pair of models in the same direction.

    THE HOLE T1 WENT THROUGH.  The store refuses a CONFLICTING REDECLARATION of
    an edge id -- that guarantee held perfectly -- so an agent that wanted to
    retype an edge simply declared a NEW one with the same endpoints and the
    type it wanted, and documented the move honestly as a "TYPED SUCCESSOR".

    Append-only prevents MUTATION and permits SUPERSESSION, and supersession
    has the same licensing effect with none of the visibility: the refusal and
    its own override sit side by side with no relation between them the checker
    can see.  In the live case, an UNTYPED edge was refusing a claim whose own
    cite read "NOT DERIVED.  Recorded so that using it is a type error rather
    than a habit"; the parallel edge handed that claim a licence, and `gp check`
    went on printing the refusal as though it still bound.

    Parallel edges are not always wrong -- two genuinely different maps can join
    the same objects.  So this reports rather than refuses, and the discharge
    asks for the one thing that distinguishes the cases: say which edge is
    authoritative and why the other is not.

    A WITHDRAWN EDGE IS NOT A SECOND EDGE.  This rule used to answer its own
    discharge with a shrug: an author who did exactly what it asked -- named
    the successor with `supersedes`, said how -- got the severity dropped to
    DEBT and the finding kept, so a fully declared chain of three still read
    "3 edges join A -> B" for the life of the campaign.  But the question this
    rule asks is WHICH ONE BINDS, and a declared supersession answers it: the
    replaced edge binds nothing.  Counting dead edges made the count say
    something untrue about a graph that had already been repaired, and put
    another undischargeable line in the baseline.

    Two guards, because the whole hazard of this repair is that supersession
    must never be a way to make a finding disappear:

      TRAFFIC.  An edge some live inference still rides is NOT withdrawn in
      effect, whatever its successor says, and it stays in the count.  This is
      where the untyped rule and this one legitimately differ: an UNTYPED edge
      that still carries traffic is refused loudly by `check_transport`, but a
      dead PERMISSIVE edge licenses that traffic silently, and this finding is
      the only thing in the system that would mention it.

      NO DOWNGRADE FOR A SUPERSESSION OF SOMETHING ELSE.  What remains after
      the dead are removed is by construction a set of edges none of which
      replaces another, so the parallelism between them was declared by nobody
      and the old `declared` downgrade would only fire for a `supersedes`
      pointing outside the pair -- an override bought with an unrelated
      sentence.  The severity now turns on traffic alone.
    """
    dead = withdrawn_edges(graph)
    findings = []
    by_ends = {}
    for eid in sorted(graph.edges):
        e = graph.edges[eid]
        by_ends.setdefault((e["src"], e["dst"]), []).append(eid)
    for (src, dst), at_ends in sorted(by_ends.items()):
        eids = [eid for eid in at_ends
                if eid not in dead or live_crossings(graph, [eid])]
        if len(eids) < 2:
            continue
        types = {eid: graph.edges[eid]["type"] for eid in eids}
        # Traffic over any of them makes this live rather than latent.
        crossing = live_crossings(graph, eids)
        sev = UNSOUND_PREMISE if crossing else DEBT
        withdrawn = [eid for eid in at_ends if eid not in eids]
        findings.append(Finding(
            R_PARALLEL, "%s:%s->%s" % (R_PARALLEL, src, dst), sev,
            "%s->%s" % (src, dst),
            "%d edges join %s -> %s: %s\n"
            "  Whatever the strictest of these refuses, the most permissive "
            "licenses, and nothing in the graph says which one binds.  An edge "
            "cannot be retyped (the fold refuses a conflicting redeclaration), "
            "so declaring a second one is how a refusal gets overridden without "
            "the override being visible as one.\n"
            "  inferences crossing them: %s%s"
            % (len(eids), src, dst,
               ", ".join("%s [%s]" % (e, types[e]) for e in eids),
               ", ".join(crossing) or "(none yet)",
               ("\n  not counted, superseded and unridden: %s"
                % ", ".join(withdrawn)) if withdrawn else ""),
            "Name which edge is authoritative. If the newer one supersedes the "
            "older, say so with `supersedes` -- that transfers the older "
            "edge's obligations rather than silently clearing them, and the "
            "checker will ask how each was discharged. If the two are "
            "genuinely different relations between the same models, the models "
            "are probably conflating two objects: split them.",
            semantic_key="|".join("%s:%s" % (e, types[e]) for e in eids)))
    return findings


def check_vacuous_conclusions(graph):
    """A conclusion drawn ABOUT a model the graph proves has no points.

    Every predicate is true of the empty set, so a PREDICATE or IDENTITY
    concluding at a model carrying an EMPTY claim says nothing -- while looking
    exactly like a result, carrying an evidence grade, and counting as a clean
    inference.

    This is the failure mode the source campaign has logged three times (most
    recently: 10 of a headline "30/30 published data points" could not fail),
    and T1 produced a fourth: a cap slope recorded `exact-checked` at a model
    the same batch proved empty, with the claim's own statement hedging "would
    read".

    Note it is NOT unsound -- vacuous truths are true.  It is graded TRIAGE
    because the damage is to the reader, who counts it as evidence.
    """
    findings = []
    for iid in graph.inference_order:
        inf = graph.inferences[iid]
        if inf["concludes_kind"] not in (K.PREDICATE, K.IDENTITY):
            continue
        empties = [cid for cid, c in sorted(graph.claims.items())
                   if c.get("model") == inf["concludes_at"] and c["kind"] == K.EMPTY]
        if not empties:
            continue
        findings.append(Finding(
            R_VACUOUS, "%s:%s" % (R_VACUOUS, iid), TRIAGE, iid,
            "inference %s concludes a %s at model %s, and the graph carries an "
            "EMPTY claim at that same model (%s).\n  asserted: %s\n"
            "  Every predicate holds of the empty set, so this conclusion is "
            "true and says nothing -- but it reads as a result and counts as a "
            "clean inference."
            % (iid, inf["concludes_kind"], inf["concludes_at"],
               ", ".join(empties), inf["asserted"]),
            "Either the emptiness is wrong, or this conclusion is vacuous and "
            "should say so where a reader will see it. If the predicate was "
            "derived BEFORE the emptiness was known, that is worth recording "
            "explicitly -- it is the difference between a result and an "
            "artifact of the order you found things in."))
    return findings


def check_self_built(graph):
    """A model built by an inference that reasons from a claim inside it.

    `built_by` records that a model owes its existence to an inference.  If
    that inference's premise LIVES IN the model it builds, the record is
    circular: the model is justified by reasoning conducted inside it, and
    `propagate_taint` cannot terminate meaningfully at that node because the
    model is its own antecedent.

    Usually a mis-recording rather than a fraud -- the model was declared
    earlier by other means and `built_by` was reached for to express "this
    inference is about that model".  But that is what an inference already
    says, and the two mean different things to the taint rule.
    """
    findings = []
    for mid in sorted(graph.built_by):
        for b in graph.built_by[mid]:
            inf = graph.inferences.get(b)
            if inf is None:
                continue
            premise = graph.claims[inf["claim"]]["model"]
            if premise != mid:
                continue
            findings.append(Finding(
                R_SELF_BUILT, "%s:%s:%s" % (R_SELF_BUILT, mid, b), DEBT, mid,
                "model %s is declared BUILT BY inference %s, whose premise "
                "(%s) lives in %s itself.\n  The model is recorded as owing "
                "its existence to reasoning conducted inside it, which makes "
                "the provenance circular and leaves the taint rule with no "
                "antecedent to follow."
                % (mid, b, inf["claim"], mid),
                "If %s was declared by a computation or an earlier step, drop "
                "the built_by -- the inference already records that it reasons "
                "about this model. If it really was constructed by this "
                "inference, the premise belongs at the model the construction "
                "started FROM." % mid))
    return findings


def check_aliases(graph):
    """Models declared to be one object, and the merge report that goes with it.

    The fan-out risk the first real merge exposed. Two agents in isolation both
    had to build the saturated system; they agreed on a NAME, so the fold raised
    a loud conflict on their differing descriptions -- the case that already
    worked. The dangerous case is two ids for one object: nothing collides, the
    merge composes silently, and the graph carries a duplicate that folds
    cleanly and is wrong.

    An alias records the identity without asking either branch to retract --
    neither was wrong, they described one object from two directions. What the
    checker can verify is CONSISTENCY, not identity: aliased models must not
    disagree about their chart, and their claims all now bear on one object, so
    a contradiction between them is a contradiction rather than two facts about
    two things.
    """
    findings = []
    for aid in sorted(graph.aliases):
        a = graph.aliases[aid]
        models = a["models"]
        charts = {graph.models[m].get("chart") for m in models
                  if graph.models[m].get("chart")}
        if len(charts) > 1:
            findings.append(Finding(
                R_ALIAS, "%s:%s:chart" % (R_ALIAS, aid), UNSOUND_PREMISE, aid,
                "same_as %s declares %s to be one object, but they are in "
                "different charts: %s.\n  A change of chart is a change of "
                "coordinates, and two descriptions in different coordinates "
                "are not automatically the same object -- that is a claim "
                "needing a map, not an alias."
                % (aid, ", ".join(models), ", ".join(sorted(charts))),
                "Either exhibit the coordinate change as an EQUIVALENCE with "
                "`forward`, `inverse`, and `ring_iso`, or the alias is "
                "wrong."))
        # Contradictory existence claims across an alias are now contradictory
        # AT ONE OBJECT, which is worth saying out loud.
        kinds = {}
        for m in models:
            for cid, c in sorted(graph.claims.items()):
                if c.get("model") == m and c["kind"] in EXISTENCE_OPPOSITE:
                    kinds.setdefault(c["kind"], []).append((cid, m))
        if len(kinds) > 1:
            findings.append(Finding(
                R_ALIAS, "%s:%s:contradiction" % (R_ALIAS, aid),
                UNSOUND_CONCLUSION, aid,
                "same_as %s declares %s to be one object, and they carry "
                "OPPOSITE existence claims:\n%s\n  Before the alias these were "
                "two facts about two things. After it they are a contradiction."
                % (aid, ", ".join(models),
                   "\n".join("    %-9s %s at %s" % (k, c, m)
                             for k, v in sorted(kinds.items())
                             for c, m in v)),
                "One of the claims is wrong, or the alias is. Note which is "
                "cheaper to check: an EXHIBITED witness settles a NONEMPTY by "
                "substitution."))
    return findings


def check_unexhibited_witness(graph):
    """NONEMPTY claims that are asserted rather than exhibited.

    The mirror of `UNKNOWN-IDENTITY-ORIGIN`, and DEBT for the same reason: a
    hole recorded as a hole.  What makes it worth reporting rather than
    shrugging at is that the discharge is unusually cheap -- substituting a
    point into the generators is arithmetic, and `cas_check_witness` does it.

    An existence claim is the one place where the evidence is an OBJECT rather
    than an argument, and objects can be checked.
    """
    findings = []
    for cid in sorted(graph.claims):
        c = graph.claims[cid]
        if c["kind"] != K.NONEMPTY or c.get("witness_kind") != K.ASSERTED:
            continue
        findings.append(Finding(
            R_WITNESS, "%s:%s" % (R_WITNESS, cid), DEBT, cid,
            "NONEMPTY claim %s at model %s is ASSERTED, not exhibited.\n"
            "  %s\n"
            "  Nothing here distinguishes holding the point from claiming to."
            % (cid, c.get("model") or c.get("family"), c["statement"]),
            "If you have the point, declare witness_kind EXHIBITED and give "
            "the coordinates in `witness_point` -- {\"x\": \"3\", \"y\": "
            "\"4\"}, a value per ring variable. `gp verify` substitutes it "
            "into the model's generators and confirms it is a solution, which "
            "is arithmetic and the cheapest check this system performs. "
            "`witness` takes the prose version and stays free text. If "
            "existence follows from something else already recorded, say "
            "DERIVED and record the inference. If it is genuinely an "
            "assertion -- a published claim you have not verified -- ASSERTED "
            "is the honest answer and this finding is the record of that."))
    return findings


def check_witness_point(graph):
    """Exhibited points: refuted, untested, or recorded only in prose.

    THE MIRROR OF `check_identity`, and it exists for the same reason.  An
    EMPTY claim must name a certificate or the graph will not fold; a NONEMPTY
    claim -- where the author is holding the object, the strongest evidence in
    the system -- carried nothing a solver could touch.  A live agent put it
    exactly: "the graph cannot currently distinguish 'I have the point' from
    'I claim to have the point'."

    THREE TIERS, and only the first is an accusation.

      NOT_A_POINT   substituted and it does not vanish. The NONEMPTY is
                    unsupported AT ITS OWN MODEL, which no transport typing
                    downstream would ever have surfaced -- the same shape as a
                    REFUTED identity.
      untested      the coordinates are recorded and nothing has substituted
                    them. One solver call, and it is arithmetic.

    AND NO THIRD TIER FOR A PROSE WITNESS, which the first version had.  It
    fired on five claims in the retrodiction fixtures and would fire on all
    twenty-five live ones, and the gate those fixtures enforce is exact: "a
    framework that flags a sound step is a false-positive generator and
    unusable".  Recording a point as "(x, y) = (3, 4)" is not a defect.

    `check_identity` had already settled the same question and said so -- its
    untested tier is "deliberately NARROW ... because it is replacing one
    specific stop and not inventing a general campaign to structure every
    identity in the corpus".  A campaign to structure every NONEMPTY is that
    same campaign.  So the on-ramp lives in the ASSERTED rule's discharge and
    in `gp declare`'s epilog, where it is available to somebody about to write
    a claim rather than aimed at everybody who already has.

    Which means this rule only ever speaks about claims that OPTED IN.
    """
    findings = []
    for cid in sorted(graph.claims):
        c = graph.claims[cid]
        if c["kind"] != K.NONEMPTY or c.get("superseded_by"):
            continue
        if c.get("witness_kind") != K.EXHIBITED:
            continue
        verdict = c.get("witness_verdict")
        if verdict == "NOT_A_POINT":
            findings.append(Finding(
                R_WITNESS, "%s:refuted:%s" % (R_WITNESS, cid),
                UNSOUND_CONCLUSION, cid,
                "NONEMPTY claim %s exhibits a point that is NOT ON %s: %s"
                % (cid, c.get("model"), c.get("witness_why") or "(no detail)")
                + "\n  Substituting a point into the generators is arithmetic, "
                  "so this is a refutation and not a failed cheap test. The "
                  "existence claim is unsupported at the model it was made at, "
                  "and anything transported from it rests on nothing.",
                "Correct the coordinates or withdraw the claim. If a point "
                "really does exist but this is not it, the honest record is "
                "witness_kind ASSERTED or DERIVED -- both are legal, and "
                "neither pretends to an object you do not have.",
                semantic_key=cid))
            continue
        if verdict:
            continue
        if c.get("witness_point"):
            findings.append(Finding(
                R_WITNESS, "%s:untested:%s" % (R_WITNESS, cid), TRIAGE, cid,
                "NONEMPTY claim %s records its point and nothing has "
                "substituted it.\n"
                "  The cheapest check in the system: evaluating the "
                "generators at a point has no interpretation to argue about, "
                "no ordering assumption and no field subtlety. Either they all "
                "vanish or one of them does not." % cid,
                "Run `gp verify`. It substitutes every structured witness and "
                "records the verdict, and a NOT_A_POINT answer would mean the "
                "existence claim is unsupported at its own model.",
                semantic_key=cid))
    return findings


# THE VERDICT BEATS THE DECLARATION, and until now it did not.
#
# `verify.identity` computes an identity's origin by reduction and RECORDS it
# on the claim.  The transport layer went on reading the author's declared
# `identity_origin` -- so a claim declaring AMBIENT, with a stored verdict of
# VERIFIED_DERIVED, transported ALONG a NECESSARY_CONDITION and was reported
# CLEAN.  That cell is licensed only for AMBIENT, and `x = 0` in k[x]/(x) is
# exactly the counterexample the kernel quotes.
#
# The tool spent CAS time computing the one field that decides this transport,
# wrote the answer into the same graph, and then licensed off the declaration
# contradicting it.  That is the honour system surviving INSIDE the machinery
# built to replace it.
_VERDICT_ORIGIN = {"VERIFIED_AMBIENT": K.AMBIENT,
                   "VERIFIED_DERIVED": K.DERIVED}


def effective_origin(claim):
    """The origin transport should use: computed if there is one, else declared.

    A verdict is evidence and a declaration is a word.  Where they disagree the
    evidence wins, and `check_origin_contradiction` says so out loud rather
    than letting the correction happen silently.
    """
    return (_VERDICT_ORIGIN.get(claim.get("identity_verdict"))
            or claim.get("identity_origin"))


def effective_ring_iso(edge):
    """Use a declared flag only when its available evidence supports it.

    Structured maps are checkable, so they fail closed until VERIFIED and any
    non-VERIFIED verdict beats the declaration. VERIFIED never mints a flag.
    Legacy citation-backed equivalences remain declarable for historical graphs
    that carry no machine-readable ideals, but an unsupported bare
    boolean opens nothing.
    """
    if edge.get("ring_iso") is not True:
        return False
    if not K.is_mapped_equivalence(edge):
        return False
    return edge.get("ring_iso_verdict") == "VERIFIED"


def effective_exact_contraction(edge):
    """Whether a constructed elimination has exact contraction authority.

    Two independent proofs are required: the existing operation validator
    establishes that the target invented no equations, and either a polynomial
    section or a checked pure-lex certificate establishes that it omitted no
    retained source equations.
    """
    if edge.get("built_by_operation") != "Eliminate":
        return True
    return (edge.get("output_verdict") == "VERIFIED"
            and edge.get("contraction_verdict") in (
                "VERIFIED_SECTION", "VERIFIED_GROEBNER"))


def _condition_payload(claim_or_condition):
    """Return a structured condition from either its claim or direct shape."""
    if not isinstance(claim_or_condition, dict):
        return None
    if "condition" in claim_or_condition:
        return claim_or_condition.get("condition")
    if "all" in claim_or_condition:
        return claim_or_condition
    return None


def structured_condition_closed(claim_or_condition):
    """Whether a checked exact-affine condition defines a closed subset."""
    condition = _condition_payload(claim_or_condition) or {}
    atoms = condition.get("all") if isinstance(condition, dict) else None
    return bool(atoms) and all(
        isinstance(atom, dict) and atom.get("relation") == "ZERO"
        for atom in atoms)


def condition_expressible_at(graph, claim_or_condition, model_id):
    """Whether every structured condition atom parses in one model's ring."""
    condition = _condition_payload(claim_or_condition) or {}
    atoms = condition.get("all") if isinstance(condition, dict) else None
    model = graph.models.get(model_id) or {}
    ring_vars = model.get("ring_vars") or []
    characteristic = model.get("characteristic")
    if not atoms or not ring_vars or type(characteristic) is not int:
        return False
    try:
        for atom in atoms:
            G.parse_polynomial(atom["expression"], ring_vars, characteristic)
    except (G.CertificateError, KeyError, TypeError, ValueError):
        return False
    return True


def _canonical_condition_at(graph, condition, model_id):
    """Recheck and canonicalize a structured condition in one exact ring."""
    payload = _condition_payload(condition) or {}
    atoms = payload.get("all") if isinstance(payload, dict) else None
    model = graph.models.get(model_id) or {}
    ring_vars = model.get("ring_vars") or []
    characteristic = model.get("characteristic")
    if not atoms or not ring_vars or type(characteristic) is not int:
        raise G.CertificateError(
            "the destination model has no exact polynomial ring")
    return {"all": [
        {
            "relation": atom["relation"],
            "expression": G.canonical_polynomial(
                atom["expression"], ring_vars, characteristic),
        }
        for atom in atoms
    ]}


def pullback_condition_across_edge(graph, condition, edge, direction):
    """Pull target predicate syntax back through a concrete point map.

    This is the runtime projection of Lean's generic `Pullback` law. Abstract
    PREDICATE transport remains the kernel's decision; this helper preserves
    machine-readable syntax only for a literal identity-coordinate map or a
    currently checked constructor-built elimination projection.
    """
    if direction != K.AGAINST:
        return None, "structured predicate pullback requires AGAINST"
    source = graph.models.get(edge.get("src")) or {}
    target = graph.models.get(edge.get("dst")) or {}
    source_vars = source.get("ring_vars") or []
    target_vars = target.get("ring_vars") or []
    source_characteristic = source.get("characteristic")
    target_characteristic = target.get("characteristic")

    if edge.get("map_kind") == K.IDENTITY_MAP:
        if (not source_vars or set(source_vars) != set(target_vars)
                or type(source_characteristic) is not int
                or source_characteristic != target_characteristic):
            return None, (
                "structured condition pullback stopped: the declared identity "
                "map does not have matching exact endpoint rings")
        mode = "literal identity point map"
    elif (edge.get("type") == K.IMAGE_CLOSURE
          and edge.get("built_by_operation") == "Eliminate"
          and edge.get("map_kind") == K.POLYNOMIAL
          and edge.get("output_verdict") == "VERIFIED"):
        eliminated = target.get("eliminated")
        valid_eliminated = (
            isinstance(eliminated, list) and bool(eliminated)
            and len(eliminated) == len(set(eliminated))
            and all(name in source_vars for name in eliminated))
        expected_target = (
            [name for name in source_vars if name not in set(eliminated)]
            if valid_eliminated else None)
        if (type(source_characteristic) is not int
                or source_characteristic != target_characteristic
                or target_vars != expected_target):
            return None, (
                "structured condition pullback stopped: the checked Eliminate "
                "edge is not an exact retained-coordinate projection")
        mode = "checked retained-coordinate projection"
    else:
        return None, (
            "structured condition pullback stopped: this edge has no concrete "
            "identity or checked projection map")

    try:
        rewritten = _canonical_condition_at(
            graph, condition, edge.get("src"))
    except (G.CertificateError, KeyError, TypeError, ValueError) as exc:
        return None, "structured condition pullback failed exact checking: %s" % exc
    return rewritten, (
        "pulled back %d structured condition atom(s) through the %s"
        % (len(rewritten["all"]), mode))


def rewrite_condition_across_equivalence(graph, condition, edge, direction):
    """Reindex one structured condition through a known coordinate change.

    `forward` is the point map, so ALONG uses the polynomial `inverse` and
    AGAINST uses `forward`. Only a current verified mapped ring isomorphism or
    a literal identity-coordinate equivalence preserves machine-readable
    expressibility. The predicate transport itself remains the kernel's job.
    """
    if edge.get("type") != K.EQUIVALENCE:
        return None, "condition rewrite requires an EQUIVALENCE"
    source_id, target_id = (
        (edge["src"], edge["dst"])
        if direction == K.ALONG else (edge["dst"], edge["src"]))
    source = graph.models.get(source_id) or {}
    target = graph.models.get(target_id) or {}
    source_vars = source.get("ring_vars") or []
    target_vars = target.get("ring_vars") or []
    characteristic = target.get("characteristic")
    if (not source_vars or set(source_vars) != set(target_vars)
            or type(characteristic) is not int
            or source.get("characteristic") != characteristic):
        return None, (
            "structured condition could not be rewritten: endpoint exact "
            "polynomial rings do not agree")

    mapped = K.is_mapped_equivalence(edge)
    if mapped:
        if not effective_ring_iso(edge):
            return None, (
                "structured condition could not be rewritten: the mapped "
                "equivalence lacks current VERIFIED ring-isomorphism authority")
        images = edge["inverse" if direction == K.ALONG else "forward"]
        orientation = "inverse" if direction == K.ALONG else "forward"
    elif edge.get("map_kind") == K.IDENTITY_MAP:
        images = dict((name, name) for name in target_vars)
        orientation = "identity"
    else:
        return None, (
            "structured condition could not be rewritten: this equivalence "
            "has no checked polynomial coordinate substitution")

    payload = _condition_payload(condition) or {}
    try:
        rewritten = {"all": [
            {
                "relation": atom["relation"],
                "expression": G.substitute_polynomial(
                    atom["expression"], target_vars, images, characteristic),
            }
            for atom in payload.get("all") or []
        ]}
    except (G.CertificateError, KeyError, TypeError, ValueError) as exc:
        return None, "structured condition rewrite failed exact checking: %s" % exc
    if not rewritten["all"]:
        return None, "structured condition rewrite produced no atoms"
    return rewritten, (
        "rewrote %d structured condition atom(s) with the %s point-map "
        "substitution" % (len(rewritten["all"]), orientation))


def effective_point_surjective(edge):
    """Whether every recorded target point has a checked source-point lift.

    This is strictly stronger than presenting the closure of an image. The
    runtime producers are a checked polynomial section or finite lift cover
    paired with the
    independent no-invention verdict. Manual IMAGE_CLOSURE declarations and
    pure Groebner certificates do not acquire this authority.
    """
    return (edge.get("built_by_operation") == "Eliminate"
            and edge.get("output_verdict") == "VERIFIED"
            and (edge.get("contraction_verdict") == "VERIFIED_SECTION"
                 or edge.get("point_lift_verdict")
                    == "VERIFIED_POINT_LIFT"))


def effective_geometric_closure(edge):
    """Whether closure-level geometric image transport is established.

    Manual IMAGE_CLOSURE edges assert that semantic relation. For a constructed
    elimination, a checked section or finite lift cover establishes this
    relation as a
    consequence of the stronger point-surjectivity fact. A pure Groebner
    certificate proves ideal equality but supplies no point lift.
    """
    if edge.get("built_by_operation") != "Eliminate":
        return True
    return (edge.get("output_verdict") == "VERIFIED"
            and (edge.get("contraction_verdict") == "VERIFIED_SECTION"
                 or edge.get("point_lift_verdict")
                    == "VERIFIED_POINT_LIFT"))


def effective_image_complete(edge):
    """Epoch-2 compatibility view: both exact authorities at once."""
    return (effective_exact_contraction(edge)
            and effective_geometric_closure(edge))


def effective_certificate(claim):
    """The certificate kind transport should use: refuted beats declared.

    `derive_scope` reads the certificate KIND to decide whether an emptiness is
    field-independent, and the kernel calls that the most load-bearing line in
    the system. `verify.unit_ideal` can report NOT_UNIT -- the ideal does not
    reduce to 1, so UNIT_IDEAL_CERT is not the certificate this claim has --
    and nothing read it.

    THAT IS THE ERRATUM'S OWN SHAPE. UNIT_IDEAL_CERT base-changes; a
    field-relative emptiness wearing it derives SCHEME scope it never earned.
    A live campaign has one right now: an ideal that reduces to `t^2-3`, which
    is empty over Q and not over Q(sqrt 3).

    Returning None rather than a corrected kind is deliberate. The verifier
    knows the declared kind is WRONG; it does not know which kind is right,
    and guessing would replace a false licence with a different one. `None`
    makes `derive_scope` refuse, which is the honest answer.
    """
    certificate = claim.get("certificate")
    if claim.get("certificate_verdict") == "NOT_UNIT":
        return None
    if (certificate == "LOCALIZED_UNIT_IDEAL_CERT"
            and claim.get("certificate_verdict") != "VERIFIED"):
        return None
    return certificate


def check_localized_unit_certificates(graph):
    """A localized-unit name grants nothing until its exact proof replays."""
    findings = []
    for cid in sorted(graph.claims):
        claim = graph.claims[cid]
        if (claim.get("superseded_by")
                or claim.get("certificate")
                    != "LOCALIZED_UNIT_IDEAL_CERT"
                or claim.get("certificate_verdict") == "VERIFIED"):
            continue
        findings.append(Finding(
            R_EVIDENCE, "%s:localized-unit:%s" % (R_EVIDENCE, cid),
            DEBT, cid,
            "claim %s names LOCALIZED_UNIT_IDEAL_CERT but has no current "
            "VERIFIED localized-unit verdict. The name alone grants no "
            "effective certificate, base-change authority, or partition "
            "coverage." % cid,
            "Run `gp verify`. A bounded miss remains UNVERIFIED; only a "
            "guard-monomial cofactor identity replayed against the exact open "
            "model discharges this debt.",
            semantic_key=cid))
    return findings

def check_refuted_evidence(graph):
    """A certificate or an isomorphism the verifier REFUTED, said out loud.

    `effective_certificate` and `effective_ring_iso` make the computed answer
    win, which is right. But a silent correction is its own defect -- the
    author believes something the graph no longer acts on -- so it is reported,
    for the same reason `check_origin_contradiction` reports the third case.

    BOTH OF THESE ARE MORE DANGEROUS THAN THEY LOOK.

      NOT_UNIT             `derive_scope` reads the certificate KIND to decide
                           whether an emptiness is FIELD-INDEPENDENT, which the
                           kernel calls the most load-bearing line in the
                           system. UNIT_IDEAL_CERT base-changes; an emptiness
                           that is really field-relative wearing it derives
                           SCHEME scope it never earned. That is the shape of
                           the erratum this project started from.
      NOT_AN_ISOMORPHISM   `ring_iso` licenses an IDENTITY to cross an
                           EQUIVALENCE in BOTH directions, on the strength of a
                           boolean. A bijection on solutions is not an
                           isomorphism of coordinate rings, and the verifier
                           reduces the maps to tell the difference.

    Both were being written into the graph and read by nothing.
    """
    findings = []
    for cid in sorted(graph.claims):
        c = graph.claims[cid]
        if c.get("superseded_by") or c.get("certificate_verdict") != "NOT_UNIT":
            continue
        findings.append(Finding(
            R_REFUTED_EVIDENCE, "%s:cert:%s" % (R_REFUTED_EVIDENCE, cid),
            UNSOUND_PREMISE, cid,
            "claim %s declares certificate %s and the verifier REFUTED it: %s"
            % (cid, c.get("certificate"),
               c.get("certificate_why") or "(no detail)")
            + "\n  The certificate kind is what `derive_scope` reads to decide "
              "whether this emptiness is field-independent, so a wrong kind is "
              "not a labelling error -- it is a claim to a scope the "
              "mathematics does not give. Transport now treats this claim as "
              "having NO certificate, which is why nothing it premises is "
              "licensed.",
            "This is a statement about the CERTIFICATE and not about the "
            "emptiness -- the model may well be empty, established by other "
            "means. Name the certificate kind that actually closes it. If the "
            "argument is field-relative, the kind must be too, and "
            "`derive_scope` will then require you to name the field.",
            semantic_key=cid))
    for pid in sorted(graph.partitions):
        p = graph.partitions[pid]
        if p.get("superseded_by"):
            continue
        if p.get("exhaustive_verdict") == "NOT_GEOMETRICALLY_EXHAUSTIVE":
            findings.append(Finding(
                R_COVERAGE, "%s:geometric:%s" % (R_COVERAGE, pid),
                DEBT, pid,
                "partition %s has a computed hole over the algebraic closure, "
                "but that does not prove a hole over its declared base field: "
                "%s"
                % (pid, p.get("exhaustive_why") or "(no detail)"),
                "Prove the parent empty over the base field, add the missing "
                "branch, or provide a base-field coverage certificate. Until "
                "then the partition cannot license a case-split inference.",
                semantic_key=pid))
            continue
        if p.get("exhaustive_verdict") != "NOT_EXHAUSTIVE":
            continue
        findings.append(Finding(
            R_REFUTED_EVIDENCE, "%s:cover:%s" % (R_REFUTED_EVIDENCE, pid),
            UNSOUND_PREMISE, pid,
            "partition %s declares its branches exhaustive and the verifier "
            "REFUTED it: %s"
            % (pid, p.get("exhaustive_why") or "(no detail)")
            + "\n  Every conclusion of the form \"and those are all the "
              "cases\" rests on this, including any EMPTY established branch "
              "by branch.",
            "Add the missing branch, or narrow the parent to the region the "
            "branches do cover and re-anchor the claims there. If the split "
            "is genuinely complete and the verifier disagrees, the branches "
            "are not `parent AND condition` -- check that each carries the "
            "parent's equations as well as its own.",
            semantic_key=pid))
    for eid in sorted(graph.edges):
        e = graph.edges[eid]
        if (not e.get("superseded_by")
                and e.get("output_verdict") == "NOT_THE_STATED_OUTPUT"):
            findings.append(Finding(
                R_REFUTED_EVIDENCE, "%s:output:%s" % (R_REFUTED_EVIDENCE, eid),
                UNSOUND_PREMISE, eid,
                "the model built by %s across %s does not have the ideal that "
                "operation produces: %s"
                % (e.get("built_by_operation"), eid,
                   e.get("output_why") or "(no detail)")
                + "\n  Every claim at that model is about a different variety "
                  "from the one its construction names.",
                "Re-run the operation and record what it returns, or correct "
                "the generators by hand and say which. If the ideal was typed "
                "rather than computed, that is the defect -- the constructor "
                "emits a program precisely so the answer does not have to be "
                "transcribed.",
                semantic_key=eid))
        if (e.get("superseded_by")
                or e.get("ring_iso") is not True
                or e.get("ring_iso_verdict") != "NOT_AN_ISOMORPHISM"):
            continue
        findings.append(Finding(
            R_REFUTED_EVIDENCE, "%s:iso:%s" % (R_REFUTED_EVIDENCE, eid),
            UNSOUND_PREMISE, eid,
            "edge %s declares `ring_iso` and the verifier REFUTED it: %s"
            % (eid, e.get("ring_iso_why") or "(no detail)")
            + "\n  That flag is the whole licence for an IDENTITY to cross an "
              "EQUIVALENCE, in either direction. The declared maps failed an "
              "ideal-pullback or inverse-law check, so they do not establish "
              "an isomorphism of coordinate rings.",
            "Drop `ring_iso` and the EQUIVALENCE still carries every existence "
            "claim -- it is only the IDENTITY cells that need it. If the two "
            "models really are isomorphic as rings, the declared `forward` and "
            "`inverse` are not the maps that show it.",
            semantic_key=eid))
    return findings


def check_origin_contradiction(graph):
    """A claim whose declared origin the verifier disagreed with.

    `effective_origin` makes the computed answer win, which is right -- a
    verdict is evidence and a declaration is a word. But a silent correction
    is its own defect: the author believes something the graph no longer acts
    on, and the next reader sees a field that is not the one being used.

    So the disagreement is reported, and at UNSOUND_PREMISE when the
    declaration was the STRONGER of the two. Declaring AMBIENT where the
    computation says DERIVED is a claim to a licence the mathematics does not
    give, and it is the direction that produced a live false transport: the
    claim rode a NECESSARY_CONDITION ALONG, a cell licensed only for AMBIENT,
    and was reported clean while the graph already held the refutation.
    """
    findings = []
    for cid in sorted(graph.claims):
        c = graph.claims[cid]
        if c.get("superseded_by"):
            continue
        computed = _VERDICT_ORIGIN.get(c.get("identity_verdict"))
        declared = c.get("identity_origin")
        if not computed or not declared or computed == declared:
            continue
        overclaimed = declared == K.AMBIENT and computed == K.DERIVED
        findings.append(Finding(
            R_ORIGIN_CONFLICT, "%s:%s" % (R_ORIGIN_CONFLICT, cid),
            UNSOUND_PREMISE if overclaimed else TRIAGE, cid,
            "claim %s declares `identity_origin: %s` and the verifier computed "
            "%s.\n  %s"
            % (cid, declared, computed,
               ("AMBIENT is the STRONGER reading -- it says the rewriting never "
                "used the model's equations -- and the computation says it "
                "did. Transport is now decided by the computed value, so this "
                "claim licenses less than its declaration asks for."
                if overclaimed else
                "The computed value is what transport now uses; the "
                "declaration understates what was established.")),
            "Supersede the claim with `identity_origin: %s` and a "
            "`discharge_kind` -- that field is LICENSING, so the correction "
            "gets the second look it deserves. Leaving the two disagreeing "
            "means the graph shows a reader one thing and acts on another."
            % computed,
            semantic_key=cid))
    return findings


def check_unknown_identity_origin(graph):
    """IDENTITY claims whose origin is recorded as not yet established.

    The claim-level twin of `check_untyped`, and graded the same way: an
    UNKNOWN origin is a hole recorded as a hole, so DEBT.  Traffic across it is
    already handled by the transport rule, which refuses the cells that need
    AMBIENT and reports them at UNSOUND_PREMISE.

    What makes this different from every other debt in the system is that it
    has a MECHANICAL discharge.  Whether a rewriting is ambient or derived is
    not a matter of judgement -- it is a normal-form computation -- so the
    discharge names the call instead of asking the author to introspect.  That
    is the difference between marking out negative space and merely nagging.
    """
    findings = []
    for cid in sorted(graph.claims):
        c = graph.claims[cid]
        if c["kind"] != K.IDENTITY or c.get("identity_origin") != K.UNKNOWN:
            continue
        blocked = sorted(iid for iid in graph.inference_order
                         if graph.inferences[iid]["claim"] == cid)
        findings.append(Finding(
            R_IDENTITY_ORIGIN, "%s:%s" % (R_IDENTITY_ORIGIN, cid), DEBT, cid,
            "IDENTITY claim %s at model %s records its origin as UNKNOWN.\n"
            "  %s\n"
            "  Until it is settled the rewriting restricts to tighter models "
            "but cannot travel to looser ones, because only an AMBIENT "
            "identity survives dropping this model's equations.\n"
            "  inferences carrying it: %s"
            % (cid, c["model"], c["statement"],
               ", ".join(blocked) or "(none yet)"),
            "This is decidable, not a judgement call. Let d = LHS - RHS for "
            "this rewriting and reduce it:\n"
            "    d expands to 0 in the polynomial ring        -> AMBIENT\n"
            "    d != 0 but reduces to 0 modulo %s's ideal    -> DERIVED\n"
            "    neither                                      -> the claim is "
            "FALSE at %s, which is a bigger finding than either origin\n"
            "  `cas_classify_identity` runs exactly this and records the "
            "answer with the computation behind it, so the origin is derived "
            "from a reduction rather than asserted."
            % (c["model"], c["model"])))
    return findings


def check_self_refuting_equivalence(graph):
    """An EQUIVALENCE edge carrying evidence that it is NOT one.

    `strictness_witness` exhibits what the step loses -- a point of the target
    absent from the source.  On an edge typed EQUIVALENCE that is not a missing
    justification, it is a stated contradiction: the type says nothing is lost
    and the evidence field beside it names the thing lost.

    Graded on the same principle as UNTYPED: the contradiction ITSELF is DEBT,
    because recording it is better than not; drawing a conclusion ACROSS it is
    UNSOUND_PREMISE, because EQUIVALENCE licenses every cell unconditionally and
    so every one of those conclusions rests on a relation the edge's own
    evidence denies.
    """
    findings = []
    dead = withdrawn_edges(graph)
    for eid in sorted(graph.edges):
        e = graph.edges[eid]
        if _withdrawn_and_unridden(graph, eid, dead):
            continue
        # Legacy `witness` meant strictness in every existing use, so it is read
        # here too -- an old graph that documented an equivalence with its own
        # counterexample should surface, not stay quiet because it used the old
        # field name.
        strict = e.get("strictness_witness") or e.get("witness")
        if e["type"] != K.EQUIVALENCE or not strict:
            continue
        crossing = sorted(iid for iid in graph.inference_order
                          if any(s[0] == eid
                                 for s in graph.inferences[iid]["path"]))
        findings.append(Finding(
            "SELF-REFUTING-EQUIVALENCE", "SELF-REFUTING-EQUIVALENCE:%s" % eid,
            UNSOUND_PREMISE if crossing else DEBT, eid,
            "edge %s (%s -> %s) is typed EQUIVALENCE and carries a "
            "STRICTNESS witness -- evidence that the step is NOT an "
            "equivalence:\n  %s\n  EQUIVALENCE licenses every transport across "
            "the step in both directions, so this edge asserts a relation its "
            "own evidence refutes.\n  inferences crossing it: %s"
            % (eid, e["src"], e["dst"], strict,
               ", ".join(crossing) or "(none yet)"),
            "Decide which field is true. If the witness is right the step is "
            "lossy: retype it (NECESSARY_CONDITION if it drops equations, "
            "IMAGE_CLOSURE if it is an elimination) and the witness becomes "
            "the justification for the weaker type. If the step really is an "
            "equivalence, the witness is describing a different step -- move "
            "it to that edge and supply a `converse_witness` here instead."))
    return findings


def check_stale_premises(graph):
    """An inference resting on a claim its own author has replaced.

    SUPERSESSION DELIBERATELY DOES NOT REPOINT ANYTHING.  It would be easy to
    make an inference follow its premise to the replacement, and it would be
    the same mistake as every other silent upgrade in this codebase: the
    argument was checked against one record and would then be credited against
    a different one, with nobody looking.

    THE SEVERITY IS THE INTERESTING PART, and it is why the supersession kind
    is computed instead of declared.  If the replacement changed nothing that
    licenses a transport -- a citation, a caveat, an evidence grade -- the old
    argument is still exactly as sound as it was, and pointing it at the newer
    record is bookkeeping.  If a licensing attribute moved, or the claim now
    says something different, the argument rests on something that no longer
    exists in the form it was checked in, and it has to be redone.  An author
    who could self-report that distinction would just always report the cheap
    one.
    """
    findings = []
    for iid in graph.inference_order:
        inf = graph.inferences[iid]
        if inf.get("superseded_by"):
            continue
        for prem in inf["premises"]:
            cid = prem.get("claim")
            if not cid or cid not in graph.claims:
                continue
            old = graph.claims[cid]
            newer_id = old.get("superseded_by")
            if not newer_id:
                continue
            # A CLAIM MAY BE SPLIT INTO SEVERAL, so read every successor.
            # Bookkeeping only if ALL of them are AMEND: if any one changed
            # something that licenses a transport, the premise moved.
            ids = newer_id if isinstance(newer_id, list) else [newer_id]
            kinds = [graph.claims[i].get("discharge_kind")
                     for i in ids if i in graph.claims]
            kind = ", ".join(k for k in kinds if k) or None
            bookkeeping = bool(kinds) and all(k == K.AMEND for k in kinds)
            findings.append(Finding(
                R_STALE_PREMISE, "%s:%s:%s" % (R_STALE_PREMISE, iid, cid),
                DEBT if bookkeeping else UNSOUND_PREMISE,
                iid,
                "inference %s rests on claim %s, which %s superseded (%s)."
                % (iid, cid, S.successors(old), kind)
                + ("\n  Nothing that licenses a transport changed, so the "
                   "argument stands as checked. What is stale is the pointer."
                   if bookkeeping else
                   "\n  %s changed, so this argument was checked against a "
                   "record that no longer says what it said. The conclusion is "
                   "not withdrawn and is not licensed either -- it is "
                   "UNEXAMINED."
                   % (", ".join(sorted(set(
                       f for i in ids if i in graph.claims
                       for f in K.classify_supersession(
                           old, graph.claims[i])[1])))
                      or "The premise")),
                ("Redeclare this inference against %s and mark the old one "
                 "`supersedes`, so the graph says which argument is current. "
                 "Supersession does not repoint premises on its own: an "
                 "argument credited against a record it was never checked "
                 "against is the failure this refuses to automate."
                 % S.successors(old)),
                semantic_key="%s|%s" % (iid, cid)))
    return findings


def check_stale_paths(graph):
    """A live inference ROUTED OVER an edge its author has replaced.

    THE EXACT COMPLEMENT of `check_stale_premises`, and the precondition that
    makes silencing findings on withdrawn edges safe.  Supersession never
    repoints anything -- deliberately, since crediting an argument against a
    record it was never checked against is the failure this refuses to
    automate -- so an inference goes on riding the old edge after the author
    has declared a better one.

    Without this rule, the four edge-attribute rules would go quiet on a
    withdrawn edge and nothing anywhere would mention that live traffic still
    crosses it.  `_withdrawn_and_unridden` keeps them loud in that case; this
    says WHY, and says it against the inference rather than the edge, which is
    where the repair has to happen.

    The severity turns on the same question as STALE-PREMISE: did anything that
    LICENSES a transport actually move?  A successor that only gained a
    `converse_witness` or a `discharge_hint` licenses exactly what its
    predecessor did, so the argument stands as checked and the pointer is
    merely stale.  A successor that was retyped, or gained `ring_iso` or
    `zariski_dense`, licenses different cells -- and the argument was audited
    against the other ones.
    """
    findings = []
    dead = withdrawn_edges(graph)
    if not dead:
        return findings
    successor = {}
    for eid in sorted(graph.edges):
        old = graph.edges[eid].get("supersedes")
        if old in dead:
            successor[old] = eid
    for iid in graph.inference_order:
        inf = graph.inferences[iid]
        if inf.get("superseded_by"):
            continue
        for eid, direction in inf["path"]:
            if eid not in dead:
                continue
            new_id = successor.get(eid)
            newer = graph.edges.get(new_id) if new_id else None
            moved = ([f for f in K.EDGE_LICENSING_FIELDS
                      if graph.edges[eid].get(f) != newer.get(f)]
                     if newer else [])
            bookkeeping = newer is not None and not moved
            findings.append(Finding(
                R_STALE_PATH, "%s:%s:%s" % (R_STALE_PATH, iid, eid),
                DEBT if bookkeeping else UNSOUND_PREMISE, iid,
                "inference %s is routed over edge %s, which %s."
                % (iid, eid,
                   ("%s replaced" % new_id) if new_id else
                   "was withdrawn by %s" % graph.edges[eid].get("withdrawn_by"))
                + ("\n  It licenses exactly what %s licensed, so the argument "
                   "stands as checked and only the pointer is stale."
                   % eid if bookkeeping else
                   ("\n  The relation was withdrawn with no successor, so this "
                    "path no longer exists. The conclusion is not withdrawn "
                    "and is not licensed either -- it is UNEXAMINED."
                    if not newer else
                    "\n  %s changed, so this argument was audited against cells "
                    "the current edge does not open. The conclusion is not "
                    "withdrawn and is not licensed either -- it is UNEXAMINED."
                    % (", ".join(moved) or "The relation"))),
                ("Retract this inference if the conclusion is abandoned, or "
                 "redeclare it over a real path. A withdrawn edge has no "
                 "successor to repoint at."
                 if not new_id else
                 "Redeclare this inference over %s and mark the old one "
                 "`supersedes`. Supersession does not repoint a path on its "
                 "own: an argument credited against an edge it was never "
                 "checked against is the failure this refuses to automate."
                 % new_id),
                semantic_key="%s|%s" % (iid, eid)))
    return findings


def _group_size(graph, gid):
    """How many members the thing named `gid` covers: a family, or a group."""
    if gid in graph.families:
        return graph.families[gid]["count"]
    if gid in graph.groups:
        return graph.groups[gid]["settles"]
    return None


def check_families(graph):
    """ENUMERATION and COVERAGE.  The arithmetic half of a classification.

    ENUMERATION.  A family's `count` is an assertion somebody made, and a
    result of the form "k of N" is worthless if N is wrong.  One census DID
    check its own -- orbit sizes summing to 34,752 -- and that check had
    nowhere to live, so it went into prose and a `note`.  The obligation is the
    same shape as `partition.exhaustive`: name the claim, and the claim carries
    its own evidence grade.

    COVERAGE, and it is RECURSIVE.  The first version of this rule required
    every disposition's groups to total the family, which is wrong the moment a
    triage nests -- and a real one does: 1567 splits into 347 and 1220, then
    the 347 splits again into 343 and 4.  A disposition totals THE THING IT
    SPLITS, which may be a family or a group from an earlier split.

    Coverage cannot catch a paper nobody mentioned.  A live frontier read "32
    open" for months because five rows settled in the literature were sitting
    inside the residue, and 32 + 2 = 34 totals perfectly.  No tool catches
    that.  What it catches is the arithmetic, which is the half that is
    checkable, and what the ENUMERATION obligation adds is that the sweep
    itself becomes a graded claim rather than an assumption baked into a
    subtraction.
    """
    findings = []
    for fid in sorted(graph.families):
        fam = graph.families[fid]
        enum = fam.get("enumeration")
        if not enum or enum not in graph.claims:
            findings.append(Finding(
                R_FAMILY, "%s:%s" % (R_FAMILY, fid), UNSOUND_PREMISE, fid,
                "family %s declares count %d and names %s as the claim "
                "establishing it."
                % (fid, fam["count"],
                   "no claim" if not enum else "%r, which is not a claim" % enum)
                + "\n  Every 'k of N' result in this campaign divides by that "
                  "N. An uncounted family makes each of them a statement about "
                  "a number nobody vouched for.",
                "Record the enumeration as a claim at this family and name it "
                "in `enumeration` -- how the members were counted, and how you "
                "know the count is complete. One census verified its own by "
                "checking orbit sizes summed to the labelled total; that is "
                "exactly the claim this field wants.",
                semantic_key=fid))
    for cid in sorted(graph.claims):
        c = graph.claims[cid]
        # A COUNT claim is either a DISPOSITION (it splits something) or a
        # CROSS-COUNT (it intersects two groups). Only the first has coverage
        # arithmetic to check; the second is check_crosscuts' business.
        if c.get("kind") != K.COUNT or not c.get("splits"):
            continue
        parent = c["splits"]
        size = _group_size(graph, parent)
        if size is None:
            findings.append(Finding(
                R_FAMILY, "%s:%s" % (R_FAMILY, cid), UNSOUND_PREMISE, cid,
                "COUNT claim %s splits %r, which is neither a family nor a "
                "group declared by another disposition." % (cid, parent),
                "Name the family, or the group id from the split that produced "
                "this subset.", semantic_key=cid))
            continue
        total = sum(g["settles"] for g in c["groups"])
        if total != size:
            findings.append(Finding(
                R_FAMILY, "%s:%s" % (R_FAMILY, cid), UNSOUND_PREMISE, cid,
                "COUNT claim %s splits %s, which covers %d members, into "
                "groups totalling %d: %s."
                % (cid, parent, size, total,
                   " + ".join("%s %d" % (g["id"], g["settles"])
                              for g in c["groups"]))
                + "\n  A member unaccounted for is a member no verdict was "
                  "reached about, and a member counted twice is a verdict "
                  "reached twice about one object.",
                "Make the groups total %d, or declare the remainder as its own "
                "group with an honest verdict -- `unsettled` is a verdict and "
                "an empty residue is not the same as a covered one." % size,
                semantic_key=cid))
    return findings


def check_evidence_direction(graph):
    """A CLAIM RESTING ON THE VERDICT ITS METHOD DOES NOT PROVE.

    THE RULE I WAS LEAST SURE EARNED ITS REQUIRED FIELD, kept because a live
    census produced its evidence without being asked.  Its triage settled 1220
    classes as "not generically finite-to-one" using full Jacobian rank at a
    sampled point -- a method that proves the POSITIVE verdict, since a nonzero
    minor at one point is a nonzero polynomial, and gives only evidence for the
    negative.  The author knew: the report says deficiency "is only evidence,
    so the max over several points is taken", and the 1220 was split into 852
    forced by parameter counting and 368 resting on sampling.

    That split is the finding.  It exists because the author felt the
    difference and had nowhere to put it, so it survived as two numbers in a
    table and one number in the headline.

    A claim naming `rests_on: <group>` uses that group's verdict.  Whether the
    verdict is established is a property of the METHOD, not of the author's
    confidence, which is why the direction is declared per disposition and
    checked here rather than graded per claim.
    """
    findings = []
    for cid in sorted(graph.claims):
        c = graph.claims[cid]
        gid = c.get("rests_on")
        if not gid or gid not in graph.groups:
            continue
        g = graph.groups[gid]
        # The disposition NAMED which of its own groups its method establishes.
        # Everything it did not name is evidence -- including, routinely, the
        # other side of the same computation.
        if g["proved"]:
            continue
        findings.append(Finding(
            R_DIRECTION, "%s:%s" % (R_DIRECTION, cid), UNSOUND_PREMISE, cid,
            "claim %s rests on group %s, whose verdict %r is EVIDENCE and not "
            "proof.\n  The method was %r, and %s does not list %s among the "
            "groups it proves.\n  %s"
            % (cid, gid, g["verdict"], g["method"], g["by"], gid, g["why"]),
            "Either establish this group by a method that proves its verdict, "
            "or restate the claim as what the evidence supports. A method that "
            "screens is not a method that decides, and the difference is "
            "invisible once both are counts in the same table.",
            semantic_key="%s|%s" % (cid, gid)))
    return findings


def check_crosscuts(graph):
    """A RESULT PROVED OVER ONE DECOMPOSITION, COUNTED IN ANOTHER.

    THE BEST-EVIDENCED RULE HERE, because the error is real, was caught by
    hand, and is recorded with its correction.  A live project's class of nine
    carries two decompositions of the same nine rows -- by status (2 settled, 7
    open) and by invariant (8 sharing (a,b,t), 1 not).  A transfer result
    proved for the 8 was read as buying 8 open rows.  Both settled rows are
    (2,3,4) rows, so it buys SIX:

        "So the 'transfers to eight of the nine' result buys 6 genuinely open
        rows, not 8 -- the other two are already-settled and serve as controls."

    Nothing about that is exotic.  Two true statements about one family, and
    the product of two counts is not the count of the intersection.

    AND IT IS COMPUTABLE ONLY FROM NAMES.  This is what decides `exhibited`
    against a bare count, and it decides it honestly in both directions: at 34
    rows you list members and the intersection is arithmetic; at 1567 you do
    not, and then the claim is refused rather than guessed.  Silently allowing
    it because the check is unavailable is precisely how "8 of 9" became "8
    open rows".
    """
    findings = []
    for cid in sorted(graph.claims):
        c = graph.claims[cid]
        a_id, b_id = c.get("rests_on"), c.get("counts_against")
        if not a_id or not b_id:
            continue
        if a_id not in graph.groups or b_id not in graph.groups:
            continue
        a, b = graph.groups[a_id], graph.groups[b_id]
        asserted = c.get("asserts_count")
        if not a["exhibited"] or not b["exhibited"]:
            findings.append(Finding(
                R_CROSSCUT, "%s:%s" % (R_CROSSCUT, cid), UNSOUND_PREMISE, cid,
                "claim %s counts group %s against group %s, and the members of "
                "%s are not named."
                % (cid, a_id, b_id,
                   a_id if not a["exhibited"] else b_id)
                + "\n  Two decompositions of one family cannot be intersected "
                  "from their sizes. |A| = %d and |B| = %d bound |A and B| "
                  "only between %d and %d."
                  % (a["settles"], b["settles"],
                     max(0, a["settles"] + b["settles"]
                         - (_group_size(graph, a["of"]) or 0)),
                     min(a["settles"], b["settles"])),
                "Name the members of both groups with `exhibited`, or drop the "
                "cross-count and state the result over the decomposition it "
                "was actually proved in.",
                semantic_key="%s|%s|%s" % (cid, a_id, b_id)))
            continue
        overlap = sorted(set(a["exhibited"]) & set(b["exhibited"]))
        if asserted is not None and asserted != len(overlap):
            findings.append(Finding(
                R_CROSSCUT, "%s:%s" % (R_CROSSCUT, cid), UNSOUND_CONCLUSION,
                cid,
                "claim %s asserts %d, and %s intersected with %s is %d: %s."
                % (cid, asserted, a_id, b_id, len(overlap),
                   ", ".join(overlap) or "no members")
                # SAY BOTH NUMBERS, and say which is which.
                #
                # This printed `a.settles - len(overlap)` and called it "already
                # in B" -- the count of members OUTSIDE B, described as being
                # inside it. On the docstring's own worked example it announced
                # 6 members "already in" when 6 is exactly the count that is
                # NOT, and a live campaign caught it printing 2 where the
                # answer was 1.
                #
                # The number was right and the sentence inverted its meaning,
                # in the one message whose entire purpose is to correct a
                # double-count. A finding that miscounts while explaining a
                # miscount teaches the reader to distrust the rule, which is
                # worse than silence.
                + "\n  %d of %s's %d member(s) lie in %s (%s); the other %d do "
                  "not. A count over one decomposition is not a count in "
                  "another."
                  % (len(overlap), a_id, a["settles"], b_id,
                     ", ".join(overlap) or "none",
                     a["settles"] - len(overlap)),
                "State the intersection, %d, or say plainly which of the two "
                "numbers the result is about. A count over one decomposition "
                "is not a count in another." % len(overlap),
                semantic_key="%s|%s|%s" % (cid, a_id, b_id)))
    return findings


def _legs(graph, cid):
    """Every (inference, path) that carries claim `cid`.

    PREMISES ONLY, and never `claim`/`path`.  The store normalises a
    single-claim inference into a one-element `premises` list AND KEEPS the
    original fields, so reading both counts every such inference twice --
    which the first version of this helper did, reporting the hyperbola
    finding two identical times.

    Reading `claim`/`path` INSTEAD is the opposite bug and already cost a live
    campaign: they are backfilled from `premises[0]` only, so any claim in slot
    2 or later goes invisible, and that campaign had all three of its
    structured identities in slots 2 to 4.  `check_identity` carries the
    comment; this helper now carries the code, so there is one place to get it
    right.
    """
    legs = []
    for iid in sorted(graph.inferences):
        inf = graph.inferences[iid]
        if inf.get("superseded_by"):
            continue
        for pr in inf.get("premises") or []:
            if pr.get("claim") == cid:
                legs.append((iid, pr.get("path") or []))
    return legs


def check_inexpressible(graph):
    """An IDENTITY transported into a ring that does not have its symbols.

    THE GATE `IMAGE_CLOSURE/ALONG/IDENTITY` ACTUALLY NEEDS, and the one nothing
    asked for.  That cell was licensed on density -- "the image is dense in its
    closure, so a relation vanishing on the image vanishes on the closure" --
    which is the wrong argument twice: a set is dense in its own closure by
    definition, so the map earned nothing; and the conclusion is about POINTS
    while an IDENTITY here is membership in an ideal, which `verify.identity`
    decides by reduction.  The two agree only for radical ideals and an
    elimination ideal need not be one.

    The honest argument is the elimination theorem -- I(dst) = I(src) cap
    k[remaining] -- and what it requires is that the rewriting BE A SENTENCE IN
    THE TARGET RING.  `x*y = 1` is true on the hyperbola xy = 1, and after
    eliminating y the target ring is k[x], where it is not a false claim: it is
    not a claim.  The tool licensed it and `gp check` exited 0.

    SAME SHAPE AS `coefficients_in_base`, which is why this is worth saying
    twice.  Both gates exist only because a claim is a STRING and a string
    carries no evidence about which ring it lives in; state the theorem with
    `f g : R` and both conditions vanish into the type, which is exactly why
    the formalisation could not see either one.

    TWO TIERS, because sometimes the graph KNOWS and sometimes this is a guess.

      UNSOUND_CONCLUSION  the target records the symbol in `eliminated`. Not an
                          inference from names: the graph says that variable was
                          projected away.
      TRIAGE              the target declares `ring_vars` without the symbol.
                          Syntactic and conservative -- the name might denote a
                          constant -- so it reports.
    """
    findings = []
    for cid in sorted(graph.claims):
        c = graph.claims[cid]
        if c.get("kind") != K.IDENTITY or c.get("superseded_by"):
            continue
        if c.get("lhs") is None:
            continue
        dead = withdrawn_edges(graph)
        for iid, path in _legs(graph, cid):
            for step in path:
                eid = step[0] if isinstance(step, (list, tuple)) else step
                direction = (step[1] if isinstance(step, (list, tuple))
                             and len(step) > 1 else None)
                e = graph.edges.get(eid)
                if not e or eid in dead:
                    continue
                # WHERE THE CLAIM LANDS.  ALONG runs src -> dst, AGAINST runs
                # dst -> src, and only the landing ring can be too small.
                lands = e.get("dst") if direction == K.ALONG else e.get("src")
                target = graph.models.get(lands) or {}
                ring = target.get("ring_vars")
                if not ring:
                    continue
                missing = cas_foreign_symbols(ring, c["lhs"], c["rhs"])
                if not missing:
                    continue
                gone = [s for s in missing
                        if s in set(target.get("eliminated") or [])]
                findings.append(Finding(
                    R_INEXPRESSIBLE, "%s:%s:%s" % (R_INEXPRESSIBLE, cid, eid),
                    UNSOUND_CONCLUSION if gone else TRIAGE, cid,
                    "inference %s carries IDENTITY %s across %s to %s, whose "
                    "ring is k[%s] -- and the rewriting names %s.\n"
                    "  %s"
                    % (iid, cid, eid, lands, ", ".join(ring),
                       ", ".join("`%s`" % s for s in missing),
                       ("%s was ELIMINATED to build %s, so this is not a guess "
                        "from names. The transported statement is not a false "
                        "claim at %s -- it is not a claim there, and every "
                        "cell downstream of it is reasoning about a sentence "
                        "that does not parse in its own ring."
                        % (", ".join("`%s`" % s for s in gone), lands, lands))
                       if gone else
                       ("The check is syntactic and cannot know whether those "
                        "names denote constants rather than variables, so this "
                        "reports rather than refuses. If they are variables, "
                        "the conclusion is not expressible at %s." % lands)),
                    ("Restate the rewriting in the target's variables, or "
                     "keep the claim at its own model and transport something "
                     "that survives the projection. Eliminating a variable "
                     "does not make a statement about it into a statement "
                     "about what is left.") if gone else
                    ("If those names are constants of the base, say so in a "
                     "caveat and carry this. If they are variables, the claim "
                     "belongs at its own model only."),
                    semantic_key="%s:%s" % (cid, eid)))
    return findings


def check_pending_ideals(graph):
    """Models whose ideal is a computation nobody has run yet.

    THE POINT IS TO SAY IT BEFORE THE SOLVER DOES.  `saturate_closure` and
    `eliminate` mint a model whose ideal only the CAS knows, and both used to
    fill `generators` with a placeholder string.  Nothing objected: CONTAINMENT
    reported that "both models carry ideals, so the containment is CHECKABLE",
    which was false, and its DISCHARGE sent the author to `gp verify`, which
    passed `<saturation of M at f>` to Singular and returned `expected
    ideal-expression`.  Two layers agreed the graph was fine and the third
    failed to parse.

    A pending ideal is not a defect and this is not an accusation -- it is the
    normal state of a model between being constructed and being computed.  What
    it IS is a blocker: every reduction at that model, and every containment
    across an edge touching it, is unanswerable until the program runs.  Saying
    so costs one finding and replaces a Singular parse error.
    """
    findings = []
    for mid in sorted(graph.models):
        m = graph.models[mid]
        if not m.get("ideal_pending") or m.get("superseded_by"):
            continue
        claims = sorted(c for c in graph.claims
                        if graph.claims[c].get("model") == mid
                        and not graph.claims[c].get("superseded_by"))
        edges = sorted(e for e in graph.edges
                       if mid in (graph.edges[e].get("src"),
                                  graph.edges[e].get("dst"))
                       and not graph.edges[e].get("superseded_by"))
        blocked = (("%d claim(s) and %d edge(s) rest on it: %s."
                    % (len(claims), len(edges),
                       ", ".join(claims + edges)))
                   if (claims or edges) else
                   "Nothing rests on it yet.")
        findings.append(Finding(
            R_PENDING_IDEAL, "%s:%s" % (R_PENDING_IDEAL, mid), DEBT, mid,
            "model %s does not carry an ideal yet -- it is waiting on %s."
            % (mid, m["ideal_pending"])
            + "\n  " + blocked + " No reduction at this model can be "
              "answered until the computation runs, so `gp verify` will "
              "return UNVERIFIED for all of them. This is a normal state for "
              "a constructed model, not an error; it is reported so it does "
              "not read as a solver failure later.",
            "Run `gp construct ... --run --declare` to execute the operation "
            "and record its generators, or supersede this pending model with "
            "a RELICENSE that replaces `ideal_pending`. The two "
            "cannot be declared together -- an ideal is either known or "
            "waiting -- so the relicensing is what moves the model from one state "
            "to the other.",
            semantic_key=mid))
    return findings


def _effective_containment(graph, eid):
    """Containment verdict plus provenance when the exact question survives."""
    edge = graph.edges[eid]
    if K.is_mapped_equivalence(edge):
        return None, None, None
    if edge.get("containment"):
        return edge["containment"], edge.get("containment_why"), None
    current, seen = edge, set()
    while current.get("supersedes"):
        old_id = current["supersedes"]
        if old_id in seen:
            break
        seen.add(old_id)
        old = graph.edges.get(old_id)
        if not old:
            break
        if (current.get("type") == K.SPECIALIZATION
                or K.is_mapped_equivalence(current)
                or old.get("type") == K.SPECIALIZATION
                or K.is_mapped_equivalence(old)
                or old.get("src") != edge.get("src")
                or old.get("dst") != edge.get("dst")):
            break
        if old.get("containment"):
            return (old["containment"], old.get("containment_why"), old_id)
        current = old
    return None, None, None


def check_containment(graph):
    """Check literal inclusion edges, without conflating mapped equivalence.

    Inclusion-style edges assert `V(src) subset V(dst)`. A mapped EQUIVALENCE
    instead asserts that its forward substitution sends source points to target
    points and its inverse sends them back. Lean/MappedEquivalence proves that
    neither literal inclusion follows from that relation, so those edges are
    handled by `verify.ring_iso` and skipped here.

    Literal containment was never verified, only declared -- the SIXTH instance
    of the pattern
    this project keeps finding, at the deepest level available: a field that
    DETERMINES transport and is taken on the author's word.

    A live lane stated the cost precisely.  A flop is an isomorphism in
    codimension one, so neither variety contains the other; typed EQUIVALENCE
    it "yields a false conclusion reported clean behind one prose-dischargeable
    DEBT", and "nothing in the tool would have stopped me if I had not done the
    mathematics first".  RESTRICTION, the newest and most inviting type,
    "matches a flop on every clause except the one that matters".

    IT IS CHECKABLE NOW, for the first time, because models can carry their
    ideals: `I(dst) subset I(src)` implies `V(src) subset V(dst)`, and testing
    it is one reduction per generator -- exactly what `cas.classify_identity`
    already does.

    THIS RULE DOES NOT RUN IT.  The checker is deterministic with no solver and
    no network, and that is worth more than the convenience.  So the split is:
    this reports the HOLE, and `gp verify` fills it by spending CAS time and
    recording the answer on the edge.  An unverified containment is a debt you
    can see; a refuted one is an unsound premise.

    Silent where the data is absent, deliberately.  Every model in the corpus
    predates `generators`, and a rule that fired on all of them would be a
    false-positive generator on day one.
    """
    findings = []
    dead = withdrawn_edges(graph)
    for eid in sorted(graph.edges):
        if eid in dead:
            continue
        e = graph.edges[eid]
        if any((graph.models.get(e.get(end)) or {}).get("superseded_by")
               for end in ("src", "dst")):
            continue
        src, dst = graph.models.get(e["src"]), graph.models.get(e["dst"])
        if not src or not dst:
            continue
        # A mapped equivalence asserts dst(forward(x)) for src(x), and the
        # inverse statement in the other direction.  It does NOT assert that
        # V(src) is a literal subset of V(dst) in the coordinates as written.
        # `verify.ring_iso` checks the former; asking containment as well is a
        # different, generally false question (MappedEquivalence.lean).
        if K.is_mapped_equivalence(e):
            continue
        # A PENDING IDEAL IS NOT AN IDEAL, and the sentence below says "both
        # models carry ideals".  Saying it about a model still waiting on a
        # saturation was a false statement about the graph, and its DISCHARGE
        # sent the author to `gp verify` to reduce modulo something that does
        # not exist yet.  `pending_ideals` reports that state on its own terms.
        if src.get("ideal_pending") or dst.get("ideal_pending"):
            continue
        if src.get("generators") is None or dst.get("generators") is None:
            continue
        # THIS RULE MUST KEY ON WHAT ITS OWN VERIFIER KEYS ON.
        #
        # It tested "do both models carry ideals?" and promised `gp verify`
        # would reduce one modulo the other. `verify.containment` also requires
        # THE SAME RING, and declines when the rings differ -- correctly: an
        # ideal containment between two different polynomial rings is not a
        # reduction question.
        #
        # So on every IMAGE_CLOSURE edge, where the rings differ BY
        # CONSTRUCTION because the edge is a projection, the checker raised a
        # DEBT that was UNDISCHARGEABLE BY ITS OWN STATED REMEDY: run the named
        # command, nothing clears, re-run `gp check`, see it again verbatim.
        # A live session hit this and had no route but `gp accept`.
        #
        # Not a soundness problem -- declining is the safe direction -- but a
        # finding whose discharge cannot be delivered is worse than no finding,
        # because it spends the author's trust in every other discharge.
        #
        # What IS checkable across a projection is `operation_output`, and the
        # session's own edge carried a VERIFIED one.
        if (src.get("ring_vars") or []) != (dst.get("ring_vars") or []):
            continue
        verdict, containment_why, inherited_from = _effective_containment(graph, eid)
        if verdict == "VERIFIED":
            continue
        if verdict == "NOT_BY_IDEAL":
            ridden = live_crossings(graph, [eid])
            untyped_unridden = e["type"] == K.UNTYPED and not ridden
            findings.append(Finding(
                R_CONTAINMENT, "%s:%s" % (R_CONTAINMENT, eid),
                DEBT if untyped_unridden else UNSOUND_PREMISE, eid,
                "edge %s asserts V(%s) subset V(%s) and the SUFFICIENT test for "
                "it FAILED: %s"
                % (eid, e["src"], e["dst"],
                   containment_why or "(no reduction recorded)")
                + (("\n  This verdict was computed for %s and applies here "
                    "because the source and destination model ids are identical."
                    % inherited_from) if inherited_from else "")
                + ("\n  This edge is UNTYPED and carries no live inference, so "
                   "it licenses no cell: the failed sufficient test is an open "
                   "modelling debt, not yet an unsound premise. The containment "
                   "is UNESTABLISHED, not refuted; it can still hold through "
                   "the radical."
                   if untyped_unridden else
                   "\n  Every cell this edge licenses rests on that containment, "
                   "and it is now UNESTABLISHED rather than merely unexamined. "
                   "It is NOT refuted: reduction tests plain ideal membership "
                   "and the containment can still hold through the radical."),
                "Establish it another way and record how -- a radical-membership "
                "computation is the direct one. Or refute it properly with a "
                "POINT of the source outside the target. If the two models are "
                "related and neither contains the other, draw a SPAN and type "
                "each leg separately. If this declaration was never an edge, "
                "withdraw it with an edge tombstone: `supersedes: %s`, "
                "`discharge_kind: WITHDRAW`, and `why`."
                % eid,
                semantic_key=eid))
            continue
        findings.append(Finding(
            R_CONTAINMENT, "%s:%s" % (R_CONTAINMENT, eid), DEBT, eid,
            "edge %s asserts V(%s) subset V(%s) and both models carry ideals, "
            "so the containment is CHECKABLE and unchecked."
            % (eid, e["src"], e["dst"])
            + "\n  This is the assertion every cell on this edge rests on, "
              "and it is currently the author's word.",
            "Run `gp verify` to reduce each generator of %s's ideal modulo "
            "%s's. It is one reduction per generator and it either confirms the "
            "containment or refutes the edge." % (e["dst"], e["src"]),
            semantic_key=eid))
    return findings


def check_coefficients_in_base(graph):
    """A claim declaring `coefficients_in_base` whose own rewriting names a
    symbol the ring does not have.

    `coefficients_in_base` gates DESCENT across a BASE_EXTENSION, and it was
    declared and never checked. A shadow formalisation showed why it had
    resisted: descent does not fail because reflection fails -- for a field
    extension that holds automatically -- it fails because the claim cannot be
    WRITTEN in the smaller ring. In a typed setting that condition disappears
    into the type, which is why the formal version could not see the gate at
    all.

    So the gate is a TYPING ARTIFACT: it exists because a claim is a string,
    and a string carries no evidence about which ring it lives in. Which makes
    it decidable. The kernel's own counterexample is caught by looking:
    `x^2 + 1 = (x + i)(x - i)` names `i`, and `i` is not a ring variable.

    Syntactic and conservative, so it REPORTS rather than refuses -- `sqrt2`
    might have been defined as an element of the base, and this cannot know.
    But a declaration that contradicts the text of its own claim is worth
    saying out loud.
    """
    findings = []
    for cid in sorted(graph.claims):
        c = graph.claims[cid]
        if not c.get("coefficients_in_base") or c.get("superseded_by"):
            continue
        if c.get("lhs") is None:
            continue
        foreign = cas_foreign_symbols(c.get("ring_vars") or [],
                                      c["lhs"], c["rhs"])
        if not foreign:
            continue
        findings.append(Finding(
            R_BASE_COEFFS, "%s:%s" % (R_BASE_COEFFS, cid), TRIAGE, cid,
            "claim %s declares `coefficients_in_base`, and its rewriting names "
            "%s -- which the model's ring does not have.\n"
            "  That flag is what licenses DESCENT across a BASE_EXTENSION, and "
            "the reason it exists is this exact shape: `x^2 + 1 = (x + i)"
            "(x - i)` is valid over Q(i) and, descended to Q, `i` is not "
            "unproved -- it is not expressible. The descended statement is not "
            "a false claim, it is not a claim."
            % (cid, ", ".join("`%s`" % s for s in foreign)),
            "If those symbols really do denote elements of the base, say so in "
            "a caveat and carry this -- the check is syntactic and cannot know. "
            "If they do not, the claim belongs at the extension only, and "
            "`coefficients_in_base` should come off.",
            semantic_key=cid))
    return findings


def check_integral(graph):
    """A claim declaring `integral` whose rewriting has the prime downstairs.

    `integral` gates reducing an IDENTITY into characteristic p, and it was
    declared and never computed. The kernel's own instance is
    `d2 = h_2 - (3/8)h_1^2`, which travels a perfectly polynomial map and does
    not reduce mod 2 because 8 = 2^3.

    A shadow formalisation put this in a different class from the other gates.
    `ring_iso` is a property of a map; `identity_origin` is a property of the
    claim; this is neither. Reduction mod p is a PARTIAL map, and `integral`
    asks whether it is defined here at all. Undefined is not false -- with no
    image there is nothing to state, the same shape as `coefficients_in_base`.

    The prime comes from the SPECIALIZATION edge the claim would cross, since
    integrality is only meaningful against one.
    """
    findings = []
    primes = {}
    for eid in sorted(graph.edges):
        e = graph.edges[eid]
        if e.get("type") == K.SPECIALIZATION and e.get("prime"):
            primes[e["src"]] = (eid, e["prime"])
    for cid in sorted(graph.claims):
        c = graph.claims[cid]
        if not c.get("integral") or c.get("superseded_by"):
            continue
        if c.get("lhs") is None or c.get("model") not in primes:
            continue
        eid, p = primes[c["model"]]
        bad = cas_non_integral_denominators(p, c["lhs"], c["rhs"])
        if not bad:
            continue
        findings.append(Finding(
            R_INTEGRAL, "%s:%s" % (R_INTEGRAL, cid), TRIAGE, cid,
            "claim %s declares `integral` and would reduce mod %s across %s, "
            "and its rewriting has %s downstairs.\n"
            "  Reduction mod p is a PARTIAL map -- undefined on a coefficient "
            "with p in its denominator -- so this is not a false claim in "
            "characteristic %s, it is not a claim there at all. The kernel's "
            "own instance is `d2 = h_2 - (3/8)h_1^2`, which does not reduce "
            "mod 2 because 8 = 2^3."
            % (cid, p, eid,
               ", ".join("`%s`" % d for d in bad), p),
            "Clear the denominators and record what that costs, or keep the "
            "rewriting in characteristic 0. If those fractions are not really "
            "coefficients -- the check reads literal fractions and cannot "
            "evaluate -- say so in a caveat and carry it.",
            semantic_key=cid))
    return findings


def check_doubts(graph):
    """Authored defeaters, rendered as findings.

    Every other finding here is computed. This is the one a person writes, and
    it exists because a live session read a cited proposition, found it did not
    supply the premise it was meant to, and had nowhere to put that. It
    correctly refused to draw an UNTYPED edge -- which would assert a map
    exists and is merely unclassified, the opposite of what it found -- so the
    result went into a note, invisible to every rule.

    A doubt enters the SAME lifecycle as a computed finding: `gp accept`
    carries it with a reason, which is exactly ACCEPTED_RISK, and `answered`
    retires it.
    """
    findings = []
    for did in sorted(graph.doubts):
        d = graph.doubts[did]
        # SUPERSEDED, TOO -- and leaving this out made the supersession fix
        # half a fix. A doubt is retired by ANSWERING it, and answering an
        # existing one means sending a new version that carries `answered`,
        # which supersedes the old. If the old keeps firing, the loop still
        # does not close and the graph still reports as live debt something
        # that has been settled.
        if d.get("answered") or d.get("superseded_by"):
            continue
        findings.append(Finding(
            R_DOUBT, "%s:%s" % (R_DOUBT, did), d["severity"], d["about"],
            "%s, raised against %s by hand.\n  %s"
            % (d["kind"], d["about"], d.get("why")),
            d.get("discharge_hint")
            or ("Answer it and record `answered` with what settled it, accept "
                "it deliberately with `gp accept`, or act on it. A doubt "
                "nobody has answered is the honest state and stays visible "
                "until one of those happens."),
            semantic_key=did))
    return findings


def check_evidence(graph):
    """A computation recorded for a claim that says it was never run.

    The `evidence` record names WHAT was run, which `established_by: RAN` does
    not -- it records only that something was. So the two must agree: a claim
    graded CITED or READ with a computation attached to it is one of the two
    being wrong, and which one matters. This is the seam where, in the
    reporting session's own words, "a citation would drift into a
    verification".
    """
    findings = []
    for vid in sorted(graph.evidence):
        v = graph.evidence[vid]
        if v.get("superseded_by"):
            continue
        # AN ENUMERATION THAT DOES NOT SAY WHICH VERDICT IT DECIDES.
        #
        # A live session called this the single most important epistemic fact
        # about its run: its filter kept more branches alive at every choice
        # point, so a kill was definitive and a survival meant only that this
        # filter had not killed it. Without the field, a reader takes the
        # survivor count at face value and reads an upper bound as an answer.
        #
        # Reported rather than required, because the census is sealed and two
        # evidence records already exist without it. Same policy as `lhs`.
        if v["method"] == "ENUMERATION" and not v.get("decides"):
            findings.append(Finding(
                R_EVIDENCE, "%s:decides:%s" % (R_EVIDENCE, vid), TRIAGE, vid,
                "evidence %s is an ENUMERATION and does not say which verdict "
                "it decides.\n"
                "  A filter that keeps too much decides its EXCLUSIONS: a "
                "removal is definitive and a survival means only that this "
                "sweep did not remove it. A filter that discards too much "
                "decides the opposite. Which one it is cannot be read off the "
                "count, and the count is what gets reused."
                % vid,
                "Declare `decides`: EXCLUSIONS, INCLUSIONS, or BOTH. If the "
                "sweep is exact -- it removes everything it should and nothing "
                "it should not -- that is BOTH, and worth saying because it is "
                "the rarer case.",
                semantic_key=vid))
        c = graph.claims.get(v["for"]) or {}
        by = c.get("established_by")
        if by in (None, "RAN"):
            continue
        # ONLY AN ENUMERATION IMPLIES A GRADE, and firing on both methods made
        # this rule undischargeable.
        #
        # A live session attached a REPLICATION to a READ claim -- its code
        # reproduced a table the source PRINTS -- which is coherent and is what
        # replication is for. The rule fired anyway, and its advice ("say so in
        # the evidence's `what`") named a move the rule does not read, so the
        # only clearing move was regrading to RAN, which would have been false.
        # A finding whose stated discharge cannot discharge it teaches people
        # to accept findings rather than answer them.
        #
        # The distinction: an ENUMERATION ESTABLISHES the claim, so the grade
        # must say a run happened. A REPLICATION CORROBORATES a claim
        # established some other way, and corroborating something you read is
        # exactly the normal case.
        if v["method"] != "ENUMERATION":
            continue
        findings.append(Finding(
            R_EVIDENCE, "%s:%s" % (R_EVIDENCE, vid), TRIAGE, v["for"],
            "evidence %s records a %s computation (%s) for claim %s, but that "
            "claim is graded `established_by: %s`.\n"
            "  A computation was run and the claim says it was not. One of "
            "the two is wrong, and the direction matters: upgrading the grade "
            "on the strength of an attached script is exactly how a citation "
            "drifts into a verification."
            % (vid, v["method"], v["ran"], v["for"], by),
            "If the computation established the claim, regrade it RAN. That "
            "is an AMEND, not a RELICENSE -- evidence grading licenses "
            "nothing, which is the whole point of keeping it on a separate "
            "axis from transport. (This advice used to say RELICENSE, which "
            "contradicted the field list and was caught by a session that "
            "regraded under AMEND and was silently accepted.) If the "
            "computation only CORROBORATES something "
            "read or cited, say so in the evidence's `what`, and leave the "
            "grade where it is.",
            semantic_key=v["for"]))
    return findings


def check_citations(graph):
    """Something cites an identifier already recorded as denoting elsewhere.

    THE POINT OF TYPING A CITATION AT ALL.  Storing the resolution is worth
    little if the next person has to know to look it up; what earns it is
    firing when somebody cites the ambiguous name again.

    A live session established that a paper's "GGV1 Remark 7.10" denotes what
    the arXiv source numbers 7.14 -- the citing work used a pre-publication
    draft -- and that arXiv 7.10 is a DIFFERENT statement about the same
    subject. So the naive resolution does not fail loudly; it succeeds on the
    wrong object. That is this project's trap number one and it had no type.

    Substring matching, deliberately.  It fires only where a `hazard` was
    recorded by hand, so the false-positive surface is exactly as large as
    somebody chose to make it, and a citation with no hazard is silent.
    """
    findings = []
    hazards = [(c["cites"], c) for c in graph.citations.values()
               if c.get("hazard") and not c.get("superseded_by")]
    # A HAZARD NOTHING CAN TRIP.
    #
    # This rule substring-matches a citation's `cites` against claim and
    # inference text. A live session recorded a real hazard whose ambiguous
    # identifiers live in PYTHON DOCSTRINGS the graph points at but does not
    # contain -- so the record was correct, useful to a human, and mechanically
    # inert, and the session learned that only by reading this function.
    #
    # The checker cannot read files: it is deterministic and spawns nothing.
    # What it can do is stop the record looking more active than it is.
    for cites, c in hazards:
        text = " ".join(str(o.get(f) or "")
                        for o in list(graph.claims.values())
                        + list(graph.inferences.values())
                        for f in ("cite", "statement", "asserted"))
        if cites in text:
            continue
        findings.append(Finding(
            R_CITATION, "%s:dormant:%s" % (R_CITATION, c["id"]), DEBT,
            c["id"],
            "citation %s records a hazard about %r, and nothing in this graph "
            "cites that string, so the hazard will never fire.\n"
            "  It is not wrong -- a reader still gets it from `gp show` -- but "
            "it is doing less than a recorded hazard looks like it is doing. "
            "This checker reads the graph and no files, so an identifier that "
            "appears only in a script or a document it points at is out of "
            "reach by construction."
            % (c["id"], cites),
            "If something here really does depend on that reference, put the "
            "identifier in the claim's `cite` or `statement` where the match "
            "can see it. If the ambiguity lives entirely outside the graph, "
            "leave this as documentation and accept the finding.",
            semantic_key=c["id"]))
    if not hazards:
        return findings
    subjects = [("claim", cid, graph.claims[cid]) for cid in sorted(graph.claims)]
    subjects += [("inference", iid, graph.inferences[iid])
                 for iid in sorted(graph.inferences)]
    for kind, oid, obj in subjects:
        if obj.get("superseded_by"):
            continue
        text = " ".join(str(obj.get(f) or "")
                        for f in ("cite", "statement", "asserted"))
        for cites, c in hazards:
            if cites not in text or obj.get("citation") == c["id"]:
                continue
            findings.append(Finding(
                R_CITATION, "%s:%s:%s" % (R_CITATION, oid, c["id"]),
                TRIAGE, oid,
                "%s %s cites %r, and %s records that identifier as denoting "
                "%s.\n"
                "  %s\n"
                "  HAZARD: %s"
                % (kind, oid, cites, c["id"], c["resolves_to"],
                   c.get("why"), c["hazard"]),
                "If this %s means the object the citation resolves to, link it "
                "with `citation: %s` and the finding goes quiet. If it means "
                "the identifier's OTHER reading, say which -- because the "
                "whole reason this is recorded is that resolving it naively "
                "succeeds on the wrong object rather than failing."
                % (kind, c["id"]),
                semantic_key=oid))
    return findings


def check_stale_references(graph):
    """A live record still naming one that has been superseded.

    SUPERSESSION REPOINTS NOTHING, and until now only two of the places that
    matters had a rule. STALE-PREMISE catches an inference whose premise moved;
    STALE-MODEL catches a claim or edge whose model moved. Everything else
    pointed at corpses in silence.

    A live session hit the worst version. It superseded a claim to fix a wrong
    coordinate, and the PARTITION whose `exhaustive` named that claim became
    quietly unsatisfiable -- the coverage rule went on demanding an id that no
    longer answered, while the session passed the live successor and was
    refused with "the exhaustiveness claim is not among the premises". Nothing
    warned at declare time and nothing warned in `check`; it found the cause by
    going looking. In the same graph an `evidence` record still named a
    superseded claim and nothing noticed at all.

    A partition whose covering claim is superseded is not merely stale: it is
    UNSATISFIABLE, because the only id that would satisfy it is retired.
    """
    findings = []
    def dead(oid):
        for reg in (graph.claims, graph.inferences, graph.edges,
                    graph.models, graph.evidence, graph.doubts,
                    graph.citations):
            r = reg.get(oid)
            if r is not None:
                return r.get("superseded_by")
        return None

    refs = []
    for pid, p in sorted(graph.partitions.items()):
        refs.append(("partition", pid, "exhaustive", p.get("exhaustive"),
                     "the coverage rule demands this exact id, so the "
                     "partition cannot be satisfied at all while it names a "
                     "retired one"))
    for vid, v in sorted(graph.evidence.items()):
        if not v.get("superseded_by"):
            refs.append(("evidence", vid, "for", v.get("for"),
                         "this records a computation standing behind a claim "
                         "that has been replaced"))
    for did, d in sorted(graph.doubts.items()):
        if not d.get("superseded_by") and not d.get("answered"):
            refs.append(("doubt", did, "about", d.get("about"),
                         "this doubt is aimed at a record that has moved, so "
                         "it may already be answered or may no longer apply"))

    for kind, oid, field, target, why in refs:
        if not target:
            continue
        successor = dead(target)
        if not successor:
            continue
        findings.append(Finding(
            R_STALE_REF, "%s:%s" % (R_STALE_REF, oid), TRIAGE, oid,
            "%s %s names %s in `%s`, and %s was superseded by %s.\n  %s"
            % (kind, oid, target, field, target, S.successors(
                graph.claims.get(target) or graph.inferences.get(target)
                or graph.edges.get(target) or graph.models.get(target)
                or graph.evidence.get(target) or graph.doubts.get(target)
                or graph.citations.get(target) or {}), why),
            "Supersede %s with the reference repointed at %s. Supersession "
            "does not repoint anything on its own, deliberately -- a record "
            "silently re-aimed at a successor it was never checked against is "
            "the failure this refuses to automate."
            % (oid, successor if isinstance(successor, str)
               else ", ".join(successor)),
            semantic_key=oid))
    return findings


def check_stale_models(graph):
    """Claims and edges still anchored to a model that has been superseded.

    THE ANCHOR IS THE WORST THING TO BE ABLE TO MOVE INVISIBLY.  Models had no
    supersession machinery at all -- `supersedes` on one was accepted with no
    existence check, no back-pointer and no discharge kind -- so a live session
    corrected a model, was not refused, and then could not see the change in
    `gp show` or `gp history`. Its claims sat on the old model until it noticed
    by hand.

    That is the same shape as STALE-PREMISE, one level down. A superseded claim
    leaves inferences pointing at a dead record; a superseded model leaves
    every claim AND every edge pointing at one, and the claim is where the
    mathematics lives.
    """
    findings = []
    for cid in sorted(graph.claims):
        c = graph.claims[cid]
        if c.get("superseded_by"):
            continue
        m = graph.models.get(c.get("model"))
        if not m or not m.get("superseded_by"):
            continue
        findings.append(Finding(
            R_STALE_MODEL, "%s:%s" % (R_STALE_MODEL, cid), TRIAGE, cid,
            "claim %s sits at model %s, which was superseded by %s.\n"
            "  The claim is live and its anchor is not. Whatever the new model "
            "changed -- what it IS, its ring, its generators -- this claim was "
            "written against the old reading and nothing has re-examined it."
            % (cid, c.get("model"), S.successors(m)),
            "If the claim still holds at %s, supersede it with the model "
            "field repointed -- that is a RESTATE, because the model is part "
            "of what identifies a claim. If it does not, retract it. If the "
            "model supersession was itself a mistake, supersede the model "
            "back rather than leaving two live readings of one object."
            % S.successors(m),
            semantic_key=cid))
    dead = withdrawn_edges(graph)
    for eid in sorted(graph.edges):
        e = graph.edges[eid]
        if eid in dead:
            continue
        for end in ("src", "dst"):
            m = graph.models.get(e.get(end))
            if not m or not m.get("superseded_by"):
                continue
            findings.append(Finding(
                R_STALE_MODEL, "%s:%s:%s" % (R_STALE_MODEL, eid, end),
                TRIAGE, eid,
                "edge %s has its %s at model %s, which was superseded by %s.\n"
                "  Every cell this edge licenses rests on V(src) subset "
                "V(dst), and one of those two models has been replaced."
                % (eid, end, e.get(end), S.successors(m)),
                "Repoint the edge at %s and declare the supersession, or say "
                "why the old model is still the right endpoint."
                % S.successors(m),
                semantic_key=eid))
            break
    return findings


def check_sibling_edges(graph):
    """An edge between two branches of the same partition.

    THE OTHER HALF OF THE BUG PARTITIONS WERE BUILT TO FIX, and it sat
    unnoticed while the first half had a rule, a docstring and two live
    instances behind it.

    `check_partitions` reasons: branch = parent AND condition, so V(branch)
    subset V(parent), and an edge drawn parent -> branch asserts the reverse --
    consistent only if the parent is empty, which is invariably the thing under
    proof.  Exactly the same argument applies SIDEWAYS and nothing made it:

        A = parent AND c1,  B = parent AND c2,  c1 and c2 exclusive.
        An edge A -> B asserts V(A) subset V(B), i.e. V(A) subset V(A and B)
        = V(empty condition).  Consistent only if V(A) is empty.

    Measured before writing this: a partition with branches A and B, a
    NECESSARY_CONDITION edge from A to B, and an EXHIBITED witness at A
    transporting ALONG it produced ZERO findings and the inference was reported
    CLEAN.  The witness crossed into a branch its own case condition excludes.

    Why nothing caught it: the cells that refuse generically (EMPTY along a
    NECESSARY_CONDITION) hid the shape, because the refusal looked correct and
    came from the transport table rather than from anything knowing about
    partitions.  NONEMPTY along the same edge is licensed, and there the hole
    is visible.

    THE SOURCE BEING EMPTY IS THE ONE HONEST CASE, so the finding says so
    rather than refusing outright -- if V(A) really is empty the edge is
    vacuously fine, and the right move is to record that emptiness as a claim
    where the checker can see it.
    """
    findings = []
    branch_of = {}
    for pid in sorted(graph.partitions):
        for b in graph.partitions[pid].get("branches") or []:
            branch_of.setdefault(b, []).append(pid)
    dead = withdrawn_edges(graph)
    for eid in sorted(graph.edges):
        if eid in dead:
            continue
        e = graph.edges[eid]
        shared = sorted(set(branch_of.get(e.get("src"), []))
                        & set(branch_of.get(e.get("dst"), [])))
        if not shared:
            continue
        pid = shared[0]
        findings.append(Finding(
            R_SIBLING, "%s:%s" % (R_SIBLING, eid), UNSOUND_PREMISE, eid,
            "edge %s runs from %s to %s, and both are branches of partition "
            "%s.\n"
            "  Branches are pieces of the parent under MUTUALLY EXCLUSIVE "
            "conditions, so this edge asserts V(%s) subset V(%s) for two "
            "models whose case conditions cannot both hold. That is "
            "consistent only if V(%s) is EMPTY -- which, in every campaign "
            "that has drawn this, was the thing under proof.\n"
            "  It is the same error a partition exists to prevent, turned "
            "sideways: there the branch was typed as a total containment of "
            "the parent, here as a containment of its sibling."
            % (eid, e.get("src"), e.get("dst"), pid,
               e.get("src"), e.get("dst"), e.get("src")),
            "If %s really is empty, record that as an EMPTY claim -- then the "
            "edge is vacuous and nothing needs to cross it. If it is not "
            "empty, this is not an edge: the two branches are related through "
            "their PARENT, so route the argument branch -> parent -> branch "
            "and let each leg be typed on its own. If the conclusion needs "
            "every branch, that is what the partition's exhaustiveness claim "
            "is for." % e.get("src"),
            semantic_key=eid))
    return findings


def check_identity(graph):
    """Report identities that nothing has put to the one test that decides them.

    THIS IS WHERE A GATE USED TO BE.  RESTRICTION/ALONG/IDENTITY was licensed
    only on a declared `zariski_dense`, and that declaration turned out to be
    both insufficient (the nodal cubic satisfies it and breaks the conclusion)
    and beside the point (a restriction shares its ideal, so the identity was
    never in question).  Removing it was right, but a free gate that checked
    nothing still made people stop, and losing the stop is a real regression
    even when losing the gate is not.

    So the hesitation moves here, and it moves to somewhere it can be settled:
    an IDENTITY is `lhs - rhs` in I, reduction modulo a Groebner basis DECIDES
    that, and `gp verify` will run it.  This rule reports; it spawns nothing.

    TWO TIERS, because the two failures are not the same failure.

      REFUTED       a verdict is recorded and it is negative.  The rewriting is
                    false at its OWN model, so everything downstream of it is
                    unsound -- not merely unsupported.
      UNTESTED      the claim crosses the cell the gate used to guard and has
                    never been reduced.  Triage: nothing is known to be wrong.

    The UNTESTED tier is deliberately NARROW -- RESTRICTION, ALONG, IDENTITY,
    and nothing else -- because it is replacing one specific stop and not
    inventing a general campaign to structure every identity in the corpus.
    """
    findings = []
    dead = withdrawn_edges(graph)
    for cid in sorted(graph.claims):
        c = graph.claims[cid]
        if c.get("kind") != K.IDENTITY:
            continue
        if c.get("identity_verdict") == "REFUTED":
            findings.append(Finding(
                R_IDENTITY, "%s:%s" % (R_IDENTITY, cid),
                UNSOUND_CONCLUSION, cid,
                "claim %s was reduced and DOES NOT HOLD at %s: %s"
                % (cid, c.get("model"), c.get("identity_why") or "(no detail)")
                + "\n  This is a refutation and not a failed cheap test. An "
                  "IDENTITY asserts that lhs - rhs lies in the ideal, and "
                  "reduction modulo a Groebner basis decides ideal membership. "
                  "So the rewriting is false where it was claimed, and every "
                  "transport that carried it carried something untrue.",
                "Fix the rewriting or withdraw the claim. Transport typing "
                "cannot help here: no route is sound from a false premise, and "
                "the error is at the origin rather than on any edge.",
                semantic_key=cid))
            continue
        if c.get("identity_verdict"):
            continue
        if c.get("lhs") is not None:
            # STRUCTURED AND NEVER REDUCED, which the first version of this
            # rule fell silent on.  It skipped any claim carrying `lhs`, so
            # recording the rewriting made the checker QUIETER -- and with no
            # way to record a verdict either, the phase-3 loop had no terminus:
            # you could structure a claim, not verify it, and never hear about
            # it again.  Structuring must not be how a claim goes dark.
            # "ONE SOLVER CALL AWAY" IS FALSE IF THE IDEAL IS NOT THERE YET.
            #
            # Same class of wrong sentence as CONTAINMENT's "both models carry
            # ideals": true of the common case, asserted unconditionally, and
            # read by an author who then runs `gp verify` and gets nothing.
            # PENDING-IDEAL already reports the model; this tier just stops
            # promising an answer the graph cannot yet produce.
            waiting = (graph.models.get(c.get("model")) or {}).get(
                "ideal_pending")
            findings.append(Finding(
                R_IDENTITY, "%s:untested:%s" % (R_IDENTITY, cid),
                TRIAGE, cid,
                "claim %s records its rewriting -- %s = %s -- and nothing has "
                "reduced it.\n"
                "  %s Until it is made, `identity_origin` is still the "
                "author's word for the one field on this claim that decides "
                "where it may travel."
                % (cid, c.get("lhs"), c.get("rhs"),
                   ("The claim asserts that lhs - rhs lies in %s's ideal, and "
                    "THAT IDEAL HAS NOT BEEN COMPUTED YET -- the model is "
                    "waiting on %s. The reduction is not one solver call away; "
                    "it is one solver call away from being askable."
                    % (c.get("model"), waiting)) if waiting else
                   ("This is the cheap case. The claim asserts that lhs - rhs "
                    "lies in %s's ideal, reduction modulo a Groebner basis "
                    "DECIDES that, and the answer is one solver call away."
                    % c.get("model"))),
                ("Run the computation the model is waiting on and record its "
                 "generators; `gp verify` can reduce this claim only once the "
                 "ideal it names exists.") if waiting else
                ("Run `gp verify`. It reduces every structured IDENTITY and "
                 "records the verdict, and a REFUTED answer here would mean "
                 "the rewriting is false at its own model -- which no "
                 "transport typing anywhere downstream would ever have "
                 "surfaced."),
                semantic_key=cid))
            continue
        # PREMISES, NOT `claim`/`path` -- see `_legs`, which now owns both
        # halves of that trap.
        legs = [path for _, path in _legs(graph, cid)]
        for path in legs:
            hit = False
            for step in path:
                eid = step[0] if isinstance(step, (list, tuple)) else step
                direction = (step[1] if isinstance(step, (list, tuple))
                             and len(step) > 1 else None)
                e = graph.edges.get(eid)
                if not e or eid in dead:
                    continue
                if e.get("type") != K.RESTRICTION or direction != K.ALONG:
                    continue
                hit = True
                findings.append(Finding(
                    R_IDENTITY, "%s:%s:%s" % (R_IDENTITY, cid, eid),
                    TRIAGE, cid,
                    "claim %s crosses RESTRICTION %s as an IDENTITY, and "
                    "states its rewriting only in prose.\n"
                    "  That cell was gated on a declared `zariski_dense` until "
                    "the declaration was found to be both insufficient and "
                    "beside the point, and it is now unconditional. The cell "
                    "is right -- a restriction shares its ideal, so an identity "
                    "at one end IS the identity at the other -- but it is only "
                    "right about things that are actually identities. A "
                    "relation observed to vanish at every point of the region "
                    "is a POINTWISE claim, and it crosses this edge by being "
                    "mislabelled rather than by being transported."
                    % (cid, eid),
                    "Record `lhs`, `rhs` and `ring_vars` on the claim and run "
                    "`gp verify`. Reduction decides it: if lhs - rhs lies in "
                    "the model's ideal the claim is what it says it is, and if "
                    "it does not, the claim was pointwise all along and belongs "
                    "at the region as a PREDICATE -- which does not cross.",
                    semantic_key=cid))
                break
            if hit:
                break
    return findings


def run(graph, accepted=None):
    """All rules, in a stable order, most severe first.

    `accepted` is the baseline, passed in only because supersession has to know
    which obligations an edge inherited and what they will admit as a
    discharge.  Everything else is a pure function of the graph.
    """
    transport_findings = check_transport(graph)
    findings = (transport_findings
                + check_taint(graph, transport_findings)
                + check_coverage(graph)
                + check_refinement(graph)
                + check_untyped(graph)
                + check_unjustified_equivalence(graph)
                + check_self_refuting_equivalence(graph)
                + check_unknown_identity_origin(graph)
                + check_unexhibited_witness(graph)
                + check_witness_point(graph)
                + check_aliases(graph)
                + check_partitions(graph)
                + check_supersession(graph, accepted)
                + check_stale_premises(graph)
                + check_stale_paths(graph)
                + check_families(graph)
                + check_evidence_direction(graph)
                + check_crosscuts(graph)
                + check_inexpressible(graph)
                + check_pending_ideals(graph)
                + check_containment(graph)
                + check_identity(graph)
                + check_sibling_edges(graph)
                + check_stale_models(graph)
                + check_stale_references(graph)
                + check_citations(graph)
                + check_doubts(graph)
                + check_coefficients_in_base(graph)
                + check_integral(graph)
                + check_origin_contradiction(graph)
                + check_localized_unit_certificates(graph)
                + check_refuted_evidence(graph)
                + check_evidence(graph)
                + check_parallel_edges(graph)
                + check_vacuous_conclusions(graph)
                + check_self_built(graph))
    findings.sort(key=lambda f: (-SEVERITY_RANK[f.severity], f.rule, f.fid))
    return findings


def clean_inferences(graph, findings):
    """Inferences the checker did NOT flag.

    Reported because a framework that flags a sound step is a false-positive
    generator and unusable.  The positive controls are the load-bearing half of
    any credibility claim, so they get printed, not assumed.

    A WITHDRAWN INFERENCE IS NOT A POSITIVE CONTROL.  `check_transport` skips
    superseded inferences -- correctly, they license nothing -- and this
    counted everything it did not flag, so every withdrawn argument was
    promoted into the clean list.  A live campaign's `gp check` reported
    "clean inferences (5)" of which FOUR were withdrawn and one was genuinely
    clean.

    That is the loudest possible version of the mistake, because this number is
    the credibility claim: it is the count a reader uses to decide the checker
    is not simply refusing everything.  Inflating it with dead records is the
    same failure as `gp check` exiting 0 on a graph nobody audited, which the
    reporting project's own trap list phrases as "a checker that exits 0 has
    not necessarily proved its claim".

    AND IT COUNTED ONLY `TRANSPORT` FINDINGS, which is the same mistake in a
    quieter register.  An inference whose every step was licensed by the table,
    riding an edge that some OTHER rule had flagged, was promoted into the
    clean list -- so an argument crossing an edge whose central containment
    failed verification, or an edge between two mutually exclusive branches of
    a partition, was reported as a positive control.

    Found while closing the sibling-edge hole: the fixture that produced the
    new UNSOUND_PREMISE finding also produced `clean inferences: ['I1']`, for
    the inference riding the very edge that had just been flagged.  A reader
    gets both statements and no way to reconcile them.

    So clean now means: nothing UNSOUND on it, on its route, or on its
    premises.  The number gets smaller and starts meaning what its own
    docstring says it means.

    SEVERITY, NOT MERE PRESENCE, and the first version of this fix got that
    wrong.  Filtering on "any finding at all" dropped two pinned positive
    controls carrying VACUOUS-CONCLUSION at TRIAGE -- inferences whose
    transport is entirely correct and whose conclusion happens to be
    uninteresting because its model was proved empty elsewhere.  Those are
    exactly what a positive control IS: the checker declining to refuse a
    sound step.  A TRIAGE finding is not a refusal, so it must not cost an
    inference its clean status.

    AND ON THE DERIVED SEVERITY, NOT THE OVERRIDDEN ONE.  Using `f.severity`
    let the single inference in the corpus that talks its own severity DOWN
    reappear as a positive control.  An argument the checker refused is not
    evidence that the checker declines to refuse sound arguments, however
    deliberately its author chose to carry it -- so the number a reader uses to
    judge false-positive rate must be computed from what the checker concluded.
    """
    flagged = {f.subject for f in findings
               if SEVERITY_RANK[f.derived_severity]
               >= SEVERITY_RANK[UNSOUND_PREMISE]}
    # AND AN UNVERIFIED IDENTITY DISQUALIFIES, though it is only TRIAGE.
    #
    # The severity filter is right in general -- a VACUOUS-CONCLUSION at TRIAGE
    # is a legitimate positive control -- but UNTESTED-IDENTITY is different in
    # kind. It says the claim's CENTRAL CONTENT has never been checked, and an
    # argument resting on that is not evidence that the checker declines to
    # refuse sound steps.
    #
    # Found via a review's counterexample: localise `k[x,y]/(xy)` at `x`, where
    # `y = 0` holds in the localisation and not in the ambient ring. Declared
    # as an IDENTITY and transported ALONG, the table licenses it -- correctly,
    # because a RESTRICTION shares its ideal, so the fault is that `y = 0` is
    # not an IDENTITY at that model at all. `verify.identity` REFUTES it. But
    # at the default floor `gp check` reported the inference CLEAN and exited
    # 0, with the only signal sitting below the failing floor.
    flagged |= {f.subject for f in findings if f.rule == R_IDENTITY}
    return [i for i, _why in _partition_inferences(graph, flagged)[0]]


def _touches(graph, iid):
    """Everything an inference rests on: its premise claims and its path."""
    inf = graph.inferences[iid]
    out = set()
    for pr in inf.get("premises") or []:
        if pr.get("claim"):
            out.add(pr["claim"])
        for step in pr.get("path") or []:
            out.add(step[0] if isinstance(step, (list, tuple)) else step)
    return out


def _partition_inferences(graph, flagged):
    """(clean, disqualified) -- and the second is why this function exists.

    THE SILENT DISAPPEARANCE.  Making `clean_inferences` exclude anything
    riding a flagged edge was right, and it created a third category nothing
    reported: an inference that is not clean, because its edge is flagged, and
    not in the findings either, because the finding names the EDGE.

    A live campaign hit it on a TRUE, correctly-typed inference and said the
    right thing about it -- "not refused; silently absent... that is the one
    failure mode a tool like this must never have."

    So the partition is explicit and both halves are returned.  A reader is
    told which arguments are positive controls, which are refused, and which
    are neither and why.
    """
    clean, disqualified = [], []
    for iid in graph.inference_order:
        inf = graph.inferences[iid]
        if inf.get("superseded_by"):
            continue
        if iid in flagged:
            continue          # reported in its own right
        hit = sorted(_touches(graph, iid) & flagged)
        if hit:
            disqualified.append((iid, hit))
        else:
            clean.append((iid, []))
    return clean, disqualified


def disqualified_inferences(graph, findings):
    """Inferences neither clean nor flagged, with what disqualified them."""
    flagged = {f.subject for f in findings
               if SEVERITY_RANK[f.derived_severity]
               >= SEVERITY_RANK[UNSOUND_PREMISE]}
    flagged |= {f.subject for f in findings if f.rule == R_IDENTITY}
    return _partition_inferences(graph, flagged)[1]


def render(findings, accepted=None, full=False):
    """Findings as text, with CARRIED ones marked as such.

    THIS IS THE T3 REPAIR.  A fresh agent handed the campaign reported "gate
    failing, five live blockers" when all nine findings had been examined and
    knowingly accepted, each with a reason.  It was not careless -- no read path
    in the system showed acceptances.  `gp check` did not, `gp check --full` did
    not exist, and `portage_check`'s `full` parameter was declared in the MCP
    schema and never read by its handler.  The baseline decided whether the HOOK
    blocked and was invisible to every tool anyone used to UNDERSTAND a
    campaign.

    So a resuming reader could not distinguish "this campaign is broken" from
    "this campaign is healthy and carrying known debt" -- which is most of the
    difference between a campaign and a mess.

    Carried findings print as one marked line with their reason, because the
    reason is the part a reviewer needs; `full=True` adds their detail.  The
    default is compact rather than hidden: once a campaign has a real graph,
    re-printing every carried obligation in full is noise on every call, but
    printing NOTHING is what caused this.
    """
    accepted = accepted or {}
    if not findings:
        return ("no findings: every recorded conclusion is licensed by the "
                "transport it rests on.")
    live = [f for f in findings if f.fid not in accepted]
    carried = [f for f in findings if f.fid in accepted]
    out = []
    # A DISCHARGE REPEATED IS NOT A DISCHARGE TWICE.
    #
    # Measured on a real campaign: 32 findings, 22,486 bytes, of which DISCHARGE
    # was 47% -- and 68% of THOSE bytes were duplicates. CONTAINMENT fired 8
    # times, TRANSPORT 7, DOUBT 5, and DOUBT's five discharges were ONE distinct
    # string. A rule's discharge is static prose; only the ids vary.
    #
    # This matters more than tidiness now that the hook actually fires: the
    # refusal path pays this cost on EVERY TOOL CALL, and the same wall arriving
    # repeatedly buries the move it is telling you to make.
    #
    # COMPRESS BY NOT REPEATING THE PROSE, NEVER BY SHORTENING IT. The discharge
    # is where this tool delivers its value -- a campaign once spent its most
    # expensive hour on a refusal whose correct answer could not be looked up --
    # so the first occurrence is printed in full and later identical ones point
    # back to it. Nothing is lost and nothing has to be asked for.
    seen_discharge = {}
    for f in live:
        out.append("%s  %s" % (f.severity, f.fid))
        out.extend("    " + l for l in f.detail.splitlines())
        first = seen_discharge.get((f.rule, f.discharge))
        if first is None:
            seen_discharge[(f.rule, f.discharge)] = f.fid
            out.append("    -> DISCHARGE: %s" % f.discharge)
        else:
            out.append("    -> DISCHARGE: as %s above." % first)
        out.append("")
    if carried:
        out.append("CARRIED -- examined and knowingly accepted (%d). These are "
                   "recorded debt, not new breakage:" % len(carried))
        for f in carried:
            entry = accepted.get(f.fid) or {}
            out.append("  %s  %s" % (f.severity, f.fid))
            out.append("      because: %s"
                       % (entry.get("why") or "(no reason recorded)"))
            if full:
                out.extend("      " + l for l in f.detail.splitlines())
        out.append("")
    if not live:
        out.append("No LIVE findings. Everything above was accepted "
                   "deliberately; the campaign is carrying debt in the open, "
                   "not failing.")
    return "\n".join(out)


def exit_code(findings, floor=UNSOUND_PREMISE, accepted=()):
    """1 iff any LIVE finding is at or above `floor`.

    The floor is DEBT-tolerant by default: a recorded hole is a hole you are
    tracking, and blocking on it would push people to stop recording them.

    ACCEPTANCE HAS TO REACH THE EXIT CODE, and for two releases it did not.
    This function never saw the baseline, so a campaign whose every finding had
    been examined and deliberately carried still exited 1 -- while the same
    command printed, three lines earlier:

        "Nothing live. Every finding at this floor was examined and accepted
         deliberately -- this campaign is carrying debt in the open, NOT
         FAILING."

    The prose and the exit code said opposite things, and the exit code is what
    a hook or a CI step reads.  So `gp accept` bought nothing at the only layer
    that automates, and a campaign legitimately carrying debt could never go
    green -- which is precisely the pressure that stops people recording holes,
    the thing the DEBT-tolerant default exists to avoid.

    A finding that is carried is not absent: it still prints, `gp history`
    still lists it, and re-accepting is still a deliberate act.  It just does
    not fail the build, because somebody already looked at it.
    """
    rank = SEVERITY_RANK[floor]
    accepted = set(accepted or ())
    return 1 if any(SEVERITY_RANK[f.severity] >= rank
                    and f.fid not in accepted for f in findings) else 0


def collect_hints(graph, **objects):
    """Author-supplied remedies from every object a finding touches.

    `discharge_for` knows what a CELL requires and cannot know what a CAMPAIGN
    would do about it.  That gap used to be filled by edges alone, and the one
    piece of evidence anybody has about cross-session handoff says it was the
    right mechanism pointed at too few objects: a returning session found the
    edge hint "came back verbatim in every refusal" and was "the only artifact
    in the campaign that did real cross-session handoff work", in the same
    report that found every prose claim about the tool had rotted within a
    session.

    So: models, claims, families and partitions carry one too.  Pass the
    objects a finding is about; the ones that have something to say are
    rendered, labelled by what they are, and the rest cost nothing.
    """
    out = []
    for label in sorted(objects):
        obj = objects[label]
        if isinstance(obj, str):
            obj = (graph.models.get(obj) or graph.claims.get(obj)
                   or graph.families.get(obj) or graph.edges.get(obj)
                   or graph.partitions.get(obj))
        if obj and obj.get("discharge_hint"):
            out.append((label, obj["discharge_hint"]))
    return out
