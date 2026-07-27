"""The checker: reads a folded graph, emits findings, decides.

Deterministic, no model in the loop, no solver, no network.  Given a graph it
returns the same findings every time, and `gp check` exits 0 iff there are
none above the configured severity floor.

The checker never grades evidence and the ladder never licenses a transport.
Those are orthogonal axes and conflating them is how a project ends up with an
`independently-audited` predicate imported across an edge that forbids it.
"""

import hashlib

from . import kernel as K
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
    claim = graph.claims[inf["claim"]]
    trace, ok = [], True
    for eid, direction in inf["path"]:
        e = graph.edges[eid]
        r = K.transport(e["type"], direction, claim["kind"],
                        scope=claim.get("scope"),
                        certificate=claim.get("certificate"),
                        map_kind=e["map_kind"],
                        zariski_closed=claim.get("zariski_closed"),
                        identity_origin=claim.get("identity_origin"),
                        integral=claim.get("integral"),
                        ring_iso=e.get("ring_iso"),
                        coefficients_in_base=claim.get("coefficients_in_base"))
        trace.append((eid, direction, r.licensed, r.reason))
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
    return K.transport(
        etype or edge["type"], direction, claim["kind"],
        scope=claim.get("scope"), certificate=claim.get("certificate"),
        map_kind=map_kind or edge["map_kind"],
        zariski_closed=(claim.get("zariski_closed")
                        if zariski_closed is None else zariski_closed),
        identity_origin=claim.get("identity_origin"),
        integral=claim.get("integral"), ring_iso=edge.get("ring_iso"),
        coefficients_in_base=claim.get("coefficients_in_base"))


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
                  if c["model"] == model_id and c["kind"] == opposite
                  and cid not in exclude)


def _first_refusal(graph, trace):
    for eid, direction, ok, reason in trace:
        if not ok:
            return graph.edges[eid], direction, reason
    return None, None, None


def check_transport(graph):
    findings = []
    for iid in graph.inference_order:
        inf = graph.inferences[iid]
        ok, trace = audit_inference(graph, iid)
        if ok:
            continue
        edge, direction, reason = _first_refusal(graph, trace)
        counter = contradicting_claims(graph, inf["concludes_at"],
                                       inf["concludes_kind"],
                                       exclude=(inf["claim"],))
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
            graph.claims[inf["claim"]]["statement"], inf["asserted"], reason)
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
            discharge_for(edge["type"], direction, inf["concludes_kind"],
                          graph=graph, edge=edge,
                          fid="%s:%s" % (R_TRANSPORT, iid),
                          traffic=True),
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
                            if c["model"] == mid)
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


def check_untyped(graph):
    findings = []
    for eid in sorted(graph.edges):
        e = graph.edges[eid]
        if e["type"] != K.UNTYPED:
            continue
        downstream = sorted(iid for iid in graph.inference_order
                            if any(s[0] == eid
                                   for s in graph.inferences[iid]["path"]))
        findings.append(Finding(
            R_UNTYPED, "%s:%s" % (R_UNTYPED, eid), DEBT, eid,
            "edge %s (%s -> %s) has no declared relaxation type.\n  debt: %s\n"
            "  inferences crossing it: %s"
            % (eid, e["src"], e["dst"], e.get("debt_why"),
               ", ".join(downstream) or "(none yet)"),
            discharge_for(K.UNTYPED, None, None, graph=graph, edge=e)))
    return findings


def check_refinement(graph):
    """Monotonicity is not a fourth type.

    Adding equations gives V(new) subset V(old), which is a NECESSARY_CONDITION
    edge new -> old read AGAINST.  "A closed branch can never reopen under
    refinement" is therefore a theorem about ONE existing type, and a
    refinement edge typed as anything else is a modelling error.
    """
    findings = []
    for eid in sorted(graph.edges):
        e = graph.edges[eid]
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

    Reported at DEBT, not higher, and only when the edge offers NEITHER a
    `witness` nor a `cite`.  A well-documented equivalence is not a finding;
    an undocumented one is a claim resting on the author's confidence.

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

    They are now separate, and only a CONVERSE witness -- the construction that
    recovers a point of the source from a point of the target -- documents an
    equivalence.  A strictness witness on an EQUIVALENCE edge is not merely
    insufficient; it is the edge exhibiting its own refutation, and it gets its
    own finding below.
    """
    findings = []
    for eid in sorted(graph.edges):
        e = graph.edges[eid]
        if e["type"] != K.EQUIVALENCE:
            continue
        if e.get("converse_witness") or e.get("cite"):
            continue
        findings.append(Finding(
            "UNJUSTIFIED-EQUIVALENCE", "UNJUSTIFIED-EQUIVALENCE:%s" % eid,
            DEBT, eid,
            "edge %s (%s -> %s) is typed EQUIVALENCE with neither a `witness` "
            "nor a `cite`.\n  EQUIVALENCE is the only type that forbids "
            "nothing, so this one row licenses every transport across the "
            "step, in both directions, unconditionally."
            % (eid, e["src"], e["dst"]),
            "Exhibit the converse -- the construction that recovers a point of "
            "%s from a point of %s -- or cite where it is proved. If you "
            "cannot do either, the step is a NECESSARY_CONDITION and should "
            "say so; nothing is lost by the weaker type except conclusions you "
            "were not entitled to." % (e["src"], e["dst"])))
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
    for eid in sorted(graph.edges):
        e = graph.edges[eid]
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


def run(graph):
    """All rules, in a stable order, most severe first."""
    transport_findings = check_transport(graph)
    findings = (transport_findings
                + check_taint(graph, transport_findings)
                + check_coverage(graph)
                + check_refinement(graph)
                + check_untyped(graph)
                + check_unjustified_equivalence(graph)
                + check_self_refuting_equivalence(graph)
                + check_unknown_identity_origin(graph))
    findings.sort(key=lambda f: (-SEVERITY_RANK[f.severity], f.rule, f.fid))
    return findings


def clean_inferences(graph, findings):
    """Inferences the checker did NOT flag.

    Reported because a framework that flags a sound step is a false-positive
    generator and unusable.  The positive controls are the load-bearing half of
    any credibility claim, so they get printed, not assumed.
    """
    flagged = {f.subject for f in findings if f.rule == R_TRANSPORT}
    return [i for i in graph.inference_order if i not in flagged]


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
    for f in live:
        out.append("%s  %s" % (f.severity, f.fid))
        out.extend("    " + l for l in f.detail.splitlines())
        out.append("    -> DISCHARGE: %s" % f.discharge)
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


def exit_code(findings, floor=UNSOUND_PREMISE):
    """1 iff any finding is at or above `floor`.

    The floor is DEBT-tolerant by default: a recorded hole is a hole you are
    tracking, and blocking on it would push people to stop recording them.
    """
    rank = SEVERITY_RANK[floor]
    return 1 if any(SEVERITY_RANK[f.severity] >= rank for f in findings) else 0
