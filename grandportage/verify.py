"""Verify by computation what the graph currently takes on the author's word.

SEPARATE FROM THE CHECKER ON PURPOSE.  `check.py` is deterministic, spawns no
process and reaches no network; given a graph it returns the same findings
every time, and that property is worth more than the convenience of folding
verification into it.  So the division is:

    check.py    reports the HOLE      -- free, deterministic, every run
    verify.py   fills it              -- costs CAS time, an explicit act

That split is the same one the project already makes between a finding and its
discharge, and it keeps the expensive thing opt-in.

WHAT IS VERIFIED, and why it is the deepest thing here.  Every edge asserts
`V(src) subset V(dst)`.  The kernel's opening comment says so and all six types
are relaxations in that sense -- and it has never been checked, only declared.
That makes it the SIXTH instance of the pattern this project keeps finding, at
the lowest level available: a field that DETERMINES transport and is taken on
the author's word.

The containment follows from an ideal containment the other way round:

    I(dst) subset I(src)   ==>   V(src) subset V(dst)

More equations cut a smaller variety.  So the test is one reduction per
generator of `I(dst)`: each must lie in `I(src)`, which is exactly the
membership question `cas.classify_identity` already answers.

SUFFICIENT, NOT NECESSARY, AND THE FAILING SIDE PROVES NOTHING.  This is the
whole of what this module may and may not say, and getting it wrong here would
be the same overreach it exists to catch.

    I(dst) subset I(src)       ==>  V(src) subset V(dst)      SOUND
    I(dst) not subset I(src)   ==>  nothing follows

The containment really needs `I(dst) subset RADICAL(I(src))`, and reduction
tests plain ideal membership.  So a generator that fails to reduce refutes the
CHEAP TEST and not the edge: the containment may still hold through the
radical.  There are therefore three verdicts and REFUTED is not among them --

    VERIFIED       every generator reduced; the containment is established
    NOT_BY_IDEAL   the cheap test failed; the containment is UNESTABLISHED,
                   which is not the same as false
    UNVERIFIED     the question could not be put (no ideal, different rings)

Genuinely REFUTING an edge needs a point of `V(src)` outside `V(dst)` -- a
witness, not a reduction -- and that is deliberately out of scope here.  A
module that answered a question it had not asked would be the honour system
wearing a computation.
"""

import hashlib
import os

from . import cas
from . import kernel as K
from . import store as S

VERIFIED = "VERIFIED"
NOT_BY_IDEAL = "NOT_BY_IDEAL"
UNVERIFIED = "UNVERIFIED"


def containment(graph, eid, timeout=300, _runner=None):
    """Is `I(dst)` inside `I(src)`?  Returns (verdict, why).

    One reduction per generator, stopping at the first that fails, because the
    first failure is the whole answer and the rest cost money.
    """
    e = graph.edges[eid]
    src, dst = graph.models.get(e["src"]), graph.models.get(e["dst"])
    if not src or not dst:
        return UNVERIFIED, "an endpoint is not a declared model"
    if src.get("generators") is None or dst.get("generators") is None:
        return UNVERIFIED, "one endpoint carries no ideal"
    ring = src.get("ring_vars") or []
    if not ring:
        return UNVERIFIED, "the source model declares no ring variables"
    if set(dst.get("ring_vars") or []) != set(ring):
        # NOT A FAILURE OF THE MATHEMATICS, a failure of the comparison.  Two
        # ideals in different rings are not comparable by reduction, and
        # pretending otherwise would produce a confident verdict about nothing.
        return UNVERIFIED, (
            "the two models are written in different rings (%s vs %s); an "
            "ideal containment between them is not a reduction question"
            % (", ".join(ring), ", ".join(dst.get("ring_vars") or [])))

    src_gens = list(src["generators"])
    for g in dst["generators"]:
        origin, evidence = cas.classify_identity(
            ring, lhs=g, rhs="0", generators=src_gens,
            timeout=timeout, _runner=_runner)
        if origin in (K.AMBIENT, K.DERIVED):
            continue
        return NOT_BY_IDEAL, (
            "generator %r of %s's ideal does not reduce to 0 modulo %s's -- it "
            "reduces to %s. So I(%s) is not inside I(%s), and the SUFFICIENT "
            "test for V(%s) subset V(%s) fails.\n"
            "  THAT IS NOT A REFUTATION. The containment can still hold "
            "through the radical, which reduction does not test. What it means "
            "is that the edge's central assertion is UNESTABLISHED, where "
            "before it was merely unexamined. To refute it you need a point of "
            "V(%s) outside V(%s), and that is a witness rather than a "
            "reduction."
            % (g, e["dst"], e["src"],
               (evidence or {}).get("reduced_modulo_ideal", "a nonzero form"),
               e["dst"], e["src"], e["src"], e["dst"], e["src"], e["dst"]))
    return VERIFIED, (
        "every generator of %s's ideal reduces to 0 modulo %s's, so I(%s) is "
        "inside I(%s) and V(%s) is inside V(%s)."
        % (e["dst"], e["src"], e["dst"], e["src"], e["src"], e["dst"]))


AMBIENT = "VERIFIED_AMBIENT"
DERIVED = "VERIFIED_DERIVED"
REFUTED = "REFUTED"


def identity(graph, cid, timeout=300, _runner=None):
    """Does this IDENTITY claim hold at its own model?  Returns (verdict, why).

    AND HERE, UNLIKE `containment`, REFUTATION IS AVAILABLE.  That asymmetry is
    not an inconsistency and it is worth stating plainly, because the module's
    other half spends a docstring refusing to say REFUTED.

        containment   the claim is `V(src) subset V(dst)`, a statement about
                      POINTS.  Reduction tests ideal membership, which is only
                      SUFFICIENT for it -- the containment can hold through the
                      radical -- so a failed reduction proves nothing.

        identity      the claim IS `lhs - rhs` lies in I, a statement about
                      FUNCTIONS.  Reduction modulo a Groebner basis DECIDES
                      ideal membership.  So a failed reduction is not a failed
                      cheap test; it is the answer.

    The difference is the same one the kernel keeps making between points and
    functions -- V(x) and V(x^2) have the same points and different coordinate
    rings -- and it is why a single reduction means different things at the two
    ends of this file.

    The verdicts:

        VERIFIED_AMBIENT   lhs - rhs is 0 in the polynomial ring.  The
                           rewriting never used the model's equations, so
                           `identity_origin: AMBIENT` is now MINTED BY
                           COMPUTATION rather than declared.
        VERIFIED_DERIVED   nonzero, but reduces to 0 modulo I.  It holds here
                           and rests on this model's own equations.
        REFUTED            it does not reduce.  The rewriting is FALSE at the
                           model it was claimed at, which no amount of correct
                           transport typing would ever have surfaced.
        UNVERIFIED         the question could not be put.
    """
    c = graph.claims.get(cid)
    if not c:
        return UNVERIFIED, "no such claim"
    if c.get("kind") != K.IDENTITY:
        return UNVERIFIED, "claim %s is %s, not an IDENTITY" % (cid, c.get("kind"))
    if c.get("lhs") is None or c.get("rhs") is None:
        return UNVERIFIED, (
            "claim %s states its rewriting only in prose. `lhs` and `rhs` are "
            "what makes it a reduction question rather than a reading "
            "question." % cid)
    ring = c.get("ring_vars") or []
    if not ring:
        return UNVERIFIED, "claim %s declares no ring variables" % cid
    model = graph.models.get(c.get("model")) or {}
    # A MODEL WITH NO EQUATIONS IS NOT A MODEL WITH MISSING DATA, and the
    # first version of this guard refused it as though it were.
    #
    # The complaint it answered was real: the REFUTED message named "%s's
    # ideal" at a model that has none, sending a reader to look for equations
    # nobody recorded.  But the fix for a wrong sentence is a right sentence.
    # Refusing to verify turned a wording bug into a false refusal, and it
    # landed on the exact case that motivated the feature -- an SOS Gram
    # identity `mon^T G mon - f = 0` lives in the polynomial ring and needs no
    # ideal at all.  `cas.classify_identity` already says so: "the model
    # imposes nothing, so 'modulo I' is the same question as 'in the ambient
    # ring', and the two agree by construction rather than by accident."
    #
    # So verify either way, and let the PROSE carry the distinction.  With no
    # ideal, DERIVED is unreachable by construction and REFUTED means "not
    # identically zero in the polynomial ring" rather than "false at this
    # model" -- both true, both worth saying, neither a reason to decline.
    gens = list(model.get("generators") or [])
    bare = not gens
    modulo = ("in the polynomial ring, which is the whole question here "
              "because %s imposes no equations" % c.get("model") if bare
              else "modulo %s's ideal" % c.get("model"))
    origin, evidence = cas.classify_identity(
        ring, lhs=c["lhs"], rhs=c["rhs"], generators=gens,
        timeout=timeout, _runner=_runner)
    if origin == K.AMBIENT:
        return AMBIENT, (
            "(%s) - (%s) reduces to 0 in the polynomial ring itself%s. The "
            "rewriting is AMBIENT, and that is now a computed fact rather "
            "than a declared one."
            % (c["lhs"], c["rhs"],
               "" if bare else
               ", before any of %s's equations are imposed" % c.get("model")))
    if origin == K.DERIVED:
        return DERIVED, (
            "(%s) - (%s) is nonzero in the polynomial ring but reduces to 0 modulo "
            "%s's ideal, so the rewriting holds in that coordinate ring and "
            "DERIVES from the model's own equations."
            % (c["lhs"], c["rhs"], c.get("model")))
    return REFUTED, (
        "(%s) - (%s) does not reduce to 0 %s -- it reduces to %s.\n"
        "  THIS ONE IS A REFUTATION, unlike a failed containment. %s So the "
        "rewriting is false where it was claimed, and every transport that "
        "carried it carried something untrue."
        % (c["lhs"], c["rhs"], modulo,
           (evidence or {}).get("reduced_modulo_ideal", "a nonzero form"),
           ("The claim is that the difference is identically zero, and that "
            "is decided by normalising it." if bare else
            "The claim is that the difference lies in the ideal, and "
            "reduction modulo a Groebner basis DECIDES ideal membership.")))


def _verdict_event(subject, of, verdict, why):
    # Content-addressed id, so re-verifying an unchanged thing with an
    # unchanged answer is an IDEMPOTENT redeclaration and the fold absorbs it.
    # Re-verifying after something changed produces a different id and both
    # verdicts stay in the log, which is what makes `gp history` able to show
    # that the answer moved.
    digest = hashlib.sha1(
        ("%s|%s|%s|%s" % (subject, of, verdict, why)).encode("utf-8")
    ).hexdigest()[:12]
    return {"ev": S.EV_VERDICT, "id": "v.%s.%s" % (of, digest),
            "subject": subject, "of": of, "verdict": verdict, "why": why}


def verify_all(root=".", timeout=300, _runner=None, record=True):
    """Verify every checkable edge AND claim, and RECORD the answers.

    RECORDING WAS THE STATED POINT AND DID NOT HAPPEN.  This function's own
    docstring promised the results were "appended as a supersession of the
    edge, so the log stays append-only and `gp history` shows that the check
    happened".  A live session measured it: the graph file was byte-identical
    before and after, and there was no `append` anywhere in the module.  It
    also iterated edges only, so the claim half had no batch entry point at
    all.  Both are fixed here.

    The answers go in as `verdict` events rather than as supersessions of the
    thing verified.  A supersession says the record CHANGED; a verdict says
    somebody CHECKED it, and the claim itself is untouched by having been
    examined.  Conflating those would make `gp history` report every
    verification as an amendment to the mathematics.

    Recording is the point.  A verification that lives in a terminal scrollback
    is a verification nobody can act on next week, and this project's whole
    claim is that the graph is the state.
    """
    path = S.graph_path(root)
    graph = S.load(path)
    results, events = [], []

    for eid in sorted(graph.edges):
        e = graph.edges[eid]
        if e.get("containment"):
            continue
        src, dst = graph.models.get(e["src"]), graph.models.get(e["dst"])
        if not src or not dst:
            continue
        if src.get("generators") is None or dst.get("generators") is None:
            continue
        verdict, why = containment(graph, eid, timeout=timeout,
                                   _runner=_runner)
        results.append(("edge", eid, verdict, why))
        events.append(_verdict_event("edge", eid, verdict, why))

    for cid in sorted(graph.claims):
        c = graph.claims[cid]
        if c.get("kind") != K.IDENTITY or c.get("identity_verdict"):
            continue
        # Silent where the rewriting was never recorded.  An unstructured
        # IDENTITY is not a failed verification, it is an unasked question,
        # and `check` is where that hole gets reported.
        if c.get("lhs") is None or c.get("rhs") is None:
            continue
        verdict, why = identity(graph, cid, timeout=timeout, _runner=_runner)
        results.append(("claim", cid, verdict, why))
        events.append(_verdict_event("claim", cid, verdict, why))

    if record and events:
        # ROOT, not the graph path.  `append` resolves `.portage/graph.jsonl`
        # itself, so passing the resolved path built
        # `.portage/graph.jsonl/.portage` and crashed -- on the ONE line the
        # suite never reached, because every test called `verify_all` with
        # `record=False` or a fixture that produced no events.
        S.append(events, root)
    return results
