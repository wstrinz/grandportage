"""Verify by computation what the graph currently takes on the author's word.

SEPARATE FROM THE CHECKER ON PURPOSE.  `check.py` is deterministic, spawns no
process and reaches no network; given a graph it returns the same findings
every time, and that property is worth more than the convenience of folding
verification into it.  So the division is:

    check.py    reports the HOLE      -- free, deterministic, every run
    verify.py   fills it              -- costs CAS time, an explicit act

That split is the same one the project already makes between a finding and its
discharge, and it keeps the expensive thing opt-in.

WHAT IS VERIFIED, and why it is the deepest thing here.  An inclusion-style
edge asserts `V(src) subset V(dst)`, and that premise was never checked, only
declared.

SPECIALIZATION IS NOT AN INCLUSION. It relates the generic fibre of a scheme
over Spec Z to a special fibre. Those are different fibres, not nested sets;
the kernel's own Fano/non-Fano counterexamples go in both directions. There is
no containment to check, so `containment` refuses the row rather than computing
a confident answer about a relation that does not exist.

A MAPPED EQUIVALENCE IS THE SECOND NON-INCLUSION PRESENTATION. Its `forward`
substitution carries source points to target points and `inverse` carries them
back; `ring_iso` checks both ideal maps and both inverse compositions. Neither
direction implies literal containment in the written coordinates, exactly as
`GrandPortage/MappedEquivalence.lean` proves.

Found by asking how much of the transport table follows from inclusion alone.
Twenty-seven of thirty-six point cells do; three more follow from inclusion in
both directions, which is what an EQUIVALENCE's converse buys; three need a
capability inclusion does not supply. The last three are SPECIALIZATION's, and
they are weaker than inclusion for the reason above. A generalisation that
quietly mis-describes an exceptional presentation is the shape this project
exists to catch.

For edges that do assert literal inclusion, containment was the sixth instance
of the recurring pattern: a premise that determines transport and is taken on
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

import copy
import json
import os

from . import artifacts as A
from . import cas
from . import groebner as G
from . import groebner_producer as GP
from . import kernel as K
from . import operations as O
from . import provenance as P
from . import store as S

VERIFIED = "VERIFIED"
NOT_BY_IDEAL = "NOT_BY_IDEAL"
UNVERIFIED = "UNVERIFIED"


def _pending_ideal(mid, model):
    """The message for a model still waiting on the computation of its ideal.

    ASKED BEFORE THE SOLVER, NOT AFTER.  A constructed model -- a saturation,
    an elimination -- has an ideal that only the CAS knows, and it says so with
    `ideal_pending` rather than by putting a placeholder in `generators`.  The
    placeholder version reached Singular verbatim and came back `expected
    ideal-expression`, an honest error about the wrong thing: nothing had gone
    wrong with the solver, and nothing was wrong with the mathematics.  The
    author simply had not run the program yet, and no layer said so.
    """
    if not model.get("ideal_pending"):
        return None
    return ("%s does not carry an ideal yet -- it is waiting on %s. There is "
            "nothing to reduce modulo until that computation has run and its "
            "generators have been recorded. This is not a failed check; it is "
            "a check that cannot yet be put." % (mid, model["ideal_pending"]))


def _stale_endpoint(graph, eid):
    """Decline an edge question whose model anchor has been replaced."""
    e = graph.edges.get(eid) or {}
    for end in ("src", "dst"):
        mid = e.get(end)
        model = graph.models.get(mid) or {}
        if not model.get("superseded_by"):
            continue
        return (
            "edge %s still names %s model %s, which was superseded by %s. "
            "The verifier will not silently retarget a computation to a model "
            "the edge was never checked against. Supersede the edge with %s "
            "repointed, then rerun `gp verify`."
            % (eid, end, mid, S.successors(model), end))
    return None


def _declared_characteristic(mid, model):
    """Return an explicitly declared characteristic, never a guessed zero."""
    if "characteristic" not in model:
        return None, (
            "%s declares no characteristic. The verifier will not assume "
            "characteristic 0: the same polynomial computation can have a "
            "different answer after reduction modulo p. Declare 0 or the "
            "prime characteristic, then rerun `gp verify`." % mid)
    return model["characteristic"], None



def containment(graph, eid, timeout=300, _runner=None, _backend=None):
    """Is `I(dst)` inside `I(src)`?  Returns (verdict, why).

    One reduction per generator, stopping at the first that fails, because the
    first failure is the whole answer and the rest cost money.
    """
    e = graph.edges[eid]
    stale = _stale_endpoint(graph, eid)
    if stale:
        return UNVERIFIED, stale
    if K.is_mapped_equivalence(e):
        return UNVERIFIED, (
            "edge %s is a mapped EQUIVALENCE: it asserts that `forward` sends "
            "source points to target points and `inverse` sends them back. It "
            "does not assert literal V(%s) subset V(%s) in the coordinates as "
            "written. Run the `ring_iso` verifier for the mapped relation."
            % (eid, e["src"], e["dst"]))
    if e.get("type") == K.SPECIALIZATION:
        # NOT A RELAXATION, so there is no containment to test -- and the
        # reduction would have run in characteristic 0 against generators
        # living in characteristic p, producing a confident verdict about a
        # relation that does not exist.
        return UNVERIFIED, (
            "edge %s is a SPECIALIZATION, and that is the one type whose ends "
            "are not nested. The generic fibre and a special fibre of a scheme "
            "over Spec Z are DIFFERENT FIBRES: neither contains the other, and "
            "this kernel's own counterexamples say so -- the Fano plane is "
            "empty over Q and nonempty over F_2, the non-Fano matroid the "
            "reverse.\n"
            "  So `V(src) subset V(dst)` is not what this edge asserts, and "
            "there is nothing here for a reduction to establish. The four "
            "existence cells on this row are already False for exactly this "
            "reason." % eid)
    src, dst = graph.models.get(e["src"]), graph.models.get(e["dst"])
    if not src or not dst:
        return UNVERIFIED, "an endpoint is not a declared model"
    pending = _pending_ideal(e["src"], src) or _pending_ideal(e["dst"], dst)
    if pending:
        return UNVERIFIED, pending
    if src.get("generators") is None or dst.get("generators") is None:
        return UNVERIFIED, "one endpoint carries no ideal"
    ring = src.get("ring_vars") or []
    if not ring:
        return UNVERIFIED, "the source model declares no ring variables"
    ch, missing = _declared_characteristic(e["src"], src)
    if missing:
        return UNVERIFIED, missing
    dst_ch, missing = _declared_characteristic(e["dst"], dst)
    if missing:
        return UNVERIFIED, missing
    if dst_ch != ch:
        return UNVERIFIED, (
            "the endpoints declare different characteristics (%s vs %s). A "
            "reduction happens in ONE ring; comparing ideals across a "
            "characteristic change is what SPECIALIZATION is for, and it is "
            "refused above for the same reason."
            % (ch, dst_ch))
    if set(dst.get("ring_vars") or []) != set(ring):
        # NOT A FAILURE OF THE MATHEMATICS, a failure of the comparison.  Two
        # ideals in different rings are not comparable by reduction, and
        # pretending otherwise would produce a confident verdict about nothing.
        return UNVERIFIED, (
            "the two models are written in different rings (%s vs %s); an "
            "ideal containment between them is not a reduction question"
            % (", ".join(ring), ", ".join(dst.get("ring_vars") or [])))

    # Exact generator inclusion is already a complete certificate for this
    # special case: if every target generator occurs verbatim among the source
    # generators, then I(dst) is contained in I(src) with unit cofactors. Do
    # this before spawning a backend. Besides avoiding pointless Groebner
    # search, this keeps large sparse campaign models usable without weakening
    # the bounded search/checker contracts elsewhere. Parse the matched values
    # so identical malformed payloads cannot earn mathematical authority.
    src_gens = list(src["generators"])
    dst_gens = list(dst["generators"])
    if all(generator in src_gens for generator in dst_gens):
        try:
            for generator in dst_gens:
                G.parse_polynomial(generator, ring, ch)
        except G.CertificateError as exc:
            return UNVERIFIED, (
                "the target generators occur verbatim in the source, but "
                "one is not a valid polynomial in the declared ring: %s"
                % exc)
        return VERIFIED, (
            "every generator of %s's ideal occurs exactly among %s's "
            "generators, so unit-cofactor inclusion gives I(%s) inside "
            "I(%s) and V(%s) inside V(%s) without backend search."
            % (e["dst"], e["src"], e["dst"], e["src"],
               e["src"], e["dst"]))

    for g in dst_gens:
        origin, evidence = (_backend or cas.SingularBackend(runner=_runner)).classify_identity(
            ring, lhs=g, rhs="0", generators=src_gens,
            characteristic=ch, timeout=timeout)
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


def identity(graph, cid, timeout=300, _runner=None, _backend=None):
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
    # ASK THIS BEFORE `bare`, BECAUSE `bare` WOULD ANSWER IT WRONGLY.
    #
    # Below, a model with no generators is read as "imposes no equations" --
    # correct for an SOS Gram identity in the polynomial ring, and a FALSE
    # LICENCE for a saturation nobody has computed: the rewriting would be
    # reduced against the ambient ring and could come back VERIFIED_AMBIENT at
    # a model whose real ideal is unknown.  The two states spell themselves
    # differently for exactly this reason.
    pending = _pending_ideal(c.get("model"), model)
    if pending:
        return UNVERIFIED, pending
    ch, missing = _declared_characteristic(c.get("model"), model)
    if missing:
        return UNVERIFIED, missing
    # ABSENT IS NOT EMPTY, and reading them the same way is a false refutation.
    #
    # `generators: []` means THE AMBIENT SPACE -- the model imposes no
    # equations, so "modulo I" and "in the polynomial ring" are the same
    # question and agree by construction. That reading is right, and the SOS
    # Gram case depends on it.
    #
    # No `generators` key at all means NOBODY RECORDED THE IDEAL, which is a
    # different fact about the graph and not a fact about the model. Seventy-
    # five live models across five campaigns are in that state and NONE
    # declares `[]`, so this is the common case rather than the exotic one.
    #
    # Conflating them is safe in one direction and not the other:
    #
    #   difference is 0 in the polynomial ring  -> AMBIENT, and still SOUND.
    #     That is a statement about the ambient ring; unrecorded equations
    #     cannot make it false. So the SOS case keeps working untouched.
    #   difference is nonzero                   -> REFUTED, and FALSE.
    #     It says the rewriting does not hold at its own model, at
    #     UNSOUND_CONCLUSION, when the rewriting may hold perfectly well
    #     modulo equations the graph never recorded. "Not identically zero in
    #     the polynomial ring" is simply not the question that was asked.
    unrecorded = model.get("generators") is None
    gens = list(model.get("generators") or [])
    bare = not gens
    modulo = ("in the polynomial ring, which is the whole question here "
              "because %s imposes no equations" % c.get("model") if bare
              else "modulo %s's ideal" % c.get("model"))
    origin, evidence = (_backend or cas.SingularBackend(runner=_runner)).classify_identity(
        ring, lhs=c["lhs"], rhs=c["rhs"], generators=gens,
        characteristic=ch,
        timeout=timeout)
    if origin == K.AMBIENT:
        return AMBIENT, (
            "(%s) - (%s) reduces to 0 in the polynomial ring itself%s. The "
            "rewriting is AMBIENT, and that is now a computed fact rather "
            "than a declared one."
            % (c["lhs"], c["rhs"],
               "" if bare else
               ", before any of %s's equations are imposed" % c.get("model")))
    if origin == K.DERIVED:
        # AND HERE THE VERDICT EARNS A CERTIFICATE.
        #
        # "It reduced to 0" is a claim about a run.  Nobody can recheck it
        # without doing the run again, which means the only real check is
        # trusting the search -- the exact position `UNIT_IDEAL_CERT` was in
        # before its cofactors were captured, and that one produced an erratum.
        #
        # A DERIVED rewriting rests on the model's equations, so `lhs - rhs =
        # sum b_i f_i` and the cofactors ARE the derivation.  Expanding them is
        # arithmetic: no Buchberger, no monomial order, no trust in the search.
        # It is also the bridge to a proof assistant, which can check a
        # polynomial identity and should never run a Groebner engine.
        #
        # THE VERIFIER DOES NOT TRUST ITS OWN LIFT.  It expands what it got
        # back before recording anything, and a mismatch is reported rather
        # than smoothed over -- that is the case the expansion exists to catch.
        target = "(%s) - (%s)" % (c["lhs"], c["rhs"])
        why = ("(%s) - (%s) is nonzero in the polynomial ring but reduces to 0 "
               "modulo %s's ideal, so the rewriting holds in that coordinate "
               "ring and DERIVES from the model's own equations."
               % (c["lhs"], c["rhs"], c.get("model")))
        rep = (_backend or cas.SingularBackend(runner=_runner)).membership(
            ring, target, gens, characteristic=ch,
            timeout=timeout)
        if not rep["is_member"] or not rep["cofactors"]:
            # Reduction said 0 and the lift found nothing. That is not a
            # refutation, but a DERIVED verdict licenses transport and must
            # retain arithmetic a second checker can replay. Refuse authority
            # rather than persisting an unrecheckable backend assertion.
            return UNVERIFIED, why + (
                "\n  NO REPRESENTATION WAS RECOVERED. The reduction supports "
                "the identity but cannot license a persisted DERIVED verdict "
                "until its ideal-membership certificate is retained.")
        ok, expanded = (_backend or cas.SingularBackend(runner=_runner)).check_membership(
            ring, target, gens, rep["cofactors"],
            characteristic=ch,
            timeout=timeout)
        if not ok:
            return UNVERIFIED, (
                "the reduction said (%s) - (%s) lies in %s's ideal, and "
                "expanding the cofactors the CAS returned for it gives a "
                "difference of %s rather than 0.\n"
                "  The search and the arithmetic disagree, and the arithmetic "
                "is the half a reader can check. Nothing is recorded until "
                "they agree."
                % (c["lhs"], c["rhs"], c.get("model"), expanded))
        witness = " + ".join("(%s)*(%s)" % (b, f)
                             for b, f in zip(rep["cofactors"], gens))
        return DERIVED, why + (
            "\n  (%s) - (%s) = %s, expanded and confirmed WITHOUT recomputing "
            "a basis. The derivation is now an artifact rather than a report "
            "of one." % (c["lhs"], c["rhs"], witness)), {
                "cofactors": list(rep["cofactors"]),
                "generators": list(gens), "ring_vars": list(ring),
                "target": target}
    # THE REFUTATION IS THE ONE ANSWER AN UNRECORDED IDEAL CANNOT SUPPORT.
    if unrecorded:
        return UNVERIFIED, (
            "(%s) - (%s) is not identically zero in the polynomial ring, and "
            "%s records no ideal -- so whether the rewriting holds modulo this "
            "model's equations CANNOT BE DECIDED HERE.\n"
            "  This is not a refutation and must not be reported as one. The "
            "model may well impose equations that make it true; nobody wrote "
            "them down. If the model genuinely imposes none -- an identity in "
            "the polynomial ring, an SOS Gram relation -- declare "
            "`generators: []` and the same question becomes answerable, and "
            "the answer will be AMBIENT."
            % (c["lhs"], c["rhs"], c.get("model")))
    # A REFUTATION AT AN OPEN MODEL IS THE ONE A READER WILL ARGUE WITH, so
    # answer the argument here instead of leaving them to make it.
    #
    # `localize` emits a model carrying the SAME ideal plus `open_conditions`:
    # the restriction is a condition on POINTS and adds no equations.  So a
    # rewriting that only becomes true once f is inverted really is false at
    # this model, and a reader who expected otherwise wanted the OTHER
    # construction -- the saturation, where "some power of f kills it into I"
    # is precisely what membership means.  Both readings are defensible; only
    # one of them is the model in front of them, and the message should say
    # which.  (lean/GrandPortage/Localization.lean separates the two.)
    opens = [str(o) for o in (model.get("open_conditions") or [])]
    hint = "" if not opens else (
        "\n  NOTE THAT %s IS AN OPEN LOCUS, carrying the condition%s %s. That "
        "restricts its POINTS and adds no equations -- its ideal is the "
        "source's, unchanged -- so inverting %s is not available here. If the "
        "rewriting holds only after inverting it, the model you want is the "
        "closure of that open locus, whose ideal is the saturation; an "
        "identity there is DERIVED and does not transport back."
        % (c.get("model"), "" if len(opens) == 1 else "s",
           ", ".join(opens), opens[0]))
    return REFUTED, (
        "(%s) - (%s) does not reduce to 0 %s -- it reduces to %s.\n"
        "  THIS ONE IS A REFUTATION, unlike a failed containment. %s So the "
        "rewriting is false where it was claimed, and every transport that "
        "carried it carried something untrue.%s"
        % (c["lhs"], c["rhs"], modulo,
           (evidence or {}).get("reduced_modulo_ideal", "a nonzero form"),
           ("The claim is that the difference is identically zero, and that "
            "is decided by normalising it." if bare else
            "The claim is that the difference lies in the ideal, and "
            "reduction modulo a Groebner basis DECIDES ideal membership."),
           hint))


ISO_VERIFIED = "VERIFIED"
ISO_NOT_ISO = "NOT_AN_ISOMORPHISM"


def _check_mapped_ring_iso_certificate(certificate, ring, characteristic,
                                       source_generators, target_generators,
                                       forward, inverse):
    """Replay a closed mapped-ring-isomorphism proof by exact expansion."""
    if set(certificate) != {
            "schema", "forward_cofactors", "inverse_cofactors"}:
        return "the ring-isomorphism certificate has unknown or missing fields"
    if certificate.get("schema") != "mapped_ring_iso_v1":
        return "unsupported ring-isomorphism certificate schema %r" % (
            certificate.get("schema"),)
    forward_cofactors = certificate.get("forward_cofactors")
    inverse_cofactors = certificate.get("inverse_cofactors")
    if (not isinstance(forward_cofactors, list)
            or len(forward_cofactors) != len(target_generators)):
        return "the forward pullback certificate has the wrong generator count"
    if (not isinstance(inverse_cofactors, list)
            or len(inverse_cofactors) != len(source_generators)):
        return "the inverse pullback certificate has the wrong generator count"
    try:
        for generator, cofactors in zip(
                target_generators, forward_cofactors):
            pulled = G.substitute_polynomial(
                generator, ring, forward, characteristic,
                _preserve_sparse=True)
            G.check_membership_identity(
                pulled, source_generators, cofactors,
                ring, characteristic)
        for generator, cofactors in zip(
                source_generators, inverse_cofactors):
            pulled = G.substitute_polynomial(
                generator, ring, inverse, characteristic,
                _preserve_sparse=True)
            G.check_membership_identity(
                pulled, target_generators, cofactors,
                ring, characteristic)
        for variable in ring:
            inverse_then_forward = G.substitute_polynomial(
                G.substitute_polynomial(
                    variable, ring, inverse, characteristic),
                ring, forward, characteristic)
            if G.canonical_polynomial(
                    inverse_then_forward, ring, characteristic) != variable:
                return (
                    "the exact certificate maps fail the left inverse law "
                    "at %s" % variable)
            forward_then_inverse = G.substitute_polynomial(
                G.substitute_polynomial(
                    variable, ring, forward, characteristic),
                ring, inverse, characteristic)
            if G.canonical_polynomial(
                    forward_then_inverse, ring, characteristic) != variable:
                return (
                    "the exact certificate maps fail the right inverse law "
                    "at %s" % variable)
    except (G.CertificateError, KeyError, TypeError, ValueError, IndexError) as exc:
        return "the exact ring-isomorphism certificate was rejected: %s" % exc
    return None


def ring_iso(graph, eid, timeout=300, _runner=None, _backend=None):
    """Check an EQUIVALENCE's `ring_iso` against the maps, by reduction.

    THE MOST POWERFUL UNAUDITED BOOLEAN LEFT.  `ring_iso` is what licenses an
    IDENTITY to cross an EQUIVALENCE in either direction, and the kernel's own
    warning is that the evidence usually offered for it is the wrong kind:
    V(x^2) and V(x) have the same single solution and any converse you like,
    and `x = 0` holds in one coordinate ring and is false in the other.  Points
    do not give it.

    WHAT TO CHECK CAME FROM THE FORMALISATION.  `Reflects` -- the awkward half
    -- quantifies over preimages, which is not something a CAS can search for.
    But it is not primitive:

        PullsBack psi I J  and  psi . phi = id   ==>   Reflects phi I J

    so a verified isomorphism is four conditions a solver CAN check:

        forward   every target generator, pulled back by the point-forward
                  substitution, lies in the source ideal
        backward  every source generator, pulled back by the point-inverse
                  substitution, lies in the target ideal
        left      inverse(forward(x)) = x for every source variable
        right     forward(inverse(y)) = y for every target variable

    None is a search. All four are reductions or substitutions.

    `forward` follows the Lean and user-facing convention: it sends SOURCE
    points to TARGET points. Polynomial substitution is contravariant, hence
    the target generators are the ones reduced in the source ideal. The
    current executable surface requires both endpoints to use the same ring
    variable names; Graph.validate reports that limitation before verification.
    """
    e = graph.edges[eid]
    stale = _stale_endpoint(graph, eid)
    if stale:
        return UNVERIFIED, stale
    if e.get("type") != K.EQUIVALENCE:
        return UNVERIFIED, "edge %s is %s, not an EQUIVALENCE" % (
            eid, e.get("type"))
    fwd, inv = e.get("forward"), e.get("inverse")
    if not fwd or not inv:
        return UNVERIFIED, (
            "edge %s declares no `forward`/`inverse` substitutions, so there "
            "is nothing to reduce. `ring_iso` is a statement about the induced "
            "map on coordinate rings, and without the map it can only be "
            "taken on the author's word -- which is what it has been." % eid)
    src, dst = graph.models.get(e["src"]) or {}, graph.models.get(e["dst"]) or {}
    pending = _pending_ideal(e["src"], src) or _pending_ideal(e["dst"], dst)
    if pending:
        return UNVERIFIED, pending
    if src.get("generators") is None or dst.get("generators") is None:
        return UNVERIFIED, "one endpoint carries no ideal"
    ring = src.get("ring_vars") or []
    ch, missing = _declared_characteristic(e["src"], src)
    if missing:
        return UNVERIFIED, missing
    dst_ch, missing = _declared_characteristic(e["dst"], dst)
    if missing:
        return UNVERIFIED, missing
    if dst_ch != ch:
        return UNVERIFIED, (
            "the endpoints declare different characteristics (%s vs %s); a "
            "substitution between them is not a reduction in one ring"
            % (ch, dst_ch))
    if not ring or set(dst.get("ring_vars") or []) != set(ring):
        return UNVERIFIED, (
            "the two models are written in different rings; a substitution "
            "between them needs both variable lists to agree")

    certificate = e.get("ring_iso_certificate")
    if certificate is not None:
        certificate_problem = _check_mapped_ring_iso_certificate(
            certificate, ring, ch, list(src["generators"]),
            list(dst["generators"]), fwd, inv)
        if certificate_problem:
            return UNVERIFIED, (
                "%s. The authored maps may still be an isomorphism, but this "
                "proof does not establish it; invalid evidence is not a "
                "mathematical refutation." % certificate_problem)
        return ISO_VERIFIED, (
            "the mapped_ring_iso_v1 certificate exactly expands both ideal "
            "pullbacks and both polynomial map compositions are the identity. "
            "This backend-free proof establishes an isomorphism of the exact "
            "endpoint COORDINATE RINGS; it grants no authority outside them."
        )

    # A point-forward map F : src -> dst pulls target functions back to src.
    for g in dst["generators"]:
        _, ok = (_backend or cas.SingularBackend(runner=_runner)).pullback_reduce(
            ring, g, fwd, list(src["generators"]), characteristic=ch,
            timeout=timeout)
        if not ok:
            return ISO_NOT_ISO, (
                "target generator %r of %s does not pull back into %s's ideal "
                "under the point-forward map. The declared map therefore does "
                "not establish the required coordinate-ring homomorphism."
                % (g, e["dst"], e["src"]))
    # The point-inverse G : dst -> src pulls source functions back to dst.
    for g in src["generators"]:
        _, ok = (_backend or cas.SingularBackend(runner=_runner)).pullback_reduce(
            ring, g, inv, list(dst["generators"]), characteristic=ch,
            timeout=timeout)
        if not ok:
            return ISO_NOT_ISO, (
                "source generator %r of %s does not pull back into %s's ideal "
                "under the point-inverse map. Without that, transport in the "
                "reverse direction is not established."
                % (g, e["src"], e["dst"]))
    # both roundtrips: psi(phi(v)) = v and phi(psi(v)) = v
    for v in ring:
        once, _ = (_backend or cas.SingularBackend(runner=_runner)).pullback_reduce(ring, v, inv, [],
                                            characteristic=ch,
                                            timeout=timeout)
        twice, _ = (_backend or cas.SingularBackend(runner=_runner)).pullback_reduce(ring, once, fwd, [],
                                             characteristic=ch,
                                             timeout=timeout)
        if twice.replace(" ", "") != v:
            return ISO_NOT_ISO, (
                "`inverse(forward(%s))` does not reduce to %s, so `inverse` "
                "is not a left inverse. Both ideal checks can pass for a map "
                "that is not invertible, and then only one direction is "
                "licensed."
                % (v, v))
        once, _ = (_backend or cas.SingularBackend(runner=_runner)).pullback_reduce(ring, v, fwd, [],
                                            characteristic=ch,
                                            timeout=timeout)
        twice, _ = (_backend or cas.SingularBackend(runner=_runner)).pullback_reduce(ring, once, inv, [],
                                             characteristic=ch,
                                             timeout=timeout)
        if twice.replace(" ", "") != v:
            return ISO_NOT_ISO, (
                "`forward(inverse(%s))` does not reduce to %s, so `inverse` "
                "is not a right inverse. A mapped equivalence requires both "
                "compositions, exactly as MappedEquivalence.lean does."
                % (v, v))
    return ISO_VERIFIED, (
        "the point-forward map sends %s to %s, its pullback carries the target "
        "ideal into the source ideal, the point-inverse establishes the reverse "
        "direction, and both compositions are the identity on every variable. "
        "That is "
        "an isomorphism of COORDINATE RINGS, which is what an IDENTITY needs "
        "and what a bijection on points does not give."
        % (e["src"], e["dst"]))


OP_SOUND = "VERIFIED"
OP_UNSOUND = "NOT_THE_STATED_OUTPUT"
_MAX_SATURATION_POWER = 8


def operation_output(graph, eid, timeout=300, _runner=None, _backend=None):
    """Is a constructed model's ideal actually what the operation claims?

    THE LAST OUTPUT NOBODY CHECKED.  `decompose` proves its cover, membership
    carries cofactors, a witness gets substituted -- but `saturate_closure` and
    `eliminate` emitted a program, and whatever came back was recorded as the
    target's ideal on the strength of having asked the right question.

    WHAT IS CHECKABLE AND WHAT IS NOT, stated plainly because the difference
    decides what this verdict is worth.

      TOO BIG    every generator the output claims is genuinely there. CHEAP,
                 and it is the dangerous direction: an ideal with something
                 extra cuts out a SMALLER variety, and a smaller variety makes
                 EMPTY claims -- the ones that carry certificates and scope --
                 unsound.
      TOO SMALL  the output is ALL of what it should be. Not checked. This is
                 the completeness direction, it is as hard as recomputing the
                 answer, and getting it wrong yields a LOOSER model: sound for
                 EMPTY, unsound for NONEMPTY.

    So a VERIFIED here means "nothing was invented", not "nothing was missed",
    and the message says so rather than letting a reader assume the stronger
    reading.

    Both checks are certifying: they return the cofactors, so a second checker
    can expand `g = sum b_i f_i` without recomputing an elimination or a
    saturation.
    """
    e = graph.edges.get(eid)
    if not e:
        return UNVERIFIED, "no such edge", None
    stale = _stale_endpoint(graph, eid)
    if stale:
        return UNVERIFIED, stale, None
    kind = e.get("built_by_operation")
    if kind not in ("SaturateClosure", "Eliminate"):
        return UNVERIFIED, (
            "edge %s was not built by an operation whose output this can "
            "check" % eid), None
    # The constructed model is the edge's SRC for a saturation (it is tighter)
    # and its DST for an elimination (the projection is looser).
    built_id = e["src"] if kind == "SaturateClosure" else e["dst"]
    source_id = e["dst"] if kind == "SaturateClosure" else e["src"]
    built = graph.models.get(built_id) or {}
    source = graph.models.get(source_id) or {}
    for mid, m in ((built_id, built), (source_id, source)):
        p = _pending_ideal(mid, m)
        if p:
            return UNVERIFIED, p, None
        if m.get("generators") is None:
            return UNVERIFIED, (
                "%s records no ideal, so there is nothing to check the "
                "operation's output against" % mid), None
    ring = source.get("ring_vars") or []
    if not ring:
        return UNVERIFIED, "%s declares no ring variables" % source_id, None
    ch, missing = _declared_characteristic(source_id, source)
    if missing:
        return UNVERIFIED, missing, None
    built_ch, missing = _declared_characteristic(built_id, built)
    if missing:
        return UNVERIFIED, missing, None
    if built_ch != ch:
        return UNVERIFIED, (
            "%s and %s declare different characteristics (%s vs %s); an "
            "operation output must be checked in the ring where it was built"
            % (source_id, built_id, ch, built_ch)), None
    src_gens = list(source["generators"])
    cofactors, bad, inconclusive = {}, [], []

    if kind == "Eliminate":
        # THE TWO SORTS MUST REALLY BE THE DECLARED COORDINATE PARTITION.
        # An empty generator list otherwise passes every local membership and
        # expressibility check vacuously without establishing that the target
        # is even the retained-coordinate ring of the source.
        kept = built.get("ring_vars") or []
        eliminated = built.get("eliminated")
        if (not isinstance(eliminated, list) or not eliminated
                or len(eliminated) != len(set(eliminated))
                or any(v not in ring for v in eliminated)):
            return UNVERIFIED, (
                "%s does not record a valid nonempty eliminated-variable "
                "subset of %s's ring" % (built_id, source_id)), None
        expected_kept = [v for v in ring if v not in set(eliminated)]
        if kept != expected_kept:
            return UNVERIFIED, (
                "%s declares retained variables %s, but removing %s from "
                "%s's ordered ring leaves %s"
                % (built_id, kept, eliminated, source_id, expected_kept)), None
        # AN ELIMINATION IDEAL IS `I cap k[remaining]`, so each generator owes
        # two things: membership in I, and expressibility after the
        # projection. The second is the same condition
        # INEXPRESSIBLE-CONCLUSION checks on claims, asked here of an ideal.
        kept = built.get("ring_vars") or []
        for g in built["generators"]:
            foreign = cas.foreign_symbols(kept, g)
            if foreign:
                bad.append("%s names %s, which the projection removed"
                           % (g, ", ".join(foreign)))
                continue
            rep = (_backend or cas.SingularBackend(runner=_runner)).membership(
                ring, g, src_gens, characteristic=ch, timeout=timeout)
            if not rep["is_member"]:
                bad.append("%s is not in %s's ideal (it reduces to %s)"
                           % (g, source_id, rep["reduced"]))
            else:
                cofactors[g] = rep["cofactors"]
    else:
        f = built.get("saturated_at")
        if not f:
            return UNVERIFIED, (
                "%s does not record what it was saturated at, so `I : f^oo` "
                "names no f" % built_id), None
        for g in built["generators"]:
            # SEARCH FOR THE POWER, then CERTIFY it. `g in I : f^oo` means some
            # power of f carries g into I; the certificate is that n together
            # with the cofactors, and a checker then expands one identity
            # instead of redoing a saturation.
            found = None
            for n in range(_MAX_SATURATION_POWER + 1):
                target = g if n == 0 else "(%s)^%d*(%s)" % (f, n, g)
                rep = (_backend or cas.SingularBackend(runner=_runner)).membership(
                    ring, target, src_gens, characteristic=ch, timeout=timeout)
                if rep["is_member"]:
                    found = (n, rep["cofactors"])
                    break
            if found is None:
                inconclusive.append(
                    "no power of %s up to %d carries %s into %s's ideal"
                    % (f, _MAX_SATURATION_POWER, g, source_id))
            else:
                cofactors["(%s)^%d*(%s)" % (f, found[0], g)] = found[1]

    if inconclusive:
        return UNVERIFIED, (
            "%s's saturation output was not certified: %s. This is a bounded "
            "witness search, not a non-membership proof; a valid saturation "
            "witness may require a larger exponent. Recompute the saturation "
            "or supply an explicit witness rather than treating the search "
            "bound as a refutation."
            % (built_id, "; ".join(inconclusive))), None
    if bad:
        return OP_UNSOUND, (
            "%s's ideal is not the %s it is recorded as: %s.\n"
            "  This is the dangerous direction. An ideal carrying something "
            "it should not cuts out a SMALLER variety, and a smaller variety "
            "makes EMPTY claims -- the ones that carry certificates and derive "
            "scope -- unsound."
            % (built_id, kind, "; ".join(bad))), None
    if kind == "SaturateClosure":
        established = (
            "every generator g of %s's ideal has a certified saturation "
            "witness: for some n, (%s)^n*g lies in %s's ideal (%s). Thus the "
            "SaturateClosure invented nothing.\n"
            % (built_id, built.get("saturated_at"), source_id,
               ", ".join(sorted(cofactors))))
    else:
        established = (
            "every generator of %s's elimination ideal belongs to %s's ideal "
            "and uses only the retained variables, so Eliminate invented "
            "nothing.\n" % (built_id, source_id))
    return OP_SOUND, (established +
        "  NOTE WHAT THIS DOES NOT SAY: that the output is COMPLETE. Whether "
        "the operation missed something is the other direction, it is as hard "
        "as recomputing the answer, and it is not checked here. A missed "
        "generator yields a LOOSER model -- still sound for EMPTY, unsound "
        "for NONEMPTY."), {
            "cofactors": [cofactors[k] for k in sorted(cofactors)],
            "targets": sorted(cofactors), "generators": src_gens,
            "ring_vars": list(ring),
            "target_ring_vars": list(built.get("ring_vars") or []),
            "eliminated": list(built.get("eliminated") or [])}


SECTION_VERIFIED = "VERIFIED_SECTION"
SECTION_REJECTED = "CERTIFICATE_REJECTED"
GROEBNER_VERIFIED = "VERIFIED_GROEBNER"
GROEBNER_REJECTED = "GROEBNER_CERTIFICATE_REJECTED"
POINT_LIFT_VERIFIED = "VERIFIED_POINT_LIFT"
POINT_LIFT_REJECTED = "POINT_LIFT_CERTIFICATE_REJECTED"


def elimination_section(graph, eid, section, timeout=300, _runner=None,
                        _backend=None):
    """Check a polynomial retraction proving elimination completeness.

    The ordinary operation verifier proves that every recorded target
    generator came from the source ideal. This checker proves the independent
    reverse inclusion: substitute polynomial images for eliminated variables,
    fix retained variables literally, and certify that every source generator
    lands in the recorded target ideal. Together those two certificates give
    exact contraction. The same polynomial retraction also gives an explicit
    lift of every target-valued point over the declared coefficient algebra.
    """
    e = graph.edges.get(eid)
    if not e or e.get("built_by_operation") != "Eliminate":
        return UNVERIFIED, (
            "edge %s is not a constructor-built Eliminate edge" % eid), None
    stale = _stale_endpoint(graph, eid)
    if stale:
        return UNVERIFIED, stale, None
    source = graph.models.get(e.get("src")) or {}
    target = graph.models.get(e.get("dst")) or {}
    for mid, model in ((e.get("src"), source), (e.get("dst"), target)):
        pending = _pending_ideal(mid, model)
        if pending:
            return UNVERIFIED, pending, None
        if model.get("generators") is None:
            return UNVERIFIED, (
                "%s records no ideal, so a section cannot be checked" % mid
            ), None
    source_ring = source.get("ring_vars") or []
    target_ring = target.get("ring_vars") or []
    eliminated = target.get("eliminated")
    if (not source_ring or not isinstance(eliminated, list)
            or not eliminated or len(eliminated) != len(set(eliminated))
            or any(variable not in source_ring for variable in eliminated)):
        return UNVERIFIED, (
            "%s does not record a valid nonempty eliminated-variable subset"
            % e.get("dst")), None
    expected_target = [v for v in source_ring if v not in set(eliminated)]
    if target_ring != expected_target:
        return UNVERIFIED, (
            "%s's retained ring %s is not the ordered complement %s"
            % (e.get("dst"), target_ring, expected_target)), None
    source_ch, missing = _declared_characteristic(e.get("src"), source)
    if missing:
        return UNVERIFIED, missing, None
    target_ch, missing = _declared_characteristic(e.get("dst"), target)
    if missing:
        return UNVERIFIED, missing, None
    if source_ch != target_ch:
        return UNVERIFIED, (
            "the elimination endpoints have different characteristics"
        ), None
    if not isinstance(section, dict) or set(section) != set(eliminated):
        return SECTION_REJECTED, (
            "a polynomial section must give exactly the eliminated variables "
            "%s; got %s" % (eliminated, sorted(section) if isinstance(
                section, dict) else type(section).__name__)), None
    for variable in eliminated:
        image = section.get(variable)
        if not isinstance(image, str) or not image.strip():
            return SECTION_REJECTED, (
                "the image of %s must be a nonempty polynomial string"
                % variable), None
        foreign = cas.foreign_symbols(target_ring, image)
        if foreign:
            return SECTION_REJECTED, (
                "the proposed image %s -> %s names %s outside the retained "
                "ring" % (variable, image, ", ".join(foreign))), None

    images = dict((v, v) for v in target_ring)
    images.update((v, section[v]) for v in eliminated)
    # The backend map is simultaneous, but its image list must follow the
    # source-ring order. A sequential substitution silently breaks swaps and
    # nonlinear sections.
    images = dict((v, images[v]) for v in source_ring)
    backend = _backend or cas.SingularBackend(runner=_runner)
    target_generators = list(target["generators"])
    rows = []
    for generator in source["generators"]:
        substituted, _ = backend.pullback_reduce(
            source_ring, generator, images, generators=[],
            characteristic=source_ch, timeout=timeout)
        foreign = cas.foreign_symbols(target_ring, substituted)
        if foreign:
            return SECTION_REJECTED, (
                "substituting into %s produced %s, which still names %s "
                "outside the retained ring"
                % (generator, substituted, ", ".join(foreign))), None
        if not target_generators:
            if substituted.replace(" ", "") != "0":
                return SECTION_REJECTED, (
                    "the proposed section sends source generator %s to %s, "
                    "not to zero in the recorded zero target ideal"
                    % (generator, substituted)), None
            cofactors = []
        else:
            membership = backend.membership(
                target_ring, substituted, target_generators,
                characteristic=source_ch, timeout=timeout)
            if not membership["is_member"]:
                return SECTION_REJECTED, (
                    "the proposed section sends source generator %s to %s, "
                    "which is not in the target ideal (remainder %s)"
                    % (generator, substituted, membership["reduced"])), None
            cofactors = list(membership["cofactors"])
            bad_cofactors = cas.foreign_symbols(target_ring, *cofactors)
            if bad_cofactors:
                return SECTION_REJECTED, (
                    "the membership cofactors name %s outside the retained "
                    "ring" % ", ".join(bad_cofactors)), None
            ok, expanded = backend.check_membership(
                target_ring, substituted, target_generators, cofactors,
                characteristic=source_ch, timeout=timeout)
            if not ok:
                return SECTION_REJECTED, (
                    "the membership search returned cofactors for %s, but "
                    "independent expansion produced %s"
                    % (substituted, expanded)), None
        rows.append({
            "source_generator": generator,
            "substituted": substituted,
            "cofactors": cofactors,
        })

    representation = {
        "method": "polynomial_section_v1",
        "section": dict((v, section[v]) for v in eliminated),
        "source_ring_vars": list(source_ring),
        "target_ring_vars": list(target_ring),
        "eliminated": list(eliminated),
        "source_generators": list(source["generators"]),
        "target_generators": target_generators,
        "images": images,
        "rows": rows,
    }
    return SECTION_VERIFIED, (
        "the simultaneous polynomial section fixes every retained variable "
        "and sends every source generator into the recorded target ideal; "
        "expanded cofactors independently confirm each membership. This "
        "establishes contraction completeness and gives an explicit "
        "polynomial lift of every target-valued point. Combined with VERIFIED "
        "operation output it yields exact contraction and point-surjective "
        "image authority over the declared coefficient algebra."
    ), representation

def elimination_piecewise_lift(graph, eid, certificate, timeout=300,
                               _runner=None, _backend=None):
    """Check a finite rational-chart cover giving every target point a lift.

    Each open chart uses one nonzero polynomial guard and writes every
    eliminated coordinate as a numerator divided by a power of that guard.
    A final polynomial fallback applies when every guard is zero. Coverage is
    therefore a field tautology; exact membership identities prove that every
    chart formula lands in the source model. This authority is independent of
    contraction completeness.
    """
    e = graph.edges.get(eid)
    if not e or e.get("built_by_operation") != "Eliminate":
        return UNVERIFIED, (
            "edge %s is not a constructor-built Eliminate edge" % eid), None
    stale = _stale_endpoint(graph, eid)
    if stale:
        return UNVERIFIED, stale, None
    source_id, target_id = e.get("src"), e.get("dst")
    source = graph.models.get(source_id) or {}
    target = graph.models.get(target_id) or {}
    for mid, model in ((source_id, source), (target_id, target)):
        pending = _pending_ideal(mid, model)
        if pending:
            return UNVERIFIED, pending, None
        if model.get("generators") is None:
            return UNVERIFIED, (
                "%s records no ideal, so point lifts cannot be checked" % mid
            ), None
    source_ring = source.get("ring_vars") or []
    target_ring = target.get("ring_vars") or []
    eliminated = target.get("eliminated")
    if (not source_ring or not isinstance(eliminated, list)
            or not eliminated or len(eliminated) != len(set(eliminated))
            or any(variable not in source_ring for variable in eliminated)):
        return UNVERIFIED, (
            "%s does not record a valid nonempty eliminated-variable subset"
            % target_id), None
    expected_target = [v for v in source_ring if v not in set(eliminated)]
    if target_ring != expected_target:
        return UNVERIFIED, (
            "%s's retained ring %s is not the ordered complement %s"
            % (target_id, target_ring, expected_target)), None
    source_ch, missing = _declared_characteristic(source_id, source)
    if missing:
        return UNVERIFIED, missing, None
    target_ch, missing = _declared_characteristic(target_id, target)
    if missing:
        return UNVERIFIED, missing, None
    if source_ch != target_ch:
        return UNVERIFIED, (
            "the elimination endpoints have different characteristics"), None
    exact_domain = "Q" if source_ch == 0 else "F_%s" % source_ch
    declared_domains = [
        S.declared_coefficient_domain(model)
        for model in (source, target)
    ]
    if any(value is not None and value != exact_domain
           for value in declared_domains):
        return UNVERIFIED, (
            "piecewise rational lifting is checked over %s, but an endpoint "
            "declares %r" % (exact_domain, declared_domains)), None

    if not isinstance(certificate, dict) or set(certificate) != {
            "charts", "fallback"}:
        return POINT_LIFT_REJECTED, (
            "a point-lift certificate must contain exactly charts and fallback"
        ), None
    charts = certificate.get("charts")
    fallback = certificate.get("fallback")
    if (not isinstance(charts, list) or len(charts) > 16
            or not isinstance(fallback, dict)
            or set(fallback) != {"lift"}):
        return POINT_LIFT_REJECTED, (
            "charts must be a list of at most 16 open charts and fallback "
            "must contain exactly one lift"), None

    backend = _backend or cas.SingularBackend(runner=_runner)
    target_generators = list(target["generators"])

    def checked_lift(raw, rational):
        if not isinstance(raw, dict) or set(raw) != set(eliminated):
            raise G.CertificateError(
                "a chart lift must give exactly the eliminated variables %s"
                % eliminated
            )
        normalized = {}
        for variable in eliminated:
            value = raw[variable]
            if rational:
                if not isinstance(value, dict) or set(value) != {
                        "numerator", "denominator_power"}:
                    raise G.CertificateError(
                        "the rational lift of %s needs numerator and "
                        "denominator_power" % variable
                    )
                normalized[variable] = {
                    "numerator": G.canonical_polynomial(
                        value["numerator"], target_ring, source_ch),
                    "denominator_power": value["denominator_power"],
                }
            else:
                normalized[variable] = G.canonical_polynomial(
                    value, target_ring, source_ch)
        return normalized

    def membership(target_expression, generators):
        canonical_target = G.canonical_polynomial(
            target_expression, target_ring, source_ch)
        if not generators:
            if canonical_target != "0":
                return None
            return []
        found = backend.membership(
            target_ring, canonical_target, generators,
            characteristic=source_ch, timeout=timeout)
        if not found["is_member"]:
            return None
        cofactors = list(found["cofactors"])
        G.check_membership_identity(
            canonical_target, generators, cofactors, target_ring, source_ch
        )
        return cofactors

    normalized_charts = []
    guards = []
    try:
        for index, chart in enumerate(charts):
            if not isinstance(chart, dict) or set(chart) != {"guard", "lift"}:
                raise G.CertificateError(
                    "chart %d must contain exactly guard and lift" % index
                )
            guard = G.canonical_polynomial(
                chart["guard"], target_ring, source_ch
            )
            if guard == "0":
                raise G.CertificateError("chart %d has the zero guard" % index)
            if guard in guards:
                raise G.CertificateError("chart guards must be distinct")
            guards.append(guard)
            lift = checked_lift(chart["lift"], True)
            images = dict((name, {
                "numerator": name, "denominator_power": 0,
            }) for name in target_ring)
            images.update(lift)
            images = dict((name, images[name]) for name in source_ring)
            rows = []
            for generator in source["generators"]:
                numerator, denominator_power = G.guarded_rational_substitute(
                    generator, source_ring, target_ring, images, guard,
                    source_ch,
                )
                cofactors = None
                vanishing_power = None
                localization_power = None
                membership_target = None
                for radical_power in range(1, 5):
                    powered = G.multiply_polynomial_power(
                        "1", numerator, radical_power, target_ring, source_ch
                    )
                    for power in range(9):
                        candidate = G.multiply_polynomial_power(
                            powered, guard, power, target_ring, source_ch
                        )
                        cofactors = membership(candidate, target_generators)
                        if cofactors is not None:
                            vanishing_power = radical_power
                            localization_power = power
                            membership_target = candidate
                            break
                    if cofactors is not None:
                        break
                if cofactors is None:
                    return POINT_LIFT_REJECTED, (
                        "chart %d does not send source generator %s to zero "
                        "on guard %s within the bounded localization check"
                        % (index, generator, guard)), None
                rows.append({
                    "source_generator": generator,
                    "numerator": numerator,
                    "denominator_power": denominator_power,
                    "vanishing_power": vanishing_power,
                    "localization_power": localization_power,
                    "membership_target": membership_target,
                    "membership_generators": list(target_generators),
                    "cofactors": cofactors,
                })
            normalized_charts.append({
                "guard": guard, "lift": lift, "rows": rows,
            })

        fallback_lift = checked_lift(fallback["lift"], False)
        fallback_images = dict((name, {
            "numerator": name, "denominator_power": 0,
        }) for name in target_ring)
        fallback_images.update(dict((name, {
            "numerator": value, "denominator_power": 0,
        }) for name, value in fallback_lift.items()))
        fallback_images = dict(
            (name, fallback_images[name]) for name in source_ring
        )
        fallback_generators = target_generators + guards
        fallback_rows = []
        for generator in source["generators"]:
            numerator, denominator_power = G.guarded_rational_substitute(
                generator, source_ring, target_ring, fallback_images, "1",
                source_ch,
            )
            cofactors = None
            vanishing_power = None
            membership_target = None
            for radical_power in range(1, 5):
                candidate = G.multiply_polynomial_power(
                    "1", numerator, radical_power, target_ring, source_ch
                )
                cofactors = membership(candidate, fallback_generators)
                if cofactors is not None:
                    vanishing_power = radical_power
                    membership_target = candidate
                    break
            if cofactors is None:
                return POINT_LIFT_REJECTED, (
                    "the fallback does not send source generator %s to zero "
                    "where every chart guard vanishes within the bounded "
                    "radical check" % generator), None
            fallback_rows.append({
                "source_generator": generator,
                "numerator": numerator,
                "denominator_power": denominator_power,
                "vanishing_power": vanishing_power,
                "localization_power": 0,
                "membership_target": membership_target,
                "membership_generators": list(fallback_generators),
                "cofactors": cofactors,
            })
    except (G.CertificateError, KeyError, TypeError, ValueError) as exc:
        return POINT_LIFT_REJECTED, str(exc), None

    representation = {
        "method": "piecewise_rational_lift_v1",
        "edge": eid,
        "source_model": source_id,
        "target_model": target_id,
        "characteristic": source_ch,
        "source_ring_vars": list(source_ring),
        "target_ring_vars": list(target_ring),
        "eliminated": list(eliminated),
        "source_generators": list(source["generators"]),
        "target_generators": target_generators,
        "charts": normalized_charts,
        "fallback": {"lift": fallback_lift, "rows": fallback_rows},
    }
    return POINT_LIFT_VERIFIED, (
        "the %d principal-open rational lift chart(s) and final all-guards-zero "
        "fallback cover every %s-valued target point. Exact expanded "
        "membership identities show every partial lift lands in the source, "
        "so the elimination projection is point-surjective independently of "
        "contraction completeness." % (len(charts), exact_domain)
    ), representation

def elimination_groebner(graph, eid, certificate):
    """Check a backend-neutral Gröbner certificate against one exact edge.

    The pure checker establishes contraction completeness only. It deliberately
    does not run Singular, persist a verdict, or grant geometric point-closure
    authority. Exact contraction additionally needs the independent current
    operation-output verdict proving no equation was invented.
    """
    e = graph.edges.get(eid)
    if not e or e.get("built_by_operation") != "Eliminate":
        return UNVERIFIED, (
            "edge %s is not a constructor-built Eliminate edge" % eid
        ), None
    stale = _stale_endpoint(graph, eid)
    if stale:
        return UNVERIFIED, stale, None
    source_id, target_id = e.get("src"), e.get("dst")
    source = graph.models.get(source_id) or {}
    target = graph.models.get(target_id) or {}
    for mid, model in ((source_id, source), (target_id, target)):
        pending = _pending_ideal(mid, model)
        if pending:
            return UNVERIFIED, pending, None
        if model.get("generators") is None:
            return UNVERIFIED, (
                "%s records no ideal, so a Gröbner certificate cannot be "
                "bound to it" % mid
            ), None
    source_ring = source.get("ring_vars") or []
    target_ring = target.get("ring_vars") or []
    eliminated = target.get("eliminated")
    if (not source_ring or not isinstance(eliminated, list)
            or not eliminated or len(eliminated) != len(set(eliminated))
            or any(variable not in source_ring for variable in eliminated)):
        return UNVERIFIED, (
            "%s does not record a valid nonempty eliminated-variable subset"
            % target_id
        ), None
    eliminated_set = set(eliminated)
    ordered_eliminated = [
        variable for variable in source_ring if variable in eliminated_set
    ]
    ordered_retained = [
        variable for variable in source_ring if variable not in eliminated_set
    ]
    if target_ring != ordered_retained:
        return UNVERIFIED, (
            "%s's retained ring %s is not the ordered complement %s"
            % (target_id, target_ring, ordered_retained)
        ), None
    source_ch, missing = _declared_characteristic(source_id, source)
    if missing:
        return UNVERIFIED, missing, None
    target_ch, missing = _declared_characteristic(target_id, target)
    if missing:
        return UNVERIFIED, missing, None
    if source_ch != target_ch:
        return UNVERIFIED, (
            "the elimination endpoints have different characteristics"
        ), None
    exact_domain = "Q" if source_ch == 0 else "F_%d" % source_ch
    for mid, model in ((source_id, source), (target_id, target)):
        declared = S.declared_coefficient_domain(model)
        if declared is not None and declared != exact_domain:
            return UNVERIFIED, (
                "%s declares coefficient field %r, but this certificate "
                "checker proves polynomial identities only over %s"
                % (mid, declared, exact_domain)
            ), None
    try:
        G.preflight_certificate(certificate)
    except G.CertificateError as exc:
        return GROEBNER_REJECTED, str(exc), None
    try:
        proof = json.loads(json.dumps(
            certificate, sort_keys=True, separators=(",", ":")
        ))
    except (TypeError, ValueError, RecursionError, MemoryError) as exc:
        return GROEBNER_REJECTED, (
            "certificate is not a bounded JSON proof object: %s" % exc
        ), None
    expected = {
        "characteristic": source_ch,
        "ring_vars": ordered_eliminated + ordered_retained,
        "eliminated": ordered_eliminated,
        "source_generators": list(source["generators"]),
        "target_generators": list(target["generators"]),
    }
    mismatches = [
        field for field, value in expected.items()
        if proof.get(field) != value
    ]
    if mismatches:
        return GROEBNER_REJECTED, (
            "the certificate does not belong to edge %s: %s differ from the "
            "exact ordered graph inputs"
            % (eid, ", ".join(mismatches))
        ), None
    try:
        checked = G.check_elimination_certificate(proof)
    except G.CertificateError as exc:
        return GROEBNER_REJECTED, str(exc), None
    representation = {
        "method": "groebner_elimination_v1",
        "edge": eid,
        "source_model": source_id,
        "target_model": target_id,
        "proof": proof,
        "checked": checked,
    }
    return GROEBNER_VERIFIED, (
        "the exact polynomial checker verified each recorded source "
        "generator's basis-span identity, "
        "all %d bounded critical-pair representations, the pure-lex "
        "elimination order, and every retained-basis membership in the "
        "recorded target ideal. This proves contraction completeness: the "
        "intersection of I(source) with %s is contained in I(target). "
        "Exact contraction still requires the independent current "
        "no-invention verdict; this does not establish "
        "geometric point-image closure."
        % (checked["critical_pair_count"], target_ring)
    ), representation

COVERS = "VERIFIED"
NOT_EXHAUSTIVE = "NOT_EXHAUSTIVE"
NOT_GEOMETRICALLY_EXHAUSTIVE = "NOT_GEOMETRICALLY_EXHAUSTIVE"


def partition_exhaustiveness(graph, pid, timeout=300, _runner=None, _backend=None):
    """Do the branches actually cover the parent?

    THE STORE SAID THIS WAS OUT OF REACH: "The checker cannot verify that gamma
    in {2,3,4} really matches three branches -- that is mathematics."  It is
    mathematics and it is decidable, and the sentence was written before the
    models carried ideals to decide it with.

    WHY THIS ONE MATTERS MORE THAN THE OTHER VERIFIERS.  Every other verdict is
    about a single object: a rewriting that does not hold, a point that is not
    on the variety, a certificate that is not what it says.  A false
    exhaustiveness is about the SPACE BETWEEN objects.  Each branch stays
    individually correct, every computation on it stays sound, and the argument
    is still broken -- because "these are all the cases" was the premise, and
    it was the one thing nobody could check.

    That is also why it is invisible by construction.  A hole in a case
    analysis produces no wrong answer anywhere; it produces a missing question.

        VERIFIED         every generator common to all branches vanishes on the
                         parent, so the parent is inside their union
        NOT_GEOMETRICALLY_EXHAUSTIVE
                         one does not, and it is NAMED. This proves a hole over
                         the algebraic closure, not necessarily over the
                         declared base field
        UNVERIFIED       an ideal is missing, so the question cannot be put
    """
    p = graph.partitions.get(pid)
    if not p:
        return UNVERIFIED, "no such partition"
    parent = graph.models.get(p.get("parent"))
    if not parent:
        return UNVERIFIED, "partition %s names no declared parent" % pid
    pending = _pending_ideal(p.get("parent"), parent)
    if pending:
        return UNVERIFIED, pending
    if parent.get("generators") is None:
        return UNVERIFIED, (
            "parent %s records no ideal. Whether the branches cover it is a "
            "question about its solution set, and this graph does not say what "
            "that set is." % p.get("parent"))
    ring = parent.get("ring_vars") or []
    if not ring:
        return UNVERIFIED, "parent %s declares no ring variables" % p["parent"]
    ch, missing = _declared_characteristic(p.get("parent"), parent)
    if missing:
        return UNVERIFIED, missing
    branch_gens = []
    parent_scope = S.point_scope(parent)
    for bid in p.get("branches") or []:
        b = graph.models.get(bid)
        if not b:
            return UNVERIFIED, "branch %s is not a declared model" % bid
        bp = _pending_ideal(bid, b)
        if bp:
            return UNVERIFIED, bp
        if b.get("generators") is None:
            return UNVERIFIED, (
                "branch %s records no ideal, so the union the branches form "
                "is not something this graph can compute" % bid)
        # A BRANCH IN A DIFFERENT RING IS NOT A BRANCH. The union only makes
        # sense inside one ambient space, and comparing ideals across two would
        # produce a confident answer about neither.
        if (b.get("ring_vars") or []) != ring:
            return UNVERIFIED, (
                "branch %s lives in k[%s] and the parent in k[%s]. A case "
                "split does not change coordinates; if this one does, it is a "
                "map and wants an edge."
                % (bid, ", ".join(b.get("ring_vars") or []), ", ".join(ring)))
        branch_ch, missing = _declared_characteristic(bid, b)
        if missing:
            return UNVERIFIED, missing
        if branch_ch != ch:
            return UNVERIFIED, (
                "branch %s declares characteristic %s and the parent %s"
                % (bid, branch_ch, ch))
        branch_gens.append(list(b["generators"]))
        branch_scope = S.point_scope(b)
        if branch_scope != parent_scope:
            return UNVERIFIED, (
                "branch %s has point scope %r and the parent %r. A partition "
                "is a cover inside one coefficient domain and point universe; "
                "changing either requires a separately typed map."
                % (bid, branch_scope, parent_scope))
    if not branch_gens:
        return UNVERIFIED, "partition %s lists no branches" % pid
    # A PARENT WITH NO POINTS IS COVERED BY ANYTHING, including nothing.
    #
    # `empty_parent_covered` in lean/GrandPortage/Exhaustive.lean is two lines
    # and it is the whole engine of the counterexample below. If the parent's
    # ideal is the UNIT IDEAL it has no points over ANY field, so the cover is
    # vacuous and no amount of branch arithmetic can refute it.
    unit = (_backend or cas.SingularBackend(runner=_runner)).membership(
        ring, "1", list(parent["generators"]), characteristic=ch,
        timeout=timeout)
    if unit["is_member"]:
        return COVERS, (
            "%s's ideal is the UNIT IDEAL, so it has no points over any field "
            "and the branches cover it vacuously. Nothing about the branches "
            "was needed, or could have refuted this." % p.get("parent"))
    covered, ev = (_backend or cas.SingularBackend(runner=_runner)).partition_cover(
        ring, list(parent["generators"]), branch_gens,
        characteristic=ch, timeout=timeout)
    named = ", ".join(p.get("branches") or [])
    if covered:
        return COVERS, (
            "every point of %s lies on one of %s%s. The case analysis is "
            "COMPLETE, and that is now a computed fact rather than a declared "
            "one."
            % (p.get("parent"), named,
               " -- " + ev["why"] if ev.get("why") else ""))
    # WHAT A FAILING IDEAL TEST ACTUALLY ESTABLISHES, and it is less than the
    # first version of this message claimed.
    #
    # The criterion is equivalent to the covering by the NULLSTELLENSATZ, which
    # needs an ALGEBRAICALLY CLOSED FIELD. This tool works over Q. Only one
    # direction survives that, and it is the one soundness needs: if the test
    # PASSES the cover really does hold, over any field, because "vanishes
    # wherever the parent does" is field-independent.
    #
    # If it FAILS, what has been shown is a point of V(parent) OVER THE
    # CLOSURE that no branch reaches. Over the base field that point may not
    # exist -- `(x^2+1)` over Q has none -- in which case the branches cover
    # the parent vacuously and this verdict, at UNSOUND_PREMISE, would be
    # calling a sound case analysis broken.
    #
    # SAME SHAPE AS THE IMAGE_CLOSURE DENSITY ARGUMENT: a justification correct
    # over an algebraically closed field, applied by a tool working over Q.
    # Twice now, which makes it a class rather than an accident.
    if (S.declared_point_universe(parent)
            == S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE):
        return NOT_EXHAUSTIVE, (
            "the branches %s do not cover %s in its DECLARED point universe "
            "%s: %s vanishes wherever all branches do and not on the parent. "
            "Because the model explicitly interprets points over the "
            "algebraic closure, this is a refuted exhaustiveness premise, not "
            "merely a possible geometric hole."
            % (named, p.get("parent"),
               S.ALGEBRAIC_CLOSURE_POINT_UNIVERSE,
               ", ".join(ev["uncovered"])))

    return NOT_GEOMETRICALLY_EXHAUSTIVE, (
        "the branches %s do not cover %s OVER THE ALGEBRAIC CLOSURE: %s "
        "vanishes wherever all of them do and does not vanish on the parent.\n"
        "  THIS IS A HOLE IN THE CASE ANALYSIS, not an error in any branch. "
        "Each branch may be perfectly correct and every computation on it "
        "sound; what is false is the premise that they are all the cases.\n"
        "  ONE WAY OUT THAT IS NOT A FIX: if %s has NO POINTS OVER THE BASE "
        "FIELD, the branches cover it vacuously and this verdict is about a "
        "point that does not exist there. The test cannot decide that -- it is "
        "the emptiness question, and it wants a certificate. Record the "
        "emptiness and the case analysis is moot; the graph is the place to "
        "settle which of the two you have."
        % (named, p.get("parent"), ", ".join(ev["uncovered"]),
           p.get("parent")))


WITNESS_VERIFIED = "VERIFIED"
WITNESS_REFUTED = "NOT_A_POINT"


def point_witness(graph, cid, timeout=300, _runner=None, _backend=None):
    """Substitute a NONEMPTY claim's exhibited point into its model's equations.

    THE CHEAPEST CHECK IN THE SYSTEM, WITH NO SURFACE FOR THREE RELEASES.
    `cas.check_witness` has existed and worked the whole time; nothing called
    it.  Two check rules and one kernel refusal all promise it by name -- "put
    it in `witness` and `cas_check_witness` will substitute it into the
    generators and tell you" -- and no code path ever did.  That is the fourth
    instance of a capability with no surface (`gp verify` itself, `ring_iso`,
    `unit_ideal`, this), and the gates do not catch it: GATE 3 asks whether a
    message names a command that does not exist, not whether a capability that
    exists is reachable.

    WHY IT MATTERS MORE THAN ITS COST SUGGESTS.  An EMPTY claim must name a
    certificate or the graph will not fold.  A NONEMPTY claim -- where the
    author is LITERALLY HOLDING THE OBJECT, the strongest evidence available
    anywhere in the system -- carried nothing checkable, so a fabricated point
    typed identically to a real one.  A live agent found that unprompted and
    said so plainly: "the graph cannot currently distinguish 'I have the point'
    from 'I claim to have the point'."

    And a REFUTED witness is a false NONEMPTY at its OWN MODEL, which no
    transport typing anywhere downstream would ever have surfaced -- the same
    shape as a REFUTED identity, and the reason both verifiers exist.

        VERIFIED     every generator vanishes at the point.
        NOT_A_POINT  one does not, and it is named with its value.
        UNVERIFIED   the question could not be put.

    STRUCTURED WITNESSES ONLY, via `witness_point`.  The prose `witness` field
    stays legal and stays unchecked -- 25 live records across four campaigns
    are strings like "(x, y) = (1, 2)" and "t = sqrt(3)" -- which is exactly
    the position IDENTITY was in before `lhs`/`rhs`.  The route out is the same
    one: record it structurally and it becomes a question a solver can answer.
    """
    c = graph.claims.get(cid)
    if not c:
        return UNVERIFIED, "no such claim"
    if c.get("kind") != K.NONEMPTY:
        return UNVERIFIED, "claim %s is %s, not a NONEMPTY" % (
            cid, c.get("kind"))
    point = c.get("witness_point")
    if not point:
        return UNVERIFIED, (
            "claim %s gives its point only in prose. `witness_point` -- a "
            "value for each ring variable -- is what makes it an arithmetic "
            "question rather than a reading question." % cid)
    model = graph.models.get(c.get("model")) or {}
    pending = _pending_ideal(c.get("model"), model)
    if pending:
        return UNVERIFIED, pending
    gens = list(model.get("generators") or [])
    if not gens:
        return UNVERIFIED, (
            "%s imposes no equations, so every point of the ambient space lies "
            "on it and there is nothing to substitute into. The claim may well "
            "be true; it is not this check that establishes it."
            % c.get("model"))
    ring = model.get("ring_vars") or c.get("ring_vars") or []
    if not ring:
        return UNVERIFIED, "neither %s nor claim %s declares ring variables" % (
            c.get("model"), cid)
    ch, missing = _declared_characteristic(c.get("model"), model)
    if missing:
        return UNVERIFIED, missing
    ok, evidence = (_backend or cas.SingularBackend(runner=_runner)).evaluate_point(
        ring, gens, point, characteristic=ch,
        timeout=timeout)
    shown = ", ".join("%s = %s" % (v, point[v]) for v in ring if v in point)
    if ok:
        return WITNESS_VERIFIED, (
            "every generator of %s's ideal vanishes at (%s), so the point is "
            "on the variety and the claim HOLDS AT ITS OWN MODEL. What that "
            "does not settle is where it may travel."
            % (c.get("model"), shown))
    failed = evidence["failed"]
    values = {g["generator"]: g["value"] for g in evidence["generators"]}
    return WITNESS_REFUTED, (
        "the point (%s) does not lie on %s: %s.\n"
        "  THIS ONE IS A REFUTATION. The claim is that the variety has a "
        "point and this is the point offered; substituting it is arithmetic "
        "and it does not vanish. So the NONEMPTY is unsupported at the model "
        "it was claimed at, and every transport that carried it carried "
        "something that was never established."
        % (shown, c.get("model"),
           "; ".join("%s evaluates to %s" % (g, values[g]) for g in failed)))


CERT_VERIFIED = "VERIFIED"
CERT_NOT_UNIT = "NOT_UNIT"


def unit_ideal(graph, cid, timeout=300, _runner=None, _backend=None):
    """Check an EMPTY claim's certificate against the computation, by expansion.

    THE LAST HONOUR-SYSTEM FIELD THAT CARRIES SCOPE, and the one that produced
    the erratum this whole project started from.

    `derive_scope` reads the certificate KIND to decide whether an emptiness
    survives a base change -- which was the fix for a declared `scope`, and
    moved the free choice one field along rather than removing it. Nothing
    relates the label `UNIT_IDEAL_CERT` to any computation. A caller who ran
    something, saw `1`, and typed the name gets the same scope as a caller who
    typed the name.

    WHAT MAKES THIS DIFFERENT FROM RE-RUNNING THE SEARCH.  The expensive step
    found cofactors `a_i` with `sum a_i f_i = 1`. Confirming that is one
    expansion -- no Buchberger, no monomial order, no trust in the search. The
    checker shares no code path with the thing it checks, which is the whole
    idea behind a certifying algorithm, and it is also the clean bridge to a
    proof assistant: Lean can check a polynomial identity and should never
    have to run a Groebner engine.

    Three verdicts:

        VERIFIED    cofactors found AND their expansion is 1
        NOT_UNIT    the ideal is not the unit ideal.  NOT a failed check --
                    the claim's certificate is simply not this one
        UNVERIFIED  the question could not be put
    """
    c = graph.claims.get(cid)
    if not c:
        return UNVERIFIED, "no such claim", None
    if c.get("kind") != K.EMPTY:
        return UNVERIFIED, "claim %s is %s, not EMPTY" % (cid, c.get("kind")), None
    # THIS VERIFIER ANSWERS ONE QUESTION AND IT IS NOT EVERY CLAIM'S QUESTION.
    #
    # It ran on ANY EMPTY claim carrying ANY certificate, and reported NOT_UNIT
    # -- "UNIT_IDEAL_CERT is not the certificate this claim has" -- about a
    # live claim that had never said it was. That claim declares
    # NONSQUARE_CLASS, and it is CORRECT: its ideal reduces to `t^2-3`, which
    # is exactly what a nonsquare-class argument looks like, empty over Q and
    # not over Q(sqrt 3).
    #
    # So the verifier refuted a certificate the author never claimed, and the
    # sentence it used to do it was already in the docstring above: NOT_UNIT
    # means "the claim's certificate is simply not this one", which only parses
    # if the claim said it was.
    #
    # Harmless while nothing read the verdict. The moment `check` began acting
    # on it, it became a false UNSOUND_PREMISE against a sound claim -- which
    # is how this was found, one command after wiring the two together.
    if c.get("certificate") != "UNIT_IDEAL_CERT":
        return UNVERIFIED, (
            "claim %s cites %s, and this verifier only decides "
            "UNIT_IDEAL_CERT. Expanding cofactors for `1` says nothing about "
            "whether a nonsquare class, a degree count or a cited theorem "
            "closes an emptiness; those are different arguments and want "
            "different checkers."
            % (cid, c.get("certificate") or "no certificate")), None
    model = graph.models.get(c.get("model")) or {}
    gens, ring = model.get("generators"), model.get("ring_vars")
    if not gens or not ring:
        return UNVERIFIED, (
            "model %s carries no ideal to expand -- a certificate about an "
            "ideal needs the ideal recorded, not only named"
            % c.get("model")), None

    ch, missing = _declared_characteristic(c.get("model"), model)
    if missing:
        return UNVERIFIED, missing, None
    rep = (_backend or cas.SingularBackend(runner=_runner)).unit_ideal(ring, list(gens), characteristic=ch,
                                        timeout=timeout)
    if not rep["is_unit"]:
        return CERT_NOT_UNIT, (
            "%s's ideal reduces to %s, not 1, so it is not the unit ideal and "
            "UNIT_IDEAL_CERT is not the certificate this claim has.\n"
            "  That is a statement about the CERTIFICATE and not about the "
            "emptiness: a model can be empty for other reasons, established by "
            "other means."
            % (c.get("model"), ", ".join(rep["basis"]))), None

    ok, expanded = (_backend or cas.SingularBackend(runner=_runner)).check_unit_ideal(
        ring, list(gens), rep["cofactors"], characteristic=ch,
        timeout=timeout)
    witness = " + ".join("(%s)*(%s)" % (a, f)
                         for a, f in zip(rep["cofactors"], gens))
    if not ok:
        return CERT_NOT_UNIT, (
            "the CAS returned cofactors for %s, and expanding them gives %s "
            "rather than 1.\n"
            "  This is the case the expansion exists to catch: the search said "
            "one thing and the arithmetic says another, and the arithmetic is "
            "the half a reader can check."
            % (c.get("model"), expanded), None)

    return CERT_VERIFIED, (
        "1 = %s, expanded and confirmed WITHOUT recomputing a basis. The "
        "certificate is now a computation rather than a name."
        % witness), {"cofactors": list(rep["cofactors"]),
                     "generators": list(gens), "ring_vars": list(ring)}


def localized_unit_ideal(graph, cid, timeout=300, _runner=None,
                         _backend=None):
    """Certify that the exact recorded principal-open model is empty.

    A point of ``D(g_1)...D(g_n)`` would make every guard invertible. If a
    guard monomial belongs to the model ideal, it would therefore be both zero
    and invertible. The bounded search is only a producer: success is checked
    by exact cofactor expansion, while exhaustion returns UNVERIFIED.
    """
    from . import localization as L

    c = graph.claims.get(cid)
    if not c:
        return UNVERIFIED, "no such claim", None
    if (c.get("kind") != K.EMPTY
            or c.get("certificate") != "LOCALIZED_UNIT_IDEAL_CERT"):
        return UNVERIFIED, (
            "claim %s does not ask for LOCALIZED_UNIT_IDEAL_CERT" % cid), None
    model = graph.models.get(c.get("model")) or {}
    ring = model.get("ring_vars")
    gens = model.get("generators")
    guards = model.get("open_conditions")
    if not ring or not gens or not guards:
        return UNVERIFIED, (
            "model %s needs ring_vars, generators, and open_conditions for "
            "a localized-unit certificate" % c.get("model")), None
    ch, missing = _declared_characteristic(c.get("model"), model)
    if missing:
        return UNVERIFIED, missing, None

    backend = _backend or cas.SingularBackend(runner=_runner)
    # First try pure guard monomials already visible in the generators. This is
    # only a producer hint, but it makes the JC q^3*t^2 and p^4*t^2 controls
    # one-shot instead of launching a total-degree walk. Non-variable guards
    # simply skip the hint and use the bounded frontier below.
    candidates = []
    guard_indices = []
    for guard in guards:
        polynomial = G.parse_polynomial(guard, ring, ch)
        if len(polynomial.terms) != 1:
            guard_indices = []
            break
        exponent, coefficient = next(iter(polynomial.terms.items()))
        if coefficient != 1 or sum(exponent) != 1:
            guard_indices = []
            break
        guard_indices.append(exponent.index(1))
    if len(set(guard_indices)) != len(guards):
        guard_indices = []
    if guard_indices:
        outside = set(range(len(ring))) - set(guard_indices)
        for generator in gens:
            for exponent in G.parse_polynomial(
                    generator, ring, ch).terms:
                powers = tuple(exponent[index] for index in guard_indices)
                if (any(powers)
                        and all(power <= 64 for power in powers)
                        and all(exponent[index] == 0 for index in outside)
                        and powers not in candidates):
                    candidates.append(powers)
                    if len(candidates) >= 8:
                        break
            if len(candidates) >= 8:
                break

    # Then small total degrees, deterministically. The cap is a producer
    # budget, not a theorem: failing to find a row proves nothing.
    product = tuple(1 for _ in guards)
    if product not in candidates:
        candidates.append(product)
    frontier = [tuple(0 for _ in guards)]
    seen = set(candidates + frontier)
    while frontier and len(candidates) < 32:
        powers = frontier.pop(0)
        if sum(powers) >= 64:
            continue
        for index in range(len(guards)):
            nxt = list(powers)
            nxt[index] += 1
            nxt = tuple(nxt)
            if nxt not in seen:
                seen.add(nxt)
                candidates.append(nxt)
                frontier.append(nxt)
                if len(candidates) >= 32:
                    break

    for powers in candidates:
        target = "1"
        for guard, power in zip(guards, powers):
            target = G.multiply_polynomial_power(
                target, guard, power, ring, ch)
        found = backend.membership(
            ring, target, list(gens), characteristic=ch, timeout=timeout)
        if not found["is_member"]:
            continue
        spec = {
            "schema": L.SCHEMA,
            "characteristic": ch,
            "ring_vars": list(ring),
            "generators": list(gens),
            "guards": list(guards),
            "expression": {
                "numerator": "1",
                "denominator_powers": [0 for _ in guards],
            },
            "certificate": {
                "localization_powers": list(powers),
                "membership_target": target,
                "cofactors": list(found["cofactors"]),
            },
        }
        checked = L.verify(spec)
        rep = {
            "method": "localized_unit_ideal_v1",
            "claim": cid,
            "model": c.get("model"),
            "proof": checked["normalized"],
            "checked": checked["checked"],
        }
        return CERT_VERIFIED, (
            "a guard monomial with powers %s belongs to the recorded ideal; "
            "exact cofactor expansion proves 1=0 in this localization, so "
            "the open model %s has no points. No parent emptiness is implied."
            % (list(powers), c.get("model"))), rep
    return UNVERIFIED, (
        "no localized-unit witness was found in the bounded search of %d "
        "guard monomials. This is search exhaustion, not evidence that the "
        "open model has a point." % len(candidates)), None

def _verdict_event(graph, subject, of, verdict, why, representation=None,
                   execution=None, verifier=None):
    # Content-address the answer together with the exact verifier/kernel/backend
    # identity and semantic input that made it authoritative.
    ev = {"ev": S.EV_VERDICT, "subject": subject, "of": of,
          "verdict": verdict, "why": why}
    ev.update(P.metadata(
        graph, subject, of, execution=execution,
        representation=representation, verifier=verifier, verdict=verdict))
    if representation:
        ev["representation"] = representation
    ev["id"] = "v.%s.%s" % (of, P.event_digest(ev))
    return ev


def verify_elimination_section(root, eid, section, timeout=300, record=True,
                               backend=None, _runner=None):
    """Check and optionally persist one explicit elimination section."""
    path = S.graph_path(root)
    graph = S.load(path)
    if backend is not None and _runner is not None:
        raise ValueError("pass backend or legacy _runner, not both")
    backend = backend or cas.SingularBackend(runner=_runner)
    if record and not backend.can_record_verdicts:
        raise ValueError(
            "record=True requires the exact production backend and binary; "
            "test doubles may be used only with record=False")
    execution_start = backend.execution_count
    try:
        verdict, why, representation = elimination_section(
            graph, eid, section, timeout=timeout, _backend=backend)
    except cas.CASError as exc:
        verdict, why, representation = UNVERIFIED, (
            "the CAS could not check this section:\n  %s" % exc), None
    if record:
        A.persist_all(root, backend.execution_artifacts(execution_start))
        event = _verdict_event(
            graph, "elimination", eid, verdict, why, representation,
            execution=backend.provenance(execution_start))
        S.append([event], root)
    return verdict, why, representation

def verify_elimination_point_lift(root, eid, certificate, timeout=300,
                                  record=True, backend=None, _runner=None):
    """Check and optionally persist one finite piecewise point-lift cover."""
    path = S.graph_path(root)
    graph = S.load(path)
    if backend is not None and _runner is not None:
        raise ValueError("pass backend or legacy _runner, not both")
    backend = backend or cas.SingularBackend(runner=_runner)
    if record and not backend.can_record_verdicts:
        raise ValueError(
            "record=True requires the exact production backend and binary; "
            "test doubles may be used only with record=False"
        )
    execution_start = backend.execution_count
    try:
        verdict, why, representation = elimination_piecewise_lift(
            graph, eid, certificate, timeout=timeout, _backend=backend
        )
    except cas.CASError as exc:
        verdict, why, representation = UNVERIFIED, (
            "the CAS could not check this point-lift cover:\n  %s" % exc
        ), None
    if record:
        A.persist_all(root, backend.execution_artifacts(execution_start))
        event = _verdict_event(
            graph, "point_lift", eid, verdict, why, representation,
            execution=backend.provenance(execution_start),
            verifier="verify.elimination_point_lift",
        )
        S.append([event], root)
    return verdict, why, representation

def verify_elimination_groebner(root, eid, timeout=300, record=True,
                                 backend=None, _runner=None):
    """Produce, independently check, and optionally persist completeness."""
    graph = S.load(S.graph_path(root))
    if backend is not None and _runner is not None:
        raise ValueError("pass backend or legacy _runner, not both")
    backend = backend or cas.SingularBackend(runner=_runner)
    if record and not backend.can_record_verdicts:
        raise ValueError(
            "record=True requires the exact production backend and binary; "
            "test doubles may be used only with record=False"
        )
    execution_start = backend.execution_count
    # Settle structural eligibility before spawning a process. An empty proof
    # reaches CERTIFICATE_REJECTED only after the edge, endpoints, field, and
    # variable partition are well-typed.
    eligibility, eligibility_why, _ = elimination_groebner(graph, eid, {})
    if eligibility == UNVERIFIED:
        verdict, why, representation = eligibility, eligibility_why, None
    else:
        edge = graph.edges[eid]
        source = graph.models[edge["src"]]
        target = graph.models[edge["dst"]]
        try:
            produced = GP.produce_elimination_groebner(
                backend,
                source["ring_vars"],
                source["generators"],
                target["eliminated"],
                target["generators"],
                characteristic=source["characteristic"],
                timeout=timeout,
            )
            verdict, why, representation = elimination_groebner(
                graph, eid, produced["proof"]
            )
            if (verdict == GROEBNER_VERIFIED
                    and representation["checked"] != produced["checked"]):
                raise cas.CASError(
                    "producer and graph-bound checker summaries disagree"
                )
        except (cas.CASError, G.CertificateError) as exc:
            verdict, why, representation = UNVERIFIED, (
                "the certificate producer could not complete a checked proof:\n"
                "  %s" % exc
            ), None
    if record:
        A.persist_all(root, backend.execution_artifacts(execution_start))
        event = _verdict_event(
            graph, "elimination", eid, verdict, why, representation,
            execution=backend.provenance(execution_start),
            verifier="verify.elimination_groebner",
        )
        S.append([event], root)
    return verdict, why, representation


def materialize_elimination_groebner(
        root, src, eliminated, produces, timeout=300, record=True,
        backend=None, _runner=None):
    """Materialize a certified target in one prevalidated graph batch.

    The retained lex basis is discovered rather than supplied. Before any
    declaration is appended, the operation-output verifier proves that every
    retained generator belongs to the source ideal, while the backend-neutral
    Groebner checker proves contraction completeness. These are independent
    directions; neither is allowed to stand in for the other.
    """
    if backend is not None and _runner is not None:
        raise ValueError("pass backend or legacy _runner, not both")
    backend = backend or cas.SingularBackend(runner=_runner)
    if record and not backend.can_record_verdicts:
        raise ValueError(
            "record=True requires the exact production backend and binary; "
            "test doubles may be used only with record=False"
        )
    if not isinstance(produces, str) or not produces.strip():
        raise ValueError("produces must be a nonempty model id")

    graph = S.load(S.graph_path(root))
    source = graph.models.get(src)
    if source is None:
        raise ValueError("%s is not a model in this graph" % src)
    if (source.get("superseded_by") or source.get("retracted_by")
            or source.get("withdrawn_by")):
        raise ValueError("%s is not an active model" % src)
    if source.get("ideal_pending"):
        raise ValueError("%s still has a pending ideal" % src)
    if source.get("ring_vars") is None or source.get("generators") is None:
        raise ValueError("%s must record ring variables and an ideal" % src)
    if "characteristic" not in source:
        raise ValueError("%s must declare a characteristic" % src)

    if isinstance(eliminated, (str, bytes)):
        raise ValueError("eliminated must be a sequence of variable names")
    eliminated = list(eliminated)
    ring = list(source["ring_vars"])
    if (not eliminated or len(eliminated) != len(set(eliminated))
            or any(variable not in ring for variable in eliminated)):
        raise ValueError("eliminated must be a nonempty unique ring subset")
    if set(eliminated) == set(ring):
        raise ValueError("elimination cannot remove every ring variable")
    characteristic = source["characteristic"]
    exact_domain = "Q" if characteristic == 0 else "F_%d" % characteristic
    if source.get("field") != exact_domain:
        raise ValueError(
            "%s must declare the exact coefficient field %s"
            % (src, exact_domain)
        )

    operation = O.eliminate(
        src, eliminated, produces, ring, source["generators"],
        characteristic=characteristic,
    )
    events = [dict(event) for event in operation.events]
    target_event = next(
        event for event in events if event.get("ev") == S.EV_MODEL
    )
    target_event["field"] = exact_domain
    edge_event = next(
        event for event in events if event.get("ev") == S.EV_EDGE
    )
    eid = edge_event["id"]

    # Reject conflicting ids and malformed constructor output before spawning
    # an expensive process. This preview is discarded and grants no authority.
    preview_events = copy.deepcopy(events)
    preview_target = next(
        event for event in preview_events if event.get("ev") == S.EV_MODEL
    )
    preview_target.pop("ideal_pending", None)
    preview_target["generators"] = []
    preview = copy.deepcopy(graph)
    for event in preview_events:
        preview.apply(event, source="<materialize-preview>")
    preview.validate()

    execution_start = backend.execution_count
    produced = GP.produce_retained_elimination_groebner(
        backend, source["ring_vars"], source["generators"], eliminated,
        characteristic=source["characteristic"], timeout=timeout,
    )
    target_event.pop("ideal_pending", None)
    target_event["generators"] = list(
        produced["proof"]["target_generators"]
    )

    candidate = copy.deepcopy(graph)
    for event in events:
        candidate.apply(event, source="<materialize-candidate>")
    candidate.validate()

    contraction, contraction_why, contraction_rep = elimination_groebner(
        candidate, eid, produced["proof"]
    )
    if contraction != GROEBNER_VERIFIED:
        raise cas.CASError(
            "the graph-bound Groebner proof was not accepted: %s"
            % contraction_why
        )
    if contraction_rep["checked"] != produced["checked"]:
        raise cas.CASError(
            "producer and graph-bound checker summaries disagree"
        )
    # Capture producer-only provenance before operation_output spawns its own
    # independent ideal-membership checks.
    contraction_event = _verdict_event(
        candidate, "elimination", eid, contraction, contraction_why,
        contraction_rep, execution=backend.provenance(execution_start),
        verifier="verify.elimination_groebner",
    )

    operation_start = backend.execution_count
    output, output_why, output_rep = operation_output(
        candidate, eid, timeout=timeout, _backend=backend
    )
    if output != OP_SOUND:
        raise cas.CASError(
            "the retained basis failed the no-invention check: %s"
            % output_why
        )
    output_event = _verdict_event(
        candidate, "operation", eid, output, output_why, output_rep,
        execution=backend.provenance(operation_start),
        verifier="verify.operation_output",
    )

    append_events = events + [output_event, contraction_event]
    if record:
        # Objects before log: an append failure may leave only harmless,
        # content-addressed orphans, never a partial mathematical declaration.
        A.persist_all(root, backend.execution_artifacts(execution_start))
        latest = S.load(S.graph_path(root))
        if latest.models.get(src) != source:
            raise S.GraphError(
                "%s changed while the certificate was being produced; "
                "nothing was appended" % src
            )
        if produces in latest.models or eid in latest.edges:
            raise S.GraphError(
                "target id %s or edge id %s appeared while the certificate "
                "was being produced; nothing was appended" % (produces, eid)
            )
        # S.append folds the complete batch before writing it. It is
        # prevalidated rather than a crash-atomic filesystem transaction, so
        # the reload above is the narrow race check around the long CAS run.
        S.append(append_events, root)
    return {
        "model": produces,
        "edge": eid,
        "generators": list(target_event["generators"]),
        "operation_verdict": output,
        "contraction_verdict": contraction,
        "why": contraction_why,
        "checked": produced["checked"],
        "events": append_events,
    }
def verify_all(root=".", timeout=300, _runner=None, record=True, backend=None):
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
    if backend is not None and _runner is not None:
        raise ValueError("pass backend or legacy _runner, not both")
    backend = backend or cas.SingularBackend(runner=_runner)
    if record and not backend.can_record_verdicts:
        raise ValueError(
            "record=True requires the exact production backend and binary; "
            "subclasses, injected runners, and version overrides may be used "
            "only with record=False")

    def run(subject, oid, fn):
        """One object, and a failure here must not cost the other twenty.

        A live campaign lost a whole run to this: one claim naming a symbol
        the ring did not have raised out of `classify_identity`, the batch
        aborted, `S.append` never ran, and FOUR CLAIMS AND TWELVE EDGES that
        had already verified were discarded.  `gp check` had reported that
        exact claim politely one command earlier.
        """
        rep = None
        execution_start = backend.execution_count
        try:
            out = fn()
        except cas.CASError as exc:
            verdict, why = UNVERIFIED, (
                "the CAS could not answer for this object, and the rest of the "
                "run continued:\n  %s" % exc)
        else:
            verdict, why = out[0], out[1]
            # THE CERTIFICATE, IF THE VERIFIER MINTED ONE -- and this line is
            # why it now survives.  `unit_ideal` has returned cofactors as a
            # third element since it was written, and the call site sliced them
            # off with `[:2]`. So the expensive part ran, the representation
            # was built, the expansion confirmed it, and the graph kept only
            # the word VERIFIED. The one artifact a reader could have rechecked
            # without trusting the search was computed and dropped.
            rep = out[2] if len(out) > 2 else None
        if record:
            # OBJECT BEFORE LOG. A persistence failure leaves the append-only
            # graph byte-identical; a later append failure can leave only a
            # harmless, deduplicated orphan.
            A.persist_all(root, backend.execution_artifacts(execution_start))
        results.append((subject, oid, verdict, why))
        events.append(_verdict_event(
            graph, subject, oid, verdict, why, rep,
            execution=backend.provenance(execution_start)))

    for eid in sorted(graph.edges):
        e = graph.edges[eid]
        # SUPERSEDED RECORDS ARE NOT IN THE GRAPH as far as `check` is
        # concerned, and `verify` disagreed -- it filtered only on the verdict
        # field.  So a claim corrected by supersession kept being re-verified,
        # and kept re-raising the error that had motivated the correction.
        if e.get("superseded_by"):
            continue
        src, dst = graph.models.get(e["src"]), graph.models.get(e["dst"])
        if not src or not dst:
            continue
        if (not e.get("containment")
                and not K.is_mapped_equivalence(e)
                and src.get("generators") is not None
                and dst.get("generators") is not None):
            run("edge", eid, lambda eid=eid: containment(
                graph, eid, timeout=timeout, _backend=backend))
        # RING_ISO HAD NO SURFACE AT ALL.  It worked, it caught a planted
        # false EQUIVALENCE in a live campaign, and it was reachable only by
        # importing the module from Python -- the same defect `gp verify`
        # itself had two days earlier.
        # WHAT A CONSTRUCTOR ACTUALLY PRODUCED, against what it says it did.
        if (e.get("built_by_operation") in ("SaturateClosure", "Eliminate")
                and not e.get("output_verdict")):
            run("operation", eid, lambda eid=eid: operation_output(
                graph, eid, timeout=timeout, _backend=backend))
        # THE MAPS ARE THE TRIGGER, NOT THE FLAG.
        #
        # This required `ring_iso` IN ADDITION to the maps, so an author who
        # did the natural thing -- supply `forward` and `inverse` -- got
        # SILENCE: no verdict, and nothing anywhere saying the maps had been
        # ignored. A live session reached this verifier only by reading the
        # dispatcher, and rightly called it a verifier that passes its tests
        # and is never reached in the field.
        #
        # `effective_ring_iso` already refuses to MINT the flag from a VERIFIED
        # verdict -- an author who never declared it is not granted it by a
        # check they did not ask for -- so running this unconditionally records
        # an answer without licensing anything.
        if (K.is_mapped_equivalence(e)
                and not e.get("ring_iso_verdict")):
            run("ring_iso", eid, lambda eid=eid: ring_iso(
                graph, eid, timeout=timeout, _backend=backend))

    for cid in sorted(graph.claims):
        c = graph.claims[cid]
        if c.get("superseded_by"):
            continue
        if (c.get("kind") == K.IDENTITY and not c.get("identity_verdict")
                and c.get("lhs") is not None and c.get("rhs") is not None):
            # Silent where the rewriting was never recorded.  An unstructured
            # IDENTITY is not a failed verification, it is an unasked
            # question, and `check` reports that hole.
            run("claim", cid, lambda cid=cid: identity(
                graph, cid, timeout=timeout, _backend=backend))
        # ONLY the kind this verifier decides. Running it on every certificate
        # spent a solver call to produce a refutation of something nobody
        # claimed.
        if (c.get("kind") == K.EMPTY
                and c.get("certificate") == "UNIT_IDEAL_CERT"
                and not c.get("certificate_verdict")):
            # NO `[:2]` -- that slice is what threw the cofactors away.
            run("certificate", cid,
                lambda cid=cid: unit_ideal(graph, cid, timeout=timeout,
                                           _backend=backend))
        # THE OTHER HALF OF THE EXISTENCE STORY, and the last of the four
        # capabilities that worked and could not be reached.  Silent on a prose
        # witness for the same reason as an unstructured IDENTITY: that is an
        # unasked question, not a failed one, and `check` is where the hole
        # gets reported.
        if (c.get("kind") == K.EMPTY
                and c.get("certificate") == "LOCALIZED_UNIT_IDEAL_CERT"
                and not c.get("certificate_verdict")):
            run("certificate", cid,
                lambda cid=cid: localized_unit_ideal(
                    graph, cid, timeout=timeout, _backend=backend))
        if (c.get("kind") == K.NONEMPTY and c.get("witness_point")
                and not c.get("witness_verdict")):
            run("witness", cid, lambda cid=cid: point_witness(
                graph, cid, timeout=timeout, _backend=backend))

    # THE PREMISE NOBODY COULD CHECK. A partition's `exhaustive` claim is what
    # licenses every conclusion of the form "and those are all the cases", and
    # until now it was a claim id pointing at prose.
    for pid in sorted(graph.partitions):
        p = graph.partitions[pid]
        if p.get("superseded_by") or p.get("exhaustive_verdict"):
            continue
        run("partition", pid, lambda pid=pid: partition_exhaustiveness(
            graph, pid, timeout=timeout, _backend=backend))

    if record and events:
        # ROOT, not the graph path.  `append` resolves `.portage/graph.jsonl`
        # itself, so passing the resolved path built
        # `.portage/graph.jsonl/.portage` and crashed -- on the ONE line the
        # suite never reached, because every test called `verify_all` with
        # `record=False` or a fixture that produced no events.
        S.append(events, root)
    return results
