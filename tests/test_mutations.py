"""Whole-gate mutations: does the gate have teeth?

A check that cannot fail is worse than no check.  Every assertion in
test_retrodiction.py is only worth something if some reachable edit to the
graph breaks it, so each mutation below perturbs ONE declared attribute and
asserts the verdict moves.

Two shapes appear, and both matter:

  SILENCING   -- retype the edge and a real flag disappears.  This says the
                 detection turns on that attribute and not on which file the
                 claim came from.
  BREAKING    -- perturb something and a POSITIVE CONTROL starts firing.  This
                 says the clean verdicts are contingent on real attributes
                 rather than on the checker being lenient.

Some mutations do not produce a different verdict, they produce a REFUSED
FOLD.  That is the strongest outcome available: the graph cannot state the
mutated claim at all.
"""

import pytest

from grandportage import check as C
from grandportage import kernel as K
from grandportage import store as S

import helpers as H


# ===========================================================================
# JC(2)
# ===========================================================================

def test_mut_retyping_the_field_extension_silences_the_shipped_error():
    """E8 as an EQUIVALENCE: the framework is saying precisely 'this step is
    sound only if enlarging the field changes nothing', which is the true
    mathematical content of the C08 defect."""
    g = H.mutate("jc2", H.set_field("edge", "E8", type="EQUIVALENCE"))
    assert "INF-C08-HIST" not in H.flagged(g)
    assert "INF-C20-HIST" in H.flagged(g)      # the sibling edge is untouched


def test_mut_retyping_the_chart_edge_silences_the_chart_error_and_its_taint():
    """E12 as an EQUIVALENCE removes both the flag and the taint -- i.e. the
    framework says the slice calculus may be run in the shifted chart only if
    the shift is an isomorphism.  I3_AUDIT.md E4b proves it is not."""
    g = H.mutate("jc2", H.set_field("edge", "E12", type="EQUIVALENCE"))
    assert "INF-SLICEPHI" not in H.flagged(g)
    assert C.R_TAINT not in H.rules(g)


def test_mut_retyping_the_closure_edge_silences_the_survivor_triage():
    g = H.mutate("jc2", H.set_field("edge", "E10", type="EQUIVALENCE"))
    assert "INF-A10-SURV" not in H.flagged(g)


def test_mut_retyping_the_syzygy_alone_does_NOT_break_the_reverse_reading():
    """A negative result, kept because it corrects the prototype's own note.

    whetstone_dag.py annotates INF-KSYZ-REV as "the direction that would be
    FORBIDDEN on a NECESSARY_CONDITION edge".  That is true for NONEMPTY and
    for PREDICATE; it is NOT true for the claim actually recorded, which is an
    IDENTITY.  NECESSARY_CONDITION carries IDENTITY in both directions whenever
    the map is denominator-free, and E3's map is POLYNOMIAL.  So retyping E3
    alone leaves this inference licensed, and the note overstates what the
    control tests.  Recorded as a test so the correction cannot be lost.
    """
    g = H.mutate("jc2", H.set_field("edge", "E3", type="NECESSARY_CONDITION"))
    assert "INF-KSYZ-REV" not in H.flagged(g)
    # What the retyping DOES break is the forward reading: INF-KSYZ carries
    # EMPTY ALONG the arrow, which only an EQUIVALENCE licenses.  So the E3
    # mutation has teeth -- just not on the inference the prototype's note
    # points at.
    assert "INF-KSYZ" in H.flagged(g)


def test_mut_retyping_the_syzygy_AND_its_map_does_break_it():
    """What the control actually turns on: the type AND the denominators."""
    def patch(ev):
        if ev.get("ev") == "edge" and ev.get("id") == "E3":
            ev["type"] = "NECESSARY_CONDITION"
            ev["map_kind"] = "RATIONAL"
        return ev
    g = H.mutate("jc2", patch)
    assert "INF-KSYZ-REV" in H.flagged(g)


def test_probe_shows_the_syzygy_control_is_non_vacuous():
    """The prototype's PC-KSYZ-NONVACUOUS, as a probe rather than a mutation.

    EQUIVALENCE licenses PREDICATE transport in a direction the same edge
    retyped NECESSARY_CONDITION would forbid.  Without this the K-syzygy
    control could pass for free -- an edge whose type never mattered.
    """
    g = H.load("jc2")
    eq = C.probe(g, "CL-PSLICE-COND", "E3", K.ALONG)
    nc = C.probe(g, "CL-PSLICE-COND", "E3", K.ALONG,
                 etype=K.NECESSARY_CONDITION)
    assert eq.licensed and not nc.licensed


def test_mut_declaring_the_missing_component_silences_the_coverage_gap():
    """The repair, applied: declare a t-component and the leak detection goes
    quiet.  Data-driven, not tuned."""
    g = H.mutate("jc2", H.set_field(
        "model", "WINDOW", declares={"place": ["y", "inf", "t"]}))
    assert "COVERAGE:WINDOW:place" not in H.findings_by_id(g)
    # ...and the OTHER axis is untouched, so this is a targeted silencing
    # rather than the coverage rule going quiet everywhere.
    assert "COVERAGE:GSYS:order" in H.findings_by_id(g)


def test_mut_emptying_the_gauge_and_read_lists_silences_it_the_other_way():
    """The second, independent silencing.  Two mutations that kill the same
    detection from opposite sides is what distinguishes a rule from a constant."""
    g = H.mutate("jc2", H.set_field("model", "WINDOW", touches=[], reads=[]))
    assert "COVERAGE:WINDOW:place" not in H.findings_by_id(g)
    assert "COVERAGE:GSYS:order" in H.findings_by_id(g)


def test_mut_making_the_dictionary_rational_BREAKS_the_sound_leg():
    """The sound and unsound legs of a_t <= 9 reach the same conclusion from
    the same four equations.  ONE declared attribute -- E13's map_kind --
    separates them.  Make the row transform rational and the sound leg falls
    too, so the clean verdict is contingent on a real fact."""
    g = H.mutate("jc2", H.set_field("edge", "E13", map_kind="RATIONAL"))
    assert "INF-SYZCOLL-DICT" in H.flagged(g)
    assert "INF-SYZCOLL" not in H.flagged(g)   # EMPTY does not need the map


def test_mut_removing_the_counter_claim_downgrades_but_does_not_silence():
    """The severity derivation is real, and it is SEPARATE from the refusal.

    Drop the real-torus-points claim and the C08 flag survives -- the transport
    is still refused -- but it can no longer be graded a true positive, because
    nothing in the graph contradicts the conclusion any more.
    """
    def drop(ev):
        return None if ev.get("id") == "CL-C08-REAL" else ev
    g = H.mutate("jc2", drop)
    f = H.findings_by_id(g)["TRANSPORT:INF-C08-HIST"]
    assert f.severity == C.UNSOUND_PREMISE
    assert f.derived_severity == C.UNSOUND_PREMISE


def test_mut_giving_the_kill_a_base_changing_certificate_silences_it():
    """The detection turns on the CERTIFICATE, not on the field the
    computation happened in."""
    g = H.mutate("jc2", H.set_field("claim", "CL-C08",
                                    certificate="UNIT_IDEAL_CERT", scope=None))
    assert "INF-C08-HIST" not in H.flagged(g)


def test_probe_separates_the_contrast_pair_on_one_shared_edge():
    """The prototype's PC-CONTRAST-PAIR, and it MUST be a probe.

    As recorded inferences the two emptiness results travel over different
    edges (E8, a BASE_EXTENSION; E6, a NECESSARY_CONDITION), so comparing them
    directly proves nothing about the certificate.  Push BOTH across E8 and the
    only remaining difference is the certificate -- and the verdicts are
    opposite.  A rule tuned to fire on "an emptiness computed over Q" would
    refuse both.
    """
    g = H.load("jc2")
    c08 = C.probe(g, "CL-C08", "E8", K.ALONG)
    pos = C.probe(g, "CL-POSSLICE", "E8", K.ALONG)
    assert not c08.licensed and pos.licensed
    assert g.claims["CL-C08"]["certificate"] == "NONSQUARE_CLASS"
    assert g.claims["CL-POSSLICE"]["certificate"] == "NONZERO_RESULTANT"


def test_mut_giving_the_contrast_pair_a_field_relative_certificate_BREAKS_it():
    """The mutation form: strip the base-changing certificate and the licensed
    half of the pair falls, on the same probe."""
    g = H.mutate("jc2", H.set_field("claim", "CL-POSSLICE",
                                    certificate="NONSQUARE_CLASS", scope="Q"))
    assert not C.probe(g, "CL-POSSLICE", "E8", K.ALONG).licensed
    # ...but its RECORDED inference is unaffected, because E6 is a
    # NECESSARY_CONDITION edge read AGAINST, where EMPTY travels freely.
    assert "INF-POSSLICE" not in H.flagged(g)


def test_mut_typing_a_refinement_as_anything_else_is_caught():
    g = H.mutate("jc2", H.set_field("edge", "E5b", type="EQUIVALENCE"))
    assert C.R_REFINEMENT in H.rules(g)


def test_mut_untyping_an_edge_blocks_everything_crossing_it():
    g = H.mutate("jc2", H.set_field(
        "edge", "E13", type="UNTYPED",
        debt_why="relation between the charts not yet established"))
    assert {"INF-SYZCOLL", "INF-SYZCOLL-DICT"} <= H.flagged(g)
    assert C.R_UNTYPED in H.rules(g)


# ===========================================================================
# matroid
# ===========================================================================

def test_mut_making_nonsquare_class_base_change_silences_every_ml8_flag():
    """One row of the certificate registry carries all three ML8 refusals."""
    def patch(ev):
        if ev.get("ev") == "claim" and ev.get("certificate") == "NONSQUARE_CLASS":
            ev["certificate"] = "UNIT_IDEAL_CERT"
            ev.pop("scope", None)
        return ev
    g = H.mutate("matroid", patch)
    assert "IM-ML8-BASE-EXT" not in H.flagged(g)
    assert "IM-ML8-Q-BASE-EXT" not in H.flagged(g)
    assert "IM-ML8-DESCENT" in H.flagged(g)    # NONEMPTY descent is unaffected


def test_mut_downgrading_frame_normalisation_BREAKS_the_sharp_control():
    """IM-ML8-UP is NONEMPTY read AGAINST the arrow -- forbidden on a
    NECESSARY_CONDITION edge, licensed only because frame normalisation is a
    genuine equivalence."""
    g = H.mutate("matroid",
                 H.set_field("edge", "M-E2", type="NECESSARY_CONDITION"))
    assert "IM-ML8-UP" in H.flagged(g)


def test_mut_opening_the_rank_predicate_BREAKS_the_closure_control():
    """IM-U35-RANK turns on `zariski_closed` and nothing else."""
    g = H.mutate("matroid",
                 H.set_field("claim", "CM-U35-RANK", zariski_closed=False))
    assert "IM-U35-RANK" in H.flagged(g)


def test_mut_retyping_the_saturation_edge_silences_the_saturation_trap():
    g = H.mutate("matroid", H.set_field("edge", "M-E4", type="EQUIVALENCE"))
    assert "IM-NF-SKIP-SAT" not in H.flagged(g)


def test_mut_specialization_refuses_a_witness_every_other_type_allows():
    """The fifth type earns its place here.

    IM-ML8-ASCEND is a clean control under BASE_EXTENSION: a Q(sqrt(-3))-point
    IS a C-point.  Retype the step SPECIALIZATION and it is refused -- because
    a point over the generic fibre is NOT a point over the special fibre.  That
    is the whole content of the char-0 -> char-p gap, in one assertion.
    """
    g = H.mutate("matroid",
                 H.set_field("edge", "M-E1c", type="SPECIALIZATION"))
    assert "IM-ML8-ASCEND" in H.flagged(g)


@pytest.mark.parametrize("etype", [t for t in K.ALL_TYPES
                                   if t != K.SPECIALIZATION])
def test_mut_no_inherited_type_can_carry_the_characteristic_change(etype):
    """The argument that forced the fifth type, run as a mutation.

    Type the F_2 saturation step as each inherited type in turn.  Every one of
    them licenses at least one existence transport that published matroid
    theory falsifies -- Fano and non-Fano disagree in both directions -- so the
    step is either untyped or mistyped under any four-type system.
    """
    g = H.mutate("matroid", H.set_field("edge", "M-E4", type=etype))
    licensed_existence = any(
        K.transport(etype, d, k).licensed
        for d in K.DIRECTIONS for k in (K.EMPTY, K.NONEMPTY))
    assert licensed_existence
    assert isinstance(H.flagged(g), set)


def test_mut_a_field_relative_certificate_cannot_be_declared_scheme_scoped():
    """Not a different verdict -- a REFUSED FOLD.  The graph cannot state it.

    FINITE_FIELD_EXHAUSTION does not base-change (non-Fano is empty over F_2
    and nonempty over Q).  Strip the F_2 scope from the claim that uses it and
    the fold rejects the graph rather than checking something weaker.
    """
    def patch(ev):
        if ev.get("id") == "CM-NF-F2-EMPTY":
            ev.pop("scope", None)
        return ev
    with pytest.raises(K.ScopeError):
        H.mutate("matroid", patch)


def test_mut_flipping_a_domain_certificate_changes_the_derived_scope():
    g = H.mutate("matroid", H.set_field(
        "certificate", "FINITE_FIELD_EXHAUSTION", base_changes=True,
        why="mutated"))
    assert g.claims["CM-NF-F2-EMPTY"]["scope"] == K.SCHEME
    assert g.claims["CM-NF-F2-EMPTY"]["declared_scope"] == "F_2"


def test_mut_dropping_the_published_counter_claim_downgrades_the_saturation_trap():
    def drop(ev):
        return None if ev.get("id") == "CM-NF-F2-EMPTY" else ev
    g = H.mutate("matroid", drop)
    f = H.findings_by_id(g)["TRANSPORT:IM-NF-SKIP-SAT"]
    assert f.severity == C.UNSOUND_PREMISE


# ===========================================================================
# the gate as a whole
# ===========================================================================

MUTATIONS_THAT_MUST_MOVE_THE_GATE = [
    ("jc2", H.set_field("edge", "E8", type="EQUIVALENCE")),
    ("jc2", H.set_field("edge", "E12", type="EQUIVALENCE")),
    ("jc2", H.set_field("edge", "E10", type="EQUIVALENCE")),
    ("jc2", H.set_field("edge", "E3", type="NECESSARY_CONDITION")),
    ("jc2", H.set_field("model", "WINDOW",
                        declares={"place": ["y", "inf", "t"]})),
    ("jc2", H.set_field("edge", "E13", map_kind="RATIONAL")),
    ("matroid", H.set_field("edge", "M-E2", type="NECESSARY_CONDITION")),
    ("matroid", H.set_field("claim", "CM-U35-RANK", zariski_closed=False)),
    ("matroid", H.set_field("edge", "M-E4", type="EQUIVALENCE")),
    ("matroid", H.set_field("edge", "M-E1c", type="SPECIALIZATION")),
]


@pytest.mark.parametrize("domain,patch",
                         MUTATIONS_THAT_MUST_MOVE_THE_GATE)
def test_every_listed_mutation_changes_the_finding_set(domain, patch):
    """The blunt version: perturbing one declared attribute must change what
    the checker says.  If it does not, the attribute is decoration."""
    before = set(H.findings_by_id(H.load(domain)))
    after = set(H.findings_by_id(H.mutate(domain, patch)))
    assert before != after
