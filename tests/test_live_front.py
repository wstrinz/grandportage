"""The live gamma-window front.

The other two fixtures replay settled history against answer keys pinned before
this code existed.  This one models work that is OPEN, so there is no answer key
and none is claimed -- these tests assert that the tool says something stable
and correctly shaped about live obligations, not that it got a known answer.

The honest framing, kept here so it is not lost: every obligation in this
fixture was ALREADY KNOWN and already written down, in SESSION_HANDOFF.md's
prose and in F2_TOWER.md's banner.  Grand Portage discovers none of it.  What it
changes is that a prose banner -- the first thing lost at a compaction, and in
one case literally a `print` statement -- becomes a fact about the graph that
blocks the conclusion depending on it and names its own discharge.
"""

import pytest

from grandportage import check as C
from grandportage import kernel as K

import helpers as H

DOMAIN = "gamma_window"

# The four live obligations, and what each one is.
OBLIGATIONS = {
    "GI-GAMMA-IMPORT":
        "the standing gamma obligation: GGV3 sec.5 asserts gamma in {2,3} "
        "WITHOUT PROOF, while the corner layer derives only {2,3,4}",
    "GI-REPLAY-TRANSFER":
        "the replay trap: the (50,75) certificate is a replay of published "
        "algebra and there is no transcription to copy at (75,125)",
    "GI-BRIDGE":
        "the unverified bridge: two computations that share not one variable, "
        "joined by a print statement",
    "GI-WINDOW-CONFLATION":
        "two different objects wearing the word 'window' -- a collapsed cone "
        "and a depth ledger",
}


def graph():
    return H.load(DOMAIN)


def test_the_fixture_folds_and_every_path_is_connected():
    g = graph()
    assert len(g.models) == 10
    for iid in g.inference_order:
        assert g.inferences[iid]["concludes_at"] in g.models


def test_all_four_live_obligations_are_refused():
    flagged = H.flagged(graph())
    assert set(OBLIGATIONS) <= flagged


def test_the_positive_control_stays_clean():
    """GI-T4-SOUND reads a PREDICATE AGAINST the arrow, which is licensed.

    Without it this fixture would only show that the checker refuses things,
    not that it discriminates -- and on a graph built entirely from recorded
    warnings, that distinction is the whole question.
    """
    g = graph()
    assert C.clean_inferences(g, C.run(g)) == ["GI-T4-SOUND"]


def test_drawing_a_conclusion_across_an_untyped_edge_BLOCKS(monkeypatch):
    """The distinction the live run exposed, and it is not cosmetic.

    An UNTYPED edge is a hole, and a recorded hole is DEBT -- below the
    blocking floor, deliberately, so that recording holes stays cheap.  But
    DRAWING A CONCLUSION across one asserts something no declared relation
    supports.  Grading that DEBT too would put the untyped steps -- the exact
    thing the type exists to catch -- below the floor, so they would be the
    only findings that never stop anybody.
    """
    found = H.findings_by_id(graph())
    for iid in ("GI-REPLAY-TRANSFER", "GI-BRIDGE", "GI-WINDOW-CONFLATION"):
        f = found["TRANSPORT:%s" % iid]
        assert f.severity == C.UNSOUND_PREMISE, iid
    for eid in ("GE4", "GE5", "GE6"):
        assert found["UNTYPED-EDGE:%s" % eid].severity == C.DEBT, eid


def test_an_untyped_edge_with_no_traffic_does_not_block():
    """The other half: recording a hole must stay cheap, or people stop doing
    it and the hole goes back to being invisible."""
    def drop_inferences(ev):
        if ev.get("ev") == "inference" and ev.get("id") in (
                "GI-REPLAY-TRANSFER", "GI-BRIDGE", "GI-WINDOW-CONFLATION"):
            return None
        return ev
    g = H.mutate(DOMAIN, drop_inferences)
    findings = C.run(g)
    untyped = [f for f in findings if f.rule == C.R_UNTYPED]
    assert len(untyped) == 3
    assert all(f.severity == C.DEBT for f in untyped)


def test_the_gamma_obligation_is_a_direction_error_not_an_evidence_problem():
    """The sharpest thing this fixture shows.

    GC-GAMMA23 sits at ladder 'claimed' because GGV3 declines to prove it --
    so an evidence ladder ALSO objects.  But the refusal here is independent of
    that: it is a PREDICATE moving ALONG a NECESSARY_CONDITION edge, and it
    would be refused at ladder 'certified' too.  Evidence grade never licenses
    a transport.
    """
    g = graph()
    assert g.claims["GC-GAMMA23"]["ladder"] == "claimed"
    promoted = H.mutate(DOMAIN,
                        H.set_field("claim", "GC-GAMMA23", ladder="certified"))
    assert "GI-GAMMA-IMPORT" in H.flagged(promoted)


def test_the_replay_trap_is_not_caught_by_scope_or_by_evidence():
    """Neither the certificate nor the ladder is what stops the replay.

    GC-A2-KILL carries UNIT_IDEAL_CERT, which base-changes, at ladder
    exact-checked.  A framework that only tracked field scope, or only tracked
    evidence grade, would wave this through.  The EDGE is what stops it.
    """
    g = graph()
    c = g.claims["GC-A2-KILL"]
    assert c["scope"] == K.SCHEME and c["ladder"] == "exact-checked"
    assert "GI-REPLAY-TRANSFER" in H.flagged(g)


def test_naming_the_bridges_type_is_not_enough_the_DIRECTION_is_the_claim():
    """Typing GE5 NECESSARY_CONDITION as drawn does NOT discharge it, and the
    reason is the useful part.

    A PREDICATE still cannot travel ALONG a NECESSARY_CONDITION edge.  For the
    period fact to constrain the kill, the KILL layer has to be the tighter
    model -- i.e. its data has to determine the period layer's, not the other
    way round.  So the discharge is not "pick a type", it is "state which layer
    has more information, and be right".  That is a substantive claim about
    f2_tower.py, which is exactly the claim the print statement skipped.
    """
    as_drawn = H.mutate(DOMAIN, H.set_field(
        "edge", "GE5", type=K.NECESSARY_CONDITION,
        why="the period layer as a relaxation of the kill layer"))
    assert "GI-BRIDGE" in H.flagged(as_drawn)


def test_the_bridge_discharges_only_when_the_direction_is_asserted_too():
    """Reverse the edge -- claim the kill layer refines the period layer -- and
    the predicate now travels AGAINST, which is licensed.

    This mutation is NOT an endorsement.  F2_TOWER.md withdrew exactly such an
    endorsement on its second pass, and nothing here re-establishes it.  It
    shows the SHAPE of the repair and its price: someone must assert, and be
    accountable for, that the kill layer determines the period layer.
    """
    def patch(ev):
        if ev.get("ev") == "edge" and ev.get("id") == "GE5":
            ev["src"], ev["dst"] = ev["dst"], ev["src"]
            ev["type"] = K.NECESSARY_CONDITION
            ev["why"] = ("the kill layer refines the period layer: its data "
                         "would determine the period computation")
            ev.pop("debt_why", None)
        if ev.get("ev") == "inference" and ev.get("id") == "GI-BRIDGE":
            ev["path"] = [["GE5", K.AGAINST]]
        return ev
    g = H.mutate(DOMAIN, patch)
    assert "GI-BRIDGE" not in H.flagged(g)


def test_typing_the_non_converse_as_an_equivalence_is_caught():
    """b_0 = 4a_0 => t = 4 is a theorem; the converse is NOT, and the handoff
    says in as many words 'Do not state it as an equivalence.'  Retyping GE3
    EQUIVALENCE licenses the reverse reading, so the recorded warning becomes
    a caught error rather than a sentence someone has to remember."""
    g = H.load(DOMAIN)
    assert C.probe(g, "GC-T4-EMPIRICAL", "GE3", K.ALONG).licensed is False
    assert C.probe(g, "GC-T4-EMPIRICAL", "GE3", K.ALONG,
                   etype=K.EQUIVALENCE).licensed is True


def test_every_finding_names_its_discharge():
    for f in C.run(graph()):
        assert f.discharge and len(f.discharge) > 40, f.fid


def test_the_front_does_not_pass():
    """It should not.  Four live obligations stand."""
    assert C.exit_code(C.run(graph())) == 1
