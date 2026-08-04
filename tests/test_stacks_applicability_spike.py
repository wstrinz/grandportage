import copy
from pathlib import Path

import pytest

from experiments.stacks_applicability import sidecar as S


ROOT = Path(__file__).resolve().parents[1]
SPIKE = ROOT / "experiments" / "stacks_applicability"


def _shelf():
    return S.load_json(SPIKE / "theorem_shelf.json")


def _packet(tag):
    return S.load_json(SPIKE / "applications" / ("jc_%s.json" % tag))


def test_three_theorem_shelf_is_portably_pinned():
    indexed = S.validate_shelf(_shelf())
    assert set(indexed) == {"00IP", "01Z2", "08SL"}
    assert all(theorem["statement_sha256"] ==
               S.sha256_text(theorem["statement_tex"])
               for theorem in indexed.values())


def test_discovery_scores_cannot_leak_into_a_pin():
    shelf = _shelf()
    shelf["theorems"][0]["score"] = 0.999
    with pytest.raises(S.SidecarError, match="discovery-only"):
        S.validate_shelf(shelf)


@pytest.mark.parametrize("tag", ["00IP", "01Z2", "08SL"])
def test_live_jc_application_is_refused_and_has_no_graph_effect(tag):
    audit = S.audit_application(_shelf(), _packet(tag))
    assert audit["decision"] == "REFUSED_MISSING_HYPOTHESES"
    assert audit["authority_if_recorded"] == "NONE"
    assert audit["graph_effect"] == "NONE"
    assert audit["unresolved"]


def test_krull_audit_separates_printed_and_bridge_premises():
    audit = S.audit_application(_shelf(), _packet("00IP"))
    unresolved = {(item["kind"], item["id"])
                  for item in audit["unresolved"]}
    assert ("theorem_hypothesis", "module_finite") in unresolved
    assert ("application_bridge", "class_in_every_power") in unresolved
    assert ("application_bridge", "class_identified") in unresolved


def test_omitting_a_printed_hypothesis_is_malformed_not_merely_missing():
    packet = _packet("01Z2")
    packet["hypotheses"] = packet["hypotheses"][:-1]
    with pytest.raises(S.SidecarError, match="hypothesis map differs"):
        S.audit_application(_shelf(), packet)


def test_mutating_theorem_statement_digest_breaks_the_application_weld():
    packet = _packet("08SL")
    packet["theorem_pin"]["statement_sha256"] = "0" * 64
    with pytest.raises(S.SidecarError, match="does not match pinned"):
        S.audit_application(_shelf(), packet)


def test_all_bound_still_waits_for_external_theorem_acceptance():
    shelf = _shelf()
    packet = _packet("08SL")
    for item in packet["hypotheses"] + packet["application_premises"]:
        item["status"] = "BOUND"
        item["gp_claim"] = "SYNTHETIC-%s" % item["id"]
        item.pop("why", None)
    audit = S.audit_application(shelf, packet)
    assert audit["decision"] == "HELD_EXTERNAL_THEOREM_NOT_ACCEPTED"
    assert audit["graph_effect"] == "NONE"


def test_external_acceptance_only_makes_a_packet_ready_for_review():
    shelf = _shelf()
    packet = _packet("08SL")
    packet["theorem_acceptance"] = "EXTERNAL_THEOREM_ACCEPTED"
    for item in packet["hypotheses"] + packet["application_premises"]:
        item["status"] = "BOUND"
        item["gp_claim"] = "SYNTHETIC-%s" % item["id"]
        item.pop("why", None)
    audit = S.audit_application(shelf, packet)
    assert audit["decision"] == "READY_FOR_GP_REVIEW"
    assert audit["authority_if_recorded"] == "EXTERNAL_HUMAN_THEOREM"
    assert audit["graph_effect"] == "NONE"


def test_discovery_parser_accepts_only_official_stacks_tag_urls():
    good = {
        "name": "Lemma 10.51.4.",
        "slogan": "Krull intersection",
        "score": 0.73,
        "paper": {"link": "https://stacks.math.columbia.edu/tag/00IP"},
    }
    candidate = S._discovery_candidate(good)
    assert candidate["tag"] == "00IP"
    bad = copy.deepcopy(good)
    bad["paper"]["link"] = "https://example.test/tag/00IP"
    assert S._discovery_candidate(bad) is None


def test_rendered_packet_shouts_the_authority_boundary():
    rendered = S.render_application(_shelf(), _packet("00IP"))
    assert "REFUSED_MISSING_HYPOTHESES" in rendered
    assert "Application-specific bridge premises" in rendered
    assert "Graph effect: **NONE**" in rendered
