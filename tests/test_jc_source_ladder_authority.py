"""Graph-bound composition of the frozen five-step source ladder."""

import importlib.util
import json
from pathlib import Path

import pytest


pytestmark = pytest.mark.replay

from grandportage import check as C
from grandportage import verify as V


ROOT = Path(__file__).parents[1]
ADAPTER_PATH = (ROOT / "experiments" / "jc_h3_source_ladder" /
                "authority_adapter.py")
FIXTURE = (ROOT / "fixtures" / "jc_source_ladder" /
           "localized_triangular_solve_chain_v1.json")
SECOND_FIXTURE = (ROOT / "fixtures" / "jc_source_ladder" /
                  "localized_triangular_solve_chain_v2_second_face.json")
_spec = importlib.util.spec_from_file_location(
    "jc_source_ladder_authority", ADAPTER_PATH)
ADAPTER = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ADAPTER)


def _specification():
    return json.loads(FIXTURE.read_text(encoding="utf-8"))


def _second_specification():
    return json.loads(SECOND_FIXTURE.read_text(encoding="utf-8"))


def test_chain_compiles_to_exact_algebraized_localization_models():
    graph, compiled = ADAPTER.graph_from_spec(_specification())
    source = graph.models[ADAPTER.SOURCE_MODEL]
    target = graph.models[ADAPTER.TARGET_MODEL]
    edge = graph.edges[ADAPTER.EDGE]

    assert compiled["chain_report"]["checked_steps"] == 5
    assert compiled["inverse_variables"] == ["GP_INV_t"]
    assert source["ring_vars"][-1] == "GP_INV_t"
    assert source["generators"][-1] == "t*GP_INV_t-1"
    assert target["generators"][:5] == [
        "I4", "c6_9", "c9_14", "I1", "Im1"]
    assert target["generators"][-1] == "t*GP_INV_t-1"
    assert edge["forward"]["I4"] == "(-5/2)*c3_5+I4"
    assert edge["inverse"]["I4"] == "(5/2)*c3_5+I4"
    assert edge["forward"]["t"] == "t"
    assert edge["forward"]["GP_INV_t"] == "GP_INV_t"
    assert edge["ring_iso"] is True
    assert edge.get("ring_iso_verdict") is None
    assert C.run(graph) == []


def test_compiler_replays_chain_before_emitting_graph_events():
    mutated = _specification()
    mutated["steps"][2]["solution"] = "0"

    with pytest.raises(Exception, match="equation is not"):
        ADAPTER.compile_events(mutated)


def test_inverse_coordinate_collision_fails_closed():
    mutated = _specification()
    mutated["ring_vars"].append("GP_INV_t")
    for step in mutated["steps"]:
        # The state fingerprints become stale first, which is already a refusal.
        step["input_state_fingerprint"] = "sha256:" + "0" * 64

    with pytest.raises(Exception):
        ADAPTER.compile_events(mutated)


def test_normalization_bearing_second_face_compiles_with_exact_context():
    graph, compiled = ADAPTER.graph_from_spec(_second_specification())
    source = graph.models[ADAPTER.SECOND_SOURCE_MODEL]
    target = graph.models[ADAPTER.SECOND_TARGET_MODEL]

    assert compiled["edge_id"] == ADAPTER.SECOND_EDGE
    assert compiled["chain_report"]["checked_steps"] == 5
    assert source["generators"][0] == "(15)*t^3+1"
    assert target["generators"][0] == "(15)*t^3+1"
    assert target["generators"][1:6] == [
        "c3_4", "c6_8", "c9_13", "c5_6", "c4_4"]
    assert compiled["inverse_variables"] == []
    assert compiled["inverse_witnesses"] == {"t": "(-15)*t^2"}
    assert "GP_INV_t" not in source["ring_vars"]
    assert "GP_INV_t" not in target["ring_vars"]
    assert C.run(graph) == []


def test_exact_certificate_verifies_normalization_bearing_second_face():
    graph, compiled = ADAPTER.graph_from_spec(_second_specification())
    verdict, why = V.ring_iso(graph, compiled["edge_id"], timeout=180)

    assert verdict == V.ISO_VERIFIED, why
    assert "backend-free proof" in why


def test_mutated_exact_certificate_is_unverified_not_a_refutation():
    graph, compiled = ADAPTER.graph_from_spec(_second_specification())
    certificate = graph.edges[compiled["edge_id"]]["ring_iso_certificate"]
    certificate["forward_cofactors"][1][0] = "0"

    verdict, why = V.ring_iso(graph, compiled["edge_id"])

    assert verdict == V.UNVERIFIED
    assert "invalid evidence is not a mathematical refutation" in why


@pytest.mark.live
def test_real_singular_verifies_compiled_chain_ring_isomorphism():
    graph, _compiled = ADAPTER.graph_from_spec(_specification())
    graph.edges[ADAPTER.EDGE].pop("ring_iso_certificate")
    verdict, why = V.ring_iso(graph, ADAPTER.EDGE, timeout=180)

    assert verdict == V.ISO_VERIFIED, why


@pytest.mark.live
def test_real_singular_refuses_chain_when_inverse_equation_is_removed():
    graph, _compiled = ADAPTER.graph_from_spec(_specification())
    graph.edges[ADAPTER.EDGE].pop("ring_iso_certificate")
    graph.models[ADAPTER.SOURCE_MODEL]["generators"] = (
        graph.models[ADAPTER.SOURCE_MODEL]["generators"][:-1])
    verdict, why = V.ring_iso(graph, ADAPTER.EDGE, timeout=180)

    assert verdict == V.ISO_NOT_ISO
    assert "does not pull back" in why
