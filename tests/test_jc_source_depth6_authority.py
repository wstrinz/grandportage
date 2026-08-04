"""Exact but deliberately source-unbound JC depth-6 boundary composition."""

import copy
import importlib.util
import json
from pathlib import Path

import pytest


pytestmark = pytest.mark.replay

from grandportage import check as C
from grandportage import cli
from grandportage import evidence as EV
from grandportage import format as F
from grandportage import store as S
from grandportage import verify as V


ROOT = Path(__file__).parents[1]
ADAPTER_PATH = (ROOT / "experiments" / "jc_h3_source_depth6" /
                "adapter.py")
FROZEN_PATH = ROOT / "fixtures" / "jc_source_depth6" / "boundary_v1.json"

_spec = importlib.util.spec_from_file_location(
    "jc_source_depth6_adapter", ADAPTER_PATH)
ADAPTER = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ADAPTER)


def _frozen():
    return json.loads(FROZEN_PATH.read_text(encoding="utf-8"))


def _graph_from_events(events):
    graph = S.Graph()
    graph.apply(F.meta_event())
    for event in events:
        graph.apply(event)
    graph.validate()
    return graph


def test_checked_in_boundary_projection_is_canonical_and_scope_honest():
    frozen = _frozen()
    report = ADAPTER.verify_frozen(frozen)

    assert report["verdict"] == "VERIFIED_FROZEN_DEPTH6_BOUNDARY"
    assert report["rung_commitments"] == 33
    assert report["R2B_terms"] == 3262
    assert report["beta_terms"] == 6124
    envelope = report["evidence_envelope"]
    assert envelope["graph_effect"] == EV.GRAPH_EFFECT_NONE
    assert envelope["licenses"] == [
        "exact_boundary_polynomials_decoded",
        "boundary_stratum_rewrites_may_be_checked",
    ]
    assert "does not expose" in envelope["outstanding_premises"][0]
    assert frozen["source_binding"] == "UNBOUND_DIGEST_COMMITMENTS_ONLY"


def test_native_sparse_coefficient_mutation_breaks_roundtrip_digest():
    frozen = _frozen()
    term = frozen["residuals"]["beta"]["polynomial"]["terms"][0]
    term["coefficient"] = "1" if term["coefficient"] != "1" else "2"

    with pytest.raises(ADAPTER.Depth6ReceiptError,
                       match="exact native sparse-map binding"):
        ADAPTER.verify_frozen(frozen)


def test_intermediate_rung_commitment_is_not_promoted_to_polynomial_proof():
    frozen = _frozen()

    assert frozen["schedule"]["intermediate_values"] == (
        "DIGEST_COMMITMENTS_ONLY")
    assert all(set(rung) <= {
        "stage", "depth", "row", "var", "pivot", "pivot_top_face",
        "terms", "value_sha256",
    } for rung in frozen["schedule"]["rungs"])
    assert "no replay of the 33-rung source march" in (
        frozen["authority_boundary"])


def test_exact_generic_and_discriminant_equivalences_verify_without_cas():
    graph = ADAPTER.graph_from_frozen(_frozen())

    assert V.ring_iso(graph, ADAPTER.GENERIC_EDGE)[0] == V.ISO_VERIFIED
    assert V.ring_iso(graph, ADAPTER.DISCRIMINANT_EDGE)[0] == V.ISO_VERIFIED
    assert C.run(graph) == []


def test_show_summarizes_sparse_ideal_generators(monkeypatch, capsys):
    graph = ADAPTER.graph_from_frozen(_frozen())
    monkeypatch.setattr(cli, "_load", lambda _args: graph)

    assert cli.cmd_show(object()) == 0
    output = capsys.readouterr().out
    assert "<sparse_polynomial_v1: 3262 terms>" in output
    assert "<sparse_polynomial_v1: 6125 terms>" in output

def test_boundary_model_has_no_silent_actual_source_or_cover_edge():
    graph = ADAPTER.graph_from_frozen(_frozen())

    assert graph.claims == {}
    assert all(ADAPTER.BOUNDARY_MODEL not in (edge["src"], edge["dst"])
               for edge in graph.edges.values())
    note = next(note for note in graph.notes
                if note.get("id") == ADAPTER.SOURCE_DEBT_NOTE)
    assert "No graph edge from the actual-source E-system is licensed" in (
        note["text"])
    assert "no checked parent-cover inference" in note["text"]


def test_generic_certificate_needs_the_alpha_inverse_equation():
    events = ADAPTER.graph_events(_frozen())
    source = next(event for event in events
                  if event.get("id") == ADAPTER.GENERIC_MODEL)
    source["generators"].pop()
    graph = _graph_from_events(events)

    verdict, why = V.ring_iso(graph, ADAPTER.GENERIC_EDGE)
    assert verdict == "UNVERIFIED"
    assert "wrong generator count" in why


def test_mutated_generic_cofactor_is_unverified_not_refuted():
    events = ADAPTER.graph_events(_frozen())
    edge = next(event for event in events
                if event.get("id") == ADAPTER.GENERIC_EDGE)
    edge["ring_iso_certificate"]["forward_cofactors"][3][3] = (
        "GP_INV_alpha+1")
    graph = _graph_from_events(events)

    verdict, why = V.ring_iso(graph, ADAPTER.GENERIC_EDGE)
    assert verdict == "UNVERIFIED"
    assert "not a mathematical refutation" in why


def test_discriminant_target_keeps_beta_relation_and_free_c7_5():
    graph = ADAPTER.graph_from_frozen(_frozen())
    target = graph.models[ADAPTER.DISCRIMINANT_BETA_MODEL]

    assert ADAPTER.BETA_ALIAS in target["generators"]
    assert "c7_5" in target["ring_vars"]
    assert "c7_5" not in target["generators"]


def test_current_native_receipt_reproduces_checked_in_projection():
    if not ADAPTER.DEFAULT_SOURCE.exists():
        pytest.skip("the sibling JC research checkout is not present")
    source_bytes = ADAPTER.DEFAULT_SOURCE.read_bytes()
    native = json.loads(source_bytes.decode("utf-8"))

    assert ADAPTER._encoded(
        ADAPTER.freeze_native(native, source_bytes)) == FROZEN_PATH.read_bytes()
