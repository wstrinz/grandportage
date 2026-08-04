"""End-to-end authority binding for the frozen JC p-axis contradiction."""

import copy
import hashlib
import importlib.util
import json
from pathlib import Path

import pytest

from grandportage import backend as B
from grandportage import check as C
from grandportage import cli
from grandportage import factor_power_contradiction as FPC
from grandportage import format as F
from grandportage import groebner as G
from grandportage import localization as L
from grandportage import provenance as P
from grandportage import store as S
from grandportage import verify as V


ROOT = Path(__file__).parents[1]
ADAPTER_PATH = ROOT / "experiments" / "jc_h3_p_axis" / "adapter.py"
FROZEN_PATH = ROOT / "fixtures" / "jc_p_axis" / "native_axis_slice_v1.json"
AUTHORITY_PATH = ROOT / "fixtures" / "jc_p_axis" / "localized_unit_ideal_v1.json"
FACTOR_PATH = (ROOT / "fixtures" / "jc_p_axis" /
               "factor_power_affine_contradiction_v1.json")

_spec = importlib.util.spec_from_file_location("jc_p_axis_adapter", ADAPTER_PATH)
ADAPTER = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ADAPTER)


def _frozen():
    raw = FROZEN_PATH.read_bytes()
    return json.loads(raw.decode("utf-8")), raw


def _execution_manifest():
    trace = [{
        "semantic_input_fingerprint": B.semantic_fingerprint("test", []),
        "program_fingerprint": B.text_fingerprint("test program"),
        "stdout_fingerprint": B.text_fingerprint("test output"),
        "stderr_fingerprint": B.text_fingerprint(""),
        "artifact_fingerprint": B.semantic_fingerprint("artifact", []),
        "returncode": 0,
        "aborted": False,
    }]
    return {
        "schema": 2,
        "contract": B.SINGULAR_CONTRACT,
        "implementation": B.SINGULAR_IMPLEMENTATION,
        "implementation_version": B.SINGULAR_IMPLEMENTATION_VERSION,
        "protocol_version": B.BACKEND_PROTOCOL_VERSION,
        "binary_version": "Singular p-axis test",
        "executions": trace,
        "trace_fingerprint": B.semantic_fingerprint(
            "backend_execution_trace", trace),
    }


def _representation(frozen):
    checked = L.verify(ADAPTER.authority_spec(frozen))
    return {
        "method": "localized_unit_ideal_v1",
        "claim": ADAPTER.EMPTY_CLAIM,
        "model": ADAPTER.AXIS_MODEL,
        "proof": checked["normalized"],
        "checked": checked["checked"],
    }


def _verified_graph():
    frozen, raw = _frozen()
    graph = ADAPTER.graph_from_frozen(frozen, raw)
    representation = _representation(frozen)
    event = V._verdict_event(
        graph, "certificate", ADAPTER.EMPTY_CLAIM, V.CERT_VERIFIED,
        "exact p-axis cofactor replay", representation,
        execution=_execution_manifest())
    graph.apply(event)
    return graph, event


def _graph_with_axis_updates(updates):
    frozen, raw = _frozen()
    events = ADAPTER.graph_events(frozen, raw)
    for event in events:
        if event.get("id") == ADAPTER.AXIS_MODEL:
            event.update(updates)
    graph = S.Graph()
    graph.apply(F.meta_event())
    for event in events:
        graph.apply(event)
    return graph


def test_show_renders_localized_proof_envelope(monkeypatch, capsys):
    graph, _event = _verified_graph()
    monkeypatch.setattr(cli, "_load", lambda _args: graph)

    assert cli.cmd_show(object()) == 0
    output = capsys.readouterr().out
    assert "rep=localized_unit_ideal_v1, 3 cofactor(s)" in output
    assert "VERIFIED" in output


def test_frozen_native_slice_has_the_expected_parent_binding():
    frozen, raw = _frozen()

    assert frozen["native_parent"]["sha256"] == ADAPTER.EXPECTED_NATIVE_SHA256
    assert hashlib.sha256(raw).hexdigest() == (
        "5c682ad0b2f5212fd21aba723d094793a212a1f59654a27b60969a9fa2bf0850")
    assert len(frozen["axis"]["zeroed"]) == 70
    assert frozen["axis"]["kept"] == ["p", "t", "c9_11", "I4"]


def test_checked_in_authority_fixture_is_exact_adapter_output():
    frozen, _raw = _frozen()
    expected = ADAPTER._encoded(ADAPTER.authority_spec(frozen))

    assert AUTHORITY_PATH.read_bytes() == expected


def test_factor_affine_receipt_and_authority_model_use_the_same_equations():
    frozen, _raw = _frozen()
    factor = json.loads(FACTOR_PATH.read_text(encoding="utf-8"))
    report = FPC.verify(factor)

    assert report["verdict"] == FPC.VERIFIED
    ring = frozen["ring_vars"]
    assert G.parse_polynomial(
        factor["factor_power"]["receipts"][0]["equation"], ring
    ) == G.parse_polynomial(frozen["factor"]["equation"], ring)
    assert G.parse_polynomial(
        factor["consequence"]["equation"], ring
    ) == G.parse_polynomial(frozen["consequence"]["equation"], ring)


def test_factor_proof_compiles_to_existing_localized_unit_certificate():
    frozen, _raw = _frozen()
    report = L.verify(ADAPTER.authority_spec(frozen))

    assert report["verdict"] == L.VERIFIED
    assert report["checked"] == {
        "target": "p^2*t^4",
        "generator_count": 3,
    }
    assert report["licenses"] == ["identity_in_declared_localization_only"]


def test_graph_verdict_mints_only_local_empty_authority():
    graph, event = _verified_graph()

    claim = graph.claims[ADAPTER.EMPTY_CLAIM]
    assert claim["certificate_verdict"] == V.CERT_VERIFIED
    assert claim["representation"]["method"] == "localized_unit_ideal_v1"
    assert graph.verdicts[event["id"]]["current"] is True
    assert C.effective_certificate(claim) == "LOCALIZED_UNIT_IDEAL_CERT"

    licensed, trace = ADAPTER.parent_refusal(graph)
    assert not licensed
    assert "does NOT license EMPTY" in trace[0][3]


def test_certificate_name_without_verdict_grants_no_authority():
    frozen, raw = _frozen()
    graph = ADAPTER.graph_from_frozen(frozen, raw)

    claim = graph.claims[ADAPTER.EMPTY_CLAIM]
    assert C.effective_certificate(claim) is None
    findings = [
        finding for finding in C.run(graph)
        if finding.fid.endswith(ADAPTER.EMPTY_CLAIM)
    ]
    assert any("name alone grants no effective certificate"
               in finding.detail for finding in findings)


@pytest.mark.parametrize("updates", [
    {"generators": [
        "15*t^3+1",
        "10*t*c9_11+14*p*t^2",
        "5*c9_11^2+10*c9_11*p*t+5*p^2*t^2",
    ]},
    {"open_conditions": ["p"]},
])
def test_equation_or_guard_mutation_refuses_old_authority(updates):
    _original, event = _verified_graph()
    changed = _graph_with_axis_updates(updates)

    changed.apply(copy.deepcopy(event))
    stored = changed.verdicts[event["id"]]
    assert stored["current"] is False
    assert changed.claims[ADAPTER.EMPTY_CLAIM].get(
        "certificate_verdict") is None


@pytest.mark.parametrize("updates", [
    {"point_universe": S.BASE_POINT_UNIVERSE},
    {"chart": "q"},
    {"cite": "sha256:" + "0" * 64},
])
def test_scope_or_source_binding_mutation_stales_old_authority(updates):
    _original, event = _verified_graph()
    changed = _graph_with_axis_updates(updates)
    changed.apply(copy.deepcopy(event))

    stored = changed.verdicts[event["id"]]
    assert stored["current"] is False
    assert "fingerprint" in stored["stale_reason"]
    assert changed.claims[ADAPTER.EMPTY_CLAIM].get(
        "certificate_verdict") is None


def test_verifier_input_fingerprint_contains_the_frozen_source_digest():
    frozen, raw = _frozen()
    graph = ADAPTER.graph_from_frozen(frozen, raw)
    payload = P.input_payload(graph, "certificate", ADAPTER.EMPTY_CLAIM)
    encoded = json.dumps(payload, sort_keys=True)

    assert ADAPTER.EXPECTED_NATIVE_SHA256 in encoded
    assert "5c682ad0b2f5212fd21aba723d094793a" in encoded


def test_adapter_refuses_any_change_to_the_native_parent_bytes():
    fake_native = {
        "schema": ADAPTER.NATIVE_SCHEMA,
        "chart": "p",
    }
    with pytest.raises(ValueError, match="native p-window receipt changed"):
        ADAPTER.freeze_native(fake_native, b"{}")


def test_frozen_model_does_not_claim_full_chart_source_or_h3_authority():
    frozen, _raw = _frozen()
    boundary = frozen["authority_boundary"]

    assert "no full p-chart" in boundary
    assert "actual-source-membership" in boundary
    assert "H3 authority" in boundary
