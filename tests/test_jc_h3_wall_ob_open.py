import copy
import hashlib
import importlib.util
import json
from pathlib import Path

import pytest


pytestmark = pytest.mark.replay

from grandportage import backend as B
from grandportage import check as C
from grandportage import localization as L
from grandportage import store as S
from grandportage import verify as V


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "experiments" / "jc_h3_wall_ob_open" / "adapter.py"


def _load():
    spec = importlib.util.spec_from_file_location("jc_wall_ob_open_test", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _frozen(module):
    raw = module.DEFAULT_FROZEN.read_bytes()
    return json.loads(raw.decode("utf-8")), raw


MODULE = _load()
FROZEN, FROZEN_BYTES = _frozen(MODULE)
VALIDATION_REPORT = MODULE.validate_frozen(FROZEN)


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
        "binary_version": "Singular wall-obstruction test",
        "executions": trace,
        "trace_fingerprint": B.semantic_fingerprint(
            "backend_execution_trace", trace),
    }


def _verified_graph(module):
    frozen, raw = _frozen(module)
    graph = module.graph_from_frozen(frozen, raw)
    checked = L.verify(module.graph_authority_spec(frozen))
    representation = {
        "method": "localized_unit_ideal_v1",
        "claim": module.EMPTY_CLAIM,
        "model": module.MODEL,
        "proof": checked["normalized"],
        "checked": checked["checked"],
    }
    event = V._verdict_event(
        graph, "certificate", module.EMPTY_CLAIM, V.CERT_VERIFIED,
        "exact on-wall dead-row cofactor replay", representation,
        execution=_execution_manifest())
    graph.apply(event)
    return graph, event


def test_frozen_polynomials_compile_to_existing_localized_unit_identity():
    module, frozen, raw, report = (
        MODULE, FROZEN, FROZEN_BYTES, VALIDATION_REPORT)

    assert hashlib.sha256(raw).hexdigest() == module.EXPECTED_FROZEN_SHA256
    assert report["verdict"] == L.VERIFIED
    assert report["checked"]["generator_count"] == 3
    assert len(frozen["polynomials"]["value_24_delta"]["terms"]) == 502
    assert len(frozen["polynomials"]["OB_ambient"]["terms"]) == 499
    assert frozen["scope"]["constructible_piece"] == "R=0 and OB!=0"


def test_checked_in_authority_fixture_is_exact_adapter_output():
    module, frozen = MODULE, FROZEN
    assert module.DEFAULT_AUTHORITY.read_bytes() == module._encoded(
        module.authority_spec(frozen))


def test_graph_verdict_mints_only_local_empty_on_exact_consequence_model():
    module = MODULE
    graph, event = _verified_graph(module)
    claim = graph.claims[module.EMPTY_CLAIM]

    assert claim["certificate_verdict"] == V.CERT_VERIFIED
    assert graph.verdicts[event["id"]]["current"] is True
    assert C.effective_certificate(claim) == "LOCALIZED_UNIT_IDEAL_CERT"
    assert len(graph.models) == 1
    assert "no automatic nine-body" in claim["caveat"]


def test_certificate_name_without_current_verdict_has_no_authority():
    module, frozen, raw = MODULE, FROZEN, FROZEN_BYTES
    graph = module.graph_from_frozen(frozen, raw)
    assert C.effective_certificate(graph.claims[module.EMPTY_CLAIM]) is None


def test_removing_ob_guard_stales_old_authority():
    module, frozen, raw = MODULE, FROZEN, FROZEN_BYTES
    _original, event = _verified_graph(module)
    events = module.graph_events(frozen, raw)
    events[0]["open_conditions"] = ["t", "p", "c2_3", "c5_7"]
    changed = S.Graph()
    from grandportage import format as F
    changed.apply(F.meta_event())
    for item in events:
        changed.apply(item)
    changed.apply(copy.deepcopy(event))

    assert changed.verdicts[event["id"]]["current"] is False
    assert changed.claims[module.EMPTY_CLAIM].get(
        "certificate_verdict") is None


def test_scope_refuses_parent_component_source_and_h3_promotion():
    module, frozen = MODULE, FROZEN
    boundary = frozen["authority_boundary"]
    assert "exact R=0, OB!=0 dead-row consequence model" in boundary
    assert "no automatic nine-body" in boundary
    assert "component" in boundary and "actual-source" in boundary
    assert "H3" in boundary and "verdict" in boundary
    assert "complete nine-body parent" in frozen["scope"]["not_materialized"]


def test_default_validation_does_not_import_native_producer(monkeypatch):
    module, frozen = MODULE, FROZEN
    monkeypatch.setattr(module, "_extract_native_polynomials",
                        lambda *_a, **_k: pytest.fail("native producer imported"))
    assert module.validate_frozen(frozen)["verdict"] == L.VERIFIED


def test_native_bindings_are_current_when_sibling_checkout_exists():
    module = MODULE
    if not module.NATIVE_ROOT.exists():
        pytest.skip("sibling JC checkout is not present")
    module.check_native_bindings(FROZEN)
