"""Bounded pinned depth-eight block commitment and projection controls."""
import copy
import hashlib
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HISTORY = ROOT / "oracle/history/checkout"
PIN = "7991c9052f13e8dcaa78b5eae36f31663e080c1e"
ADAPTER = HISTORY / "experiments/jc_h3_b0_free_plane/depth8_adapter.py"
EXPECTED = {
    "raw_coefficient": ("A2", "set", ("raw_columns", "E[2,19]", "c8_5", 0, 1), "-4"),
    "transported_block": ("A4", "set", ("transported_block", 0, 1, 0, 1), "-4"),
    "graph_effect": ("M1", "set", ("projection", "graph_effect"), "POINT_INCLUSION"),
    "derivative_transport": (
        "M1", "set", ("projection", "transport", "D7"),
        "d/dc7_4+(3/2)*c2_3*d/dc9_7"),
    "residual_export": (
        "M1", "set", ("projection", "checked_block", "residual_status"), "EXPORTED"),
    "source_equivalence": (
        "M1", "set", ("projection", "semantic_layer"),
        "EQUIVALENT_ACTUAL_SOURCE_FIBER"),
    "no_inversion_ledger": (
        "A11", "remove",
        ("native_certificate", "localization_ledger", "never_inverted"), "R"),
}


def _load():
    spec = importlib.util.spec_from_file_location("historical_depth8_block_probe", ADAPTER)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _fixture(module, digest):
    raw = module.DEFAULT_FIXTURE.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if actual != digest or actual != module.EXPECTED_FIXTURE_SHA256:
        raise ValueError("Historical depth-eight block fixture SHA-256 mismatch")
    return json.loads(raw.decode("utf-8"))


def _mutate(fixture, mutation, expected):
    gate, operation, path, value = expected
    if (mutation["op"] != operation
            or tuple(mutation["path"]) != path
            or mutation["value"] != value):
        raise ValueError("Case mutation differs from the pinned control")
    target = fixture
    for key in path[:-1]:
        target = target[key]
    key = path[-1]
    if operation == "set":
        if target[key] != mutation["original"]:
            raise ValueError("Case original value differs from pinned fixture")
        target[key] = value
    else:
        entries = target[key]
        if entries.count(value) != 1:
            raise ValueError("No-inversion ledger entry is not unique")
        entries.remove(value)


def probe(case, route):
    if route["historical_commit"] != PIN:
        raise ValueError("Wrong historical revision")
    d = case["inputs"]
    module = _load()
    fixture = _fixture(module, d["fixture_sha256"])
    baseline = module.validate_fixture_value(copy.deepcopy(fixture))
    if d["control"] == "baseline":
        if "mutation" in d or route["layer"] != "historical_necessary_block_replay":
            raise ValueError("Baseline route or payload changed")
        report = module.report_from_checked_fixture(fixture, baseline)
        if (report["graph_effect"] != "NONE"
                or report["checked_block"]["residual_status"] != "NOT_EXPORTED"):
            raise ValueError("Baseline block gained unreviewed authority")
        return {
            "observed_verdict": "ACCEPT",
            "reason": "Pinned necessary rank-two block and symbolic compatibility replayed.",
            "checked_instance": baseline,
            "raw_report_verdict": report["verdict"],
            "graph_effect": report["graph_effect"],
            "residual_status": report["checked_block"]["residual_status"],
            "external_execution": False,
        }
    control = d["control"]
    if control not in EXPECTED:
        raise ValueError("Unknown depth-eight block control")
    expected = EXPECTED[control]
    gate = expected[0]
    if route["expected_gate"] != gate:
        raise ValueError("Route gate differs from pinned control")
    _mutate(fixture, d["mutation"], expected)
    try:
        module.validate_fixture_value(fixture)
    except module.Depth8BlockEvidenceError as exc:
        failure = str(exc)
        if not failure.startswith(gate + ":"):
            raise
        return {
            "observed_verdict": "REFUSE",
            "reason": failure,
            "baseline_checked_instance": baseline,
            "control": control,
            "rejection_gate": gate,
            "outer_fixture_digest_rejection": False,
            "mathematical_invalidity_established": False,
            "graph_effect": "NONE",
            "external_execution": False,
        }
    raise ValueError("Changed depth-eight block unexpectedly validated")
