#!/usr/bin/env python3
"""Focused offline replay for the two historical Cramer exponent candidates.

Imports only the pinned historical adapter and validates its frozen fixture.  It
never calls its native_replay, fixture-construction, or binding-check paths.
"""
from __future__ import annotations
import argparse, hashlib, importlib.util, json, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HISTORY = ROOT / "oracle" / "history" / "checkout"
ADAPTER_PATH = HISTORY / "experiments" / "jc_h3_b0_compatibility" / "adapter.py"
FIXTURE_PATH = HISTORY / "fixtures" / "jc_b0_compatibility" / "class_v1.json"
CANDIDATE_DIR = ROOT / "reports" / "cramer-case-candidates"
PIN = "7991c9052f13e8dcaa78b5eae36f31663e080c1e"
EXPECTED = {
    "fixture": "faeda936b84f5f4ba68f55eeb4cc00d34a6c5f7e6e60f7312e4e3f21f1ff0e95",
    "adapter": "cc8112c8f744bfdde93dac1f4203bfa0fe520464b0d3f8b8e83d02ee9b19928e",
    "test": "bbaf7f288b7d27c667e71cec4af9af18399ffa913aeeecd179509e56bb3519ba",
}

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)

def load_adapter():
    spec = importlib.util.spec_from_file_location("pinned_cramer_adapter", ADAPTER_PATH)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module

def check_candidate(case: dict) -> None:
    binding = case["inputs"]["historical_binding"]
    require(binding["history_pin"] == PIN, "wrong history pin")
    require(binding["fixture_sha256"] == EXPECTED["fixture"], "wrong fixture binding")
    require(binding["adapter_sha256"] == EXPECTED["adapter"], "wrong adapter binding")
    require(case["inputs"]["model"]["guards"] == ["c2_3", "p", "det5"], "guard distinction changed")
    require(case["inputs"]["five_column_cramer_solve"]["denominator"] == "det5", "wrong Cramer denominator")
    require(case["inputs"]["lambda_fiber_profile"]["quadratic_term"] == "one c8_9^2 coefficient", "missing square-term threshold")
    require(case["id"] in {"GP-X406", "GP-X407"}, "unexpected candidate id")
    expected_exponent = 1 if case["id"] == "GP-X406" else 2
    expected_verdict = "REFUSE" if expected_exponent == 1 else "ACCEPT"
    require(case["inputs"]["asserted_clearing_exponent"] == expected_exponent, "wrong candidate exponent")
    require(case["expected"]["verdict"] == expected_verdict, "wrong candidate verdict")

def run() -> dict:
    started = time.perf_counter()
    require(sha(FIXTURE_PATH) == EXPECTED["fixture"], "fixture SHA-256 drift")
    require(sha(ADAPTER_PATH) == EXPECTED["adapter"], "adapter SHA-256 drift")
    test_path = HISTORY / "tests" / "test_jc_h3_b0_compatibility.py"
    require(sha(test_path) == EXPECTED["test"], "test SHA-256 drift")
    cases = [json.loads((CANDIDATE_DIR / name).read_text(encoding="utf-8")) for name in ("GP-X406.json", "GP-X407.json")]
    for case in cases:
        check_candidate(case)
    adapter = load_adapter()
    fixture = json.loads(FIXTURE_PATH.read_text(encoding="utf-8"))
    checked = adapter.validate_fixture_value(fixture)
    push = fixture["pushforward"]
    numerator = adapter._decode_univariate(push["power1_numerator"], "power-one numerator")
    denominator = adapter._decode_univariate(push["power1_denominator"], "power-one denominator")
    remainder = adapter._udivmod(numerator, denominator)[1]
    require(remainder != [adapter.K_ZERO], "power one unexpectedly clears")
    require(checked["clearing_exponent"] == 2 and checked["power_one_refuted"] is True, "historical threshold replay failed")
    return {
        "schema_version": 1,
        "status": "focused_offline_historical_replay",
        "history_pin": PIN,
"candidate_ids": [case["id"] for case in cases],
        "source_anchors": [
            "reports/PHASE-0A-SIX-DELETED-NOTES-REVIEW.json#/records/2/incidents/1",
            "deleted blob c231b42735dac46181ec92c1dabd875a2f12d4d9 lines 8-13",
            "oracle/history/checkout/experiments/jc_h3_b0_compatibility/adapter.py:496-500,750-789",
            "oracle/history/checkout/tests/test_jc_h3_b0_compatibility.py:36-45,71-83",
            "oracle/history/checkout/fixtures/jc_b0_compatibility/class_v1.json:68322-68349,91072+",
        ],
        "runtime_preflight": {
            "fixture_bytes": FIXTURE_PATH.stat().st_size,
            "adapter_entry": "validate_fixture_value",
            "native_replay_called": False,
            "native_binding_check_called": False,
            "fixture_construction_called": False,
            "external_cas_called": False,
        },
        "bindings": {"fixture_sha256": sha(FIXTURE_PATH), "adapter_sha256": sha(ADAPTER_PATH), "test_sha256": sha(test_path)},
        "observations": {
            "positive": {"id": "GP-X407", "historical_clearing_exponent": checked["clearing_exponent"], "phi_terms": checked["phi_terms"], "chart_determinant": checked["chart_determinant"], "result": "ACCEPT_AT_HISTORICAL_EXACT_REPLAY_LAYER"},
            "negative": {"id": "GP-X406", "power_one_refuted": checked["power_one_refuted"], "remainder_is_nonzero": remainder != [adapter.K_ZERO], "result": "REFUSE_AT_HISTORICAL_EXACT_REPLAY_LAYER"},
        },
        "elapsed_seconds": round(time.perf_counter() - started, 6),
        "limits": ["No corpus/oracle route was changed or run.", "No native producer, CAS, campaign, graph, or source binding check was invoked.", "The result is fixture-bound and does not prove a general denominator theorem or any graph authority."],
    }

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))
if __name__ == "__main__":
    main()



