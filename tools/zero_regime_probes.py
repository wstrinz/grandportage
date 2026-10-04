"""Pinned zero-regime facts with an explicit reference arithmetic minimality check.

The retained adapter validates the fixture and identifies R5/R6 as zero. It has
no native verifier for per-regime minimality; the degree comparison below is
our transparent arithmetic control, not a predecessor verdict.
"""
import hashlib
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PIN = "7991c9052f13e8dcaa78b5eae36f31663e080c1e"
ADAPTER = (ROOT / "oracle/history/checkout/experiments"
           / "jc_h3_adjoint_recurrence/adapter.py")


def _pinned_fixture(expected_sha256):
    spec = importlib.util.spec_from_file_location("historical_zero_regime", ADAPTER)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    raw = module.DEFAULT_FIXTURE.read_bytes()
    actual = hashlib.sha256(raw).hexdigest()
    if actual != expected_sha256 or actual != module.EXPECTED_FIXTURE_SHA256:
        raise ValueError("Pinned recurrence fixture SHA-256 mismatch")
    fixture = json.loads(raw.decode("utf-8"))
    _, premises = module.validate_fixture_value(fixture)
    return module, fixture, premises


def probe(case, route):
    if route["historical_commit"] != PIN:
        raise ValueError("Wrong historical recurrence revision")
    d = case["inputs"]
    if (d["regimes"] != ["R5", "R6"] or d["zero_from"] != 14
            or d["operator_coefficient_domain"] != "QQ"
            or d["shift_convention"] != "(S B)_d = B_(d+1)"
            or d["unit_operator"] != {"0": "1"}):
        raise ValueError("Unknown zero-regime arithmetic interpretation")
    module, fixture, premises = _pinned_fixture(d["fixture_sha256"])
    if (premises["zero_from"] != 14 or not premises["endpoint_nonzero"]
            or premises["pure_forward_annihilator"] != "S^8"
            or premises["S7_annihilates"]):
        raise ValueError("Global unilateral control drifted")
    records = fixture["native_certificate"]["regimes"]
    selected = {r["regime"]: r for r in records if r["regime"] in d["regimes"]}
    if set(selected) != set(d["regimes"]):
        raise ValueError("Zero regime missing")
    if (selected["R5"]["depths"] != [14, 14]
            or selected["R5"]["open_ended"] is not False
            or selected["R6"]["depths"] != [15, 24]
            or selected["R6"]["open_ended"] is not True):
        raise ValueError("Zero regime domains changed")
    if any(selected[name]["columns"] or selected[name]["matrix"]
           for name in d["regimes"]):
        raise ValueError("Regime is not the pinned empty matrix")
    decoded = module._decode_regimes(fixture["native_certificate"])
    checked_depths = (14, 15, 24, 25)
    if any(any(module._padded_at(depth, decoded).values())
           for depth in checked_depths):
        raise ValueError("Pinned padded sequence is nonzero in zero regime")
    # The adapter's structural branch maps every d >= 14 to ZERO. Its R6
    # declaration is open-ended. The local operator identity is 1 * 0 = 0.
    common = {
        "regimes": ["R5", "R6"],
        "regime_zero_structure": "R5 and open-ended R6 have no columns or matrix entries; padded B_d is zero from 14",
        "sampled_zero_depths": list(checked_depths),
        "unit_operator_nonzero": True,
        "unit_shift_degree": 0,
        "unit_annihilates_each_zero_regime": True,
        "global_control_case": "GP-X118",
        "global_endpoint_nonzero": premises["endpoint_nonzero"],
        "global_unilateral_S8_preserved": True,
        "native_per_regime_minimality_verdict": None,
        "arithmetic_authority": "reference_exact_identity_and_shift_degree",
        "external_execution": False,
    }
    if d["control"] == "unit_annihilator":
        return {"observed_verdict": "ACCEPT",
                "reason": "The nonzero degree-zero unit acts as 1*0=0 on each identically zero regime.",
                **common}
    if d["control"] != "reject_blanket_minimality":
        raise ValueError("Unknown zero-regime control")
    if (d["claimed_minimal_operator"] != {"0": "-1", "1": "1"}
            or d["minimality_order"] != "shift_degree"):
        raise ValueError("Unknown claimed minimality comparison")
    claimed_shift_degree = 1
    if not common["unit_annihilates_each_zero_regime"] or not (0 < claimed_shift_degree):
        raise ValueError("Unit counterexample did not refute minimality")
    return {"observed_verdict": "REFUSE",
            "reason": "The degree-zero unit annihilates R5 and R6, so degree-one S-1 is not minimal on either zero regime.",
            "claimed_shift_degree": claimed_shift_degree,
            "reference_counterexample": "1 annihilates the zero sequence",
            **common}
