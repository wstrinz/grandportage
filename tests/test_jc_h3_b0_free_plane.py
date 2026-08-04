import copy
import hashlib
import importlib.util
import json
import sys
import tempfile
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "experiments" / "jc_h3_b0_free_plane" / "adapter.py"


def _load():
    spec = importlib.util.spec_from_file_location("jc_b0_free_plane_test", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


MODULE = _load()


@pytest.fixture(scope="module")
def frozen():
    raw = MODULE.DEFAULT_FIXTURE.read_bytes()
    return raw, json.loads(raw.decode("utf-8"))


@pytest.fixture(scope="module")
def checked(frozen):
    return MODULE.validate_fixture_value(frozen[1])


def test_complete_factor_ledger_and_affine_round_trip(checked, frozen):
    assert checked == {
        "loaded_bodies": 35,
        "distinct_bodies": 31,
        "live_bodies": [
            "E321", "VD", "d7rung:row1/c9_7", "d7rung:row4/c5_0"],
        "ambient_factors": ["c5_7", "Delta"],
        "S2_factors": ["c5_7"],
        "affine_round_trip": True,
        "downstream_equations": 8,
    }
    assert hashlib.sha256(frozen[0]).hexdigest() == (
        MODULE.EXPECTED_FIXTURE_SHA256)


def test_report_has_no_graph_or_research_promotion(checked, frozen):
    report = MODULE.report_from_checked_fixture(frozen[1], checked)
    assert report["verdict"] == "VERIFIED_EXCEPTIONAL_FACTOR_LEDGER"
    assert report["graph_effect"] == "NONE"
    assert report["evidence_envelope"]["graph_effect"] == "NONE"
    assert "six coefficients" in report["first_open_obligation"]
    refused = " ".join(report["does_not_license"])
    assert "R=0" in refused and "component" in refused
    assert "source" in refused and "H3" in refused


def _change_vd_c85(value):
    value["columns"]["VD"]["c8_5"][0][1] = "14"


def _change_pivot_sign(value):
    value["columns"]["d7rung:row1/c9_7"]["c7_4"][0][1] = "3/2"


@pytest.mark.parametrize("mutator,check", [
    (lambda p: p["projection"].update({"graph_effect": "NONEMPTY"}), "M3"),
    (lambda p: p["projection"]["checked_result"]["c7_4_affine_pivot"].update(
        {"role": "NINTH_COMPATIBILITY_EQUATION"}), "M3"),
    (lambda p: p["projection"]["model"]["equations"].remove("c5_7=0"), "M3"),
    (lambda p: p["projection"]["model"]["equations"].remove("Delta=0"), "M3"),
    (lambda p: p["projection"].update({"first_open_obligation": "CLOSED"}), "M3"),
    (_change_vd_c85, "A3"),
    (_change_pivot_sign, "A3"),
])
def test_scope_and_arithmetic_mutations_refuse(frozen, mutator, check):
    changed = copy.deepcopy(frozen[1])
    mutator(changed)
    with pytest.raises(MODULE.FreePlaneEvidenceError, match=check):
        MODULE.validate_fixture_value(changed)


def test_changed_native_binding_refuses(frozen):
    changed = copy.deepcopy(frozen[1])
    changed["source_bindings"]["f2_h3_b0_free_plane_receipt.json"] = "0" * 64
    with pytest.raises(MODULE.FreePlaneEvidenceError, match="F3"):
        MODULE.validate_fixture_value(changed)


def test_changed_fixture_refuses_by_digest(frozen):
    changed = copy.deepcopy(frozen[1])
    changed["authority_boundary"] = "widened"
    with tempfile.TemporaryDirectory(prefix="gp-free-plane-", dir=ROOT) as temp:
        path = Path(temp) / "changed.json"
        path.write_bytes(MODULE.encoded(changed))
        with pytest.raises(MODULE.FreePlaneEvidenceError, match="F4"):
            MODULE.verify_fixture(path)


def test_native_bindings_are_current_when_sibling_checkout_exists(frozen):
    if not MODULE.NATIVE_ROOT.exists():
        pytest.skip("sibling JC checkout is not present")
    MODULE.check_native_bindings(frozen[1])


def test_lean_backstop_names_pivot_independence():
    text = (ROOT / "lean" / "GrandPortage" /
            "AffineCoordinate.lean").read_text(encoding="utf-8")
    assert "PivotIndependent" in text
    assert "affineTranslatedModel_eq_of_pivotIndependent" in text
    assert "affineTranslation_preserves_pivotIndependent" in text
