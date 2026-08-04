import copy
import hashlib
import importlib.util
import json
import sys
import tempfile
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = (ROOT / "experiments" / "jc_h3_b0_free_plane" /
          "depth8_adapter.py")


def _load():
    spec = importlib.util.spec_from_file_location("jc_b0_depth8_block_test", SCRIPT)
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


def test_rank_two_block_and_symbolic_compatibility_replay(checked, frozen):
    assert checked == {
        "raw_coefficients": 9,
        "transported_shape": [3, 2],
        "rank": 2,
        "unit_minor": "-(25/8)*c2_3^5*c3_5*t",
        "left_syzygy": ["c2_3", "0", "2"],
        "symbolic_compatibility": "Psi8=c2_3*r8_1+2*r8_3",
        "residual_exported": False,
    }
    assert hashlib.sha256(frozen[0]).hexdigest() == (
        MODULE.EXPECTED_FIXTURE_SHA256)


def test_report_stops_at_necessary_block_with_no_graph_effect(checked, frozen):
    report = MODULE.report_from_checked_fixture(frozen[1], checked)
    assert report["verdict"] == "VERIFIED_RANK2_NECESSARY_AFFINE_BLOCK"
    assert report["graph_effect"] == "NONE"
    assert report["evidence_envelope"]["graph_effect"] == "NONE"
    assert report["checked_block"]["residual_status"] == "NOT_EXPORTED"
    assert "export r8=" in report["first_open_obligation"]
    refused = " ".join(report["does_not_license"])
    assert "equivalence" in refused and "sufficiency" in refused
    assert "H3" in refused and "source membership" in refused


def _change_raw(value):
    value["raw_columns"]["E[2,19]"]["c8_5"][0][1] = "-4"


def _change_block(value):
    value["transported_block"][0][1][0][1] = "-4"


@pytest.mark.parametrize("mutator,check", [
    (_change_raw, "A2"),
    (_change_block, "A4"),
    (lambda p: p["projection"].update({"graph_effect": "POINT_INCLUSION"}), "M1"),
    (lambda p: p["projection"]["transport"].update(
        {"D7": "d/dc7_4+(3/2)*c2_3*d/dc9_7"}), "M1"),
    (lambda p: p["projection"]["checked_block"].update(
        {"residual_status": "EXPORTED"}), "M1"),
    (lambda p: p["projection"].update(
        {"semantic_layer": "EQUIVALENT_ACTUAL_SOURCE_FIBER"}), "M1"),
    (lambda p: p["projection"].update({"first_open_obligation": "CLOSED"}), "M1"),
    (lambda p: p["native_certificate"]["localization_ledger"][
        "never_inverted"].remove("R"), "A11"),
])
def test_arithmetic_and_scope_mutations_refuse(frozen, mutator, check):
    changed = copy.deepcopy(frozen[1])
    mutator(changed)
    with pytest.raises(MODULE.Depth8BlockEvidenceError, match=check):
        MODULE.validate_fixture_value(changed)


def test_changed_previous_gp_prerequisite_refuses(frozen):
    changed = copy.deepcopy(frozen[1])
    changed["gp_prerequisite"]["sha256"] = "0" * 64
    with pytest.raises(MODULE.Depth8BlockEvidenceError, match="C1"):
        MODULE.validate_fixture_value(changed)


def test_changed_native_binding_refuses(frozen):
    changed = copy.deepcopy(frozen[1])
    changed["source_bindings"][
        "f2_h3_b0_depth8_free_plane_coefficients.json"] = "0" * 64
    with pytest.raises(MODULE.Depth8BlockEvidenceError, match="F3"):
        MODULE.validate_fixture_value(changed)


def test_changed_fixture_refuses_by_digest(frozen):
    changed = copy.deepcopy(frozen[1])
    changed["authority_boundary"] = "widened"
    with tempfile.TemporaryDirectory(prefix="gp-depth8-block-", dir=ROOT) as temp:
        path = Path(temp) / "changed.json"
        path.write_bytes(MODULE.encoded(changed))
        with pytest.raises(MODULE.Depth8BlockEvidenceError, match="F4"):
            MODULE.verify_fixture(path)


def test_native_bindings_are_current_when_sibling_checkout_exists(frozen):
    if not MODULE.NATIVE_ROOT.exists():
        pytest.skip("sibling JC checkout is not present")
    MODULE.check_native_bindings(frozen[1])


def test_lean_contract_keeps_compatibility_distinct_from_solution():
    text = (ROOT / "lean" / "GrandPortage" /
            "AffineFiberBlock.lean").read_text(encoding="utf-8")
    assert "DeterminedAffineFiber" in text
    assert "determinedAffineFiber_nonempty_iff" in text
    assert "determinedAffineFiber_unique" in text
