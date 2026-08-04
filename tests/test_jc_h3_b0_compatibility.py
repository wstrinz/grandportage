import copy
import hashlib
import importlib.util
import json
import sys
from pathlib import Path

import pytest


pytestmark = pytest.mark.replay


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "experiments" / "jc_h3_b0_compatibility" / "adapter.py"


def _load():
    spec = importlib.util.spec_from_file_location("jc_b0_compat_test", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


MODULE = _load()
FIXTURE_RAW = MODULE.DEFAULT_FIXTURE.read_bytes()
FIXTURE = json.loads(FIXTURE_RAW.decode("utf-8"))


@pytest.fixture(scope="module")
def checked():
    return MODULE.validate_fixture_value(FIXTURE)


def test_exact_affine_and_quotient_replay_classifies_phi_narrowly(checked):
    assert checked == {
        "phi_terms": 3137,
        "chart_determinant": "VERIFIED_DET5",
        "clearing_exponent": 2,
        "power_one_refuted": True,
        "resultant_degree": 26,
        "nonzero_observation_dimension": 2,
        "zero_observation_dimension": 14,
        "zero_witness_guards": [
            "c2_3", "p", "det5", "OB-pivot", "S11"],
        "module_rendezvous": "BOUND_FROZEN_SAME_PHI",
    }
    assert hashlib.sha256(FIXTURE_RAW).hexdigest() == (
        MODULE.EXPECTED_FIXTURE_SHA256)


def test_report_keeps_ring_class_separate_from_graph_and_geometry(checked):
    report = MODULE.report_from_checked_fixture(FIXTURE, checked)
    assert report["verdict"] == "VERIFIED_NEITHER_ZERO_NOR_UNIT"
    assert report["claims"] == {
        "nonzero": "VERIFIED_BY_NONZERO_QUADRATIC_QUOTIENT_IMAGE",
        "unit": "REFUTED_BY_ZERO_IN_NONTRIVIAL_DEGREE_14_QUOTIENT",
        "nonzerodivisor": "OPEN_NOT_CLAIMED",
    }
    assert report["graph_effect"] == "NONE"
    assert report["module_rendezvous"]["status"] == "BOUND_FROZEN_SAME_PHI"
    assert report["evidence_envelope"]["graph_effect"] == "NONE"
    assert len(report["evidence_envelope"][
        "consumed_frozen_semantics"]) == 3
    refused = " ".join(report["refusals"])
    assert "K-rationality" in refused and "nonzerodivisor" in refused
    assert "H3" in refused and "source sufficiency" in refused


@pytest.mark.parametrize("mutator", [
    lambda p: p["model"]["guards"].remove("det5"),
    lambda p: p["definition"].__setitem__("clearing_exponent", 1),
    lambda p: p["definition"].__setitem__(
        "source_class", "Lambda = VD - (2/3)*c2_3*t*E321"),
    lambda p: p["claims"].__setitem__("nonzero", "REFUTED"),
    lambda p: p["claims"].__setitem__("unit", "VERIFIED"),
    lambda p: p["claims"].__setitem__("nonzerodivisor", "VERIFIED"),
    lambda p: p["model"].__setitem__("point_universe", "K_RATIONAL"),
    lambda p: p.__setitem__("graph_effect", "NONEMPTY"),
])
def test_scope_and_direction_mutations_refuse_before_expensive_replay(mutator):
    changed = copy.deepcopy(FIXTURE)
    mutator(changed["projection"])
    with pytest.raises(MODULE.CompatibilityEvidenceError, match="M1"):
        MODULE.validate_fixture_value(changed)


def test_changed_native_binding_refuses_before_replay():
    changed = copy.deepcopy(FIXTURE)
    changed["source_bindings"]["f2_h3_b0_uniform_lambda.json"] = "0" * 64
    with pytest.raises(MODULE.CompatibilityEvidenceError, match="F3"):
        MODULE.validate_fixture_value(changed)


def test_changed_witness_polynomial_refuses_by_frozen_artifact_digest(tmp_path):
    changed = copy.deepcopy(FIXTURE)
    changed["slice"]["final_modulus"][0][0] = "1"
    path = tmp_path / "changed.json"
    path.write_bytes(MODULE.encoded(changed))
    with pytest.raises(MODULE.CompatibilityEvidenceError, match="F4"):
        MODULE.verify_fixture(path)


def test_native_bindings_are_current_when_sibling_checkout_exists():
    if not MODULE.NATIVE_ROOT.exists():
        pytest.skip("sibling JC checkout is not present")
    MODULE.check_native_bindings(FIXTURE)


def test_lean_theorems_state_only_nonzero_and_nonunit_authority():
    text = (ROOT / "lean" / "GrandPortage" /
            "RingElementClass.lean").read_text(encoding="utf-8")
    assert "nonzero_of_observed_nonzero" in text
    assert "notUnit_of_observed_zero" in text
    assert "neitherZeroNorUnit_of_observations" in text
    assert "nonzerodivisor" in text
