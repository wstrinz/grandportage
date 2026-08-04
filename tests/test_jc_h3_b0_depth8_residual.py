import copy
import hashlib
import importlib.util
import json
import sys
import tempfile
from pathlib import Path

import pytest


pytestmark = pytest.mark.replay


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = (ROOT / "experiments" / "jc_h3_b0_free_plane" /
          "depth8_residual_adapter.py")


def _load():
    spec = importlib.util.spec_from_file_location(
        "jc_b0_depth8_residual_test", SCRIPT)
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


def test_explicit_residual_pullback_and_finite_unit_replay(checked, frozen):
    assert checked == {
        "r8_terms": [552, 704],
        "psi8_terms": 709,
        "psi8_class": "NONZERO_NONUNIT_FIBER_AFFINE",
        "omega8_terms": 4123,
        "exceptional_content": "c2_3^26*c3_5^2",
        "witness": {
            "dimension": 14,
            "slice_codimension": 7,
            "omega_image_degree": 13,
            "gcd_degree": 0,
            "omega_unit": True,
        },
    }
    assert hashlib.sha256(frozen[0]).hexdigest() == (
        MODULE.EXPECTED_FIXTURE_SHA256)


def test_report_excludes_only_the_frozen_witness(checked, frozen):
    report = MODULE.report_from_checked_fixture(frozen[1], checked)
    assert report["verdict"] == (
        "VERIFIED_NECESSARY_PSI8__FROZEN_WITNESS_EXCLUDED")
    assert report["graph_effect"] == "NONE"
    assert report["evidence_envelope"]["graph_effect"] == "NONE"
    assert "dimension 14" in report["checked_results"]["frozen_witness"]
    refused = " ".join(report["does_not_license"])
    assert "component" in refused and "off-slice" in refused
    assert "depth nine" in refused and "H3" in refused
    assert "source membership" in refused and "graph" in refused


@pytest.mark.parametrize("mutator,check", [
    (lambda p: p["projection"].update({"graph_effect": "LOCAL_EMPTY"}), "M1"),
    (lambda p: p["psi8_certificate"].update({
        "field": "K = QQ[t]/(15*t**3 - 1)"}), "N6"),
    (lambda p: p["pullback_certificate"]["ring"][
        "ring_variable_order"].reverse(), "N7"),
    (lambda p: p["psi8_certificate"]["source_digests"].update({
        "f2_h3_esystem_seam.py": "0" * 64}), "N4"),
    (lambda p: p["psi8_certificate"].update({
        "r8_2": "NOT BUILT -- unexplained"}), "A4"),
    (lambda p: p["pullback_certificate"]["witness"]["slice"].update({
        "c2_1": "1"}), "N8"),
])
def test_scope_pin_order_digest_middle_and_slice_mutations_refuse(
        frozen, mutator, check):
    changed = copy.deepcopy(frozen[1])
    mutator(changed)
    with pytest.raises(MODULE.Depth8ResidualEvidenceError, match=check):
        MODULE.validate_fixture_value(changed)


def test_changed_syzygy_body_refuses(frozen):
    changed = copy.deepcopy(frozen[1])
    changed["psi8_certificate"]["r8_1"]["sparse"]["terms"][0][1] = "-449"
    with pytest.raises(MODULE.Depth8ResidualEvidenceError, match="A1"):
        MODULE.validate_fixture_value(changed)


def test_exceptional_factor_cancellation_mutation_refuses(frozen):
    changed = copy.deepcopy(frozen[1])
    changed["pullback_certificate"]["exceptional_factors"][
        "policy"] = "CANCELLED"
    with pytest.raises(MODULE.Depth8ResidualEvidenceError, match="D8"):
        MODULE.validate_fixture_value(changed)


def test_changed_finite_algebra_modulus_refuses(frozen):
    changed = copy.deepcopy(frozen[1])
    changed["pullback_certificate"]["witness"]["r_final"][0] = "1"
    with pytest.raises(MODULE.Depth8ResidualEvidenceError, match="W3|W5"):
        MODULE.validate_fixture_value(changed)


def test_changed_fixture_refuses_by_digest(frozen):
    changed = copy.deepcopy(frozen[1])
    changed["authority_boundary"] = "widened"
    with tempfile.TemporaryDirectory(
            prefix="gp-depth8-residual-", dir=ROOT) as temporary:
        path = Path(temporary) / "changed.json"
        path.write_bytes(MODULE.encoded(changed))
        with pytest.raises(MODULE.Depth8ResidualEvidenceError, match="F4"):
            MODULE.verify_fixture(path)


def test_native_bindings_are_current_when_sibling_checkout_exists(frozen):
    if not MODULE.NATIVE_ROOT.exists():
        pytest.skip("sibling JC checkout is not present")
    MODULE.check_native_bindings(frozen[1])


def test_lean_contract_keeps_finite_witness_exclusion_pointwise():
    text = (ROOT / "lean" / "GrandPortage" /
            "AffineFiberBlock.lean").read_text(encoding="utf-8")
    assert "determinedAffineFiber_empty_of_scalar_nonzero" in text
    assert "pointwise" in text
    assert "component-wide" in text
