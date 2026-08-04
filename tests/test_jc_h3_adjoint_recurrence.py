import copy
import importlib.util
import json
from pathlib import Path
from types import SimpleNamespace

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = (ROOT / "experiments" / "jc_h3_adjoint_recurrence" / "adapter.py")


def _load():
    spec = importlib.util.spec_from_file_location("jc_h3_recurrence_test", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _fixture(module):
    return json.loads(module.DEFAULT_FIXTURE.read_text(encoding="utf-8"))


def test_corrected_unilateral_annihilator_is_lean_backed_and_scoped():
    module = _load()
    report = module.verify_fixture()

    assert report["verdict"] == (
        "VERIFIED_CONDITIONAL_UNILATERAL_ANNIHILATOR_IDEAL_S8")
    assert report["domain"] == {"kind": "UNILATERAL", "start": 6}
    assert report["operator_coefficient_domain"] == "QQ"
    assert "faithful QQ scaling" in report["sequence_value_module"]
    assert "width >= 8" in report["operator_representation"]
    assert report["checked_instance_premises"]["zero_from"] == 14
    assert report["checked_instance_premises"]["endpoint_nonzero"] is True
    assert report["checked_instance_premises"]["S7_annihilates"] is False
    assert report["claims"]["constant_coefficient_annihilator_ideal"] == {
        "value": "(S^8)",
        "status": "VERIFIED_LEAN_BACKED_FROM_CHECKED_PREMISES",
        "lean_theorem": "annihilatesFrom_iff_coefficients_below_gap_zero",
    }
    assert report["claims"]["reversible_backward_recurrence"]["status"] == (
        "REFUTED")
    assert "H8 for depths >=8" in report["evidence_envelope"][
        "outstanding_premises"]
    assert report["graph_effect"] == report["evidence_envelope"][
        "graph_effect"] == "NONE"


@pytest.mark.parametrize("mutate", [
    lambda value: value["projection"]["domain"].update({"kind": "BILATERAL"}),
    lambda value: value["projection"]["domain"].update({"start": 0}),
    lambda value: value["projection"].update(
        {"operator_coefficient_domain": "UNDECLARED"}),
    lambda value: value["projection"]["claims"][
        "constant_coefficient_annihilator_ideal"].update({"value": "(0)"}),
    lambda value: value["projection"]["claims"][
        "reversible_backward_recurrence"].update({"status": "VERIFIED"}),
    lambda value: value["projection"]["claims"][
        "polynomial_coefficient_annihilator"].update(
            {"minimality_scope": "ALL_OPERATORS"}),
    lambda value: value["projection"].update({"graph_effect": "CLAIM_AUTHORITY"}),
    lambda value: value["projection"]["premises"][
        "native_assumptions_not_discharged"].remove("H8 for depths >=8"),
])
def test_scope_widening_mutations_are_refused(mutate):
    module = _load()
    value = _fixture(module)
    mutate(value)

    with pytest.raises(module.RecurrenceEvidenceError, match="M1"):
        module.validate_fixture_value(value)


def test_original_false_annihilator_statement_is_refused():
    module = _load()
    value = _fixture(module)
    value["native_certificate"]["annihilator"]["constant_coefficient"] = (
        "no nonzero constant-coefficient annihilator exists")

    with pytest.raises(module.RecurrenceEvidenceError, match="N7"):
        module.validate_fixture_value(value)


def test_changed_jump_schedule_is_refused():
    module = _load()
    value = _fixture(module)
    value["native_certificate"]["operator_jumps"]["nonzero_at"] = [7, 8, 11, 13]

    with pytest.raises(module.RecurrenceEvidenceError, match="J2"):
        module.validate_fixture_value(value)


def test_zeroing_depth13_endpoint_refuses_minimal_shift_claim():
    module = _load()
    value = _fixture(module)
    zero = copy.deepcopy(
        value["native_certificate"]["regimes"][0]["matrix"][0]["value"])
    assert zero["terms"] == 0
    for entry in value["native_certificate"]["regimes"][3]["matrix"]:
        entry["value"] = copy.deepcopy(zero)

    with pytest.raises(module.RecurrenceEvidenceError, match="J4|A2"):
        module.validate_fixture_value(value)


def test_default_replay_does_not_execute_native_checker(monkeypatch):
    module = _load()
    monkeypatch.setattr(module.subprocess, "run", lambda *_a, **_k:
                        pytest.fail("default replay spawned native checker"))

    assert module.verify_fixture()["graph_effect"] == "NONE"


def test_native_replay_requires_current_corrected_summary(monkeypatch):
    module = _load()
    output = ("44/44 checks passed in 0.05 s; adjoint-recurrence certificate " +
              module.NATIVE_BINDINGS[
                  "f2_h3_adjoint_recurrence_certificate.json"])
    monkeypatch.setattr(module.subprocess, "run", lambda *_a, **_k:
                        SimpleNamespace(returncode=0, stderr="", stdout=output))

    assert module.native_replay()["verdict"] == "VERIFIED_NATIVE_44_OF_44"


def test_frozen_digest_and_native_bindings_are_checked(tmp_path):
    module = _load()
    value = _fixture(module)
    path = tmp_path / "recurrence.json"
    path.write_text(json.dumps(value, sort_keys=True), encoding="utf-8")
    with pytest.raises(module.RecurrenceEvidenceError, match="F4"):
        module.verify_fixture(path)

    if not module.NATIVE_ROOT.exists():
        pytest.skip("sibling JC checkout is not present")
    fixture, _premises = module.validate_fixture_value(value)
    module.check_native_bindings(fixture)


def test_report_write_is_atomic_and_refuses_overwrite(tmp_path):
    module = _load()
    path = tmp_path / "report.json"
    report = module.verify_fixture()

    module._atomic_write(path, report)
    assert json.loads(path.read_text(encoding="utf-8")) == report
    assert not list(tmp_path.glob("*.tmp"))
    with pytest.raises(module.RecurrenceEvidenceError, match="output exists"):
        module._atomic_write(path, report)


def test_lean_shadow_exposes_the_generic_cutoff_characterization():
    source = (ROOT / "lean" / "GrandPortage" /
              "ParametricRecurrence.lean").read_text(encoding="utf-8")
    assert "theorem annihilatesFrom_iff_coefficients_below_gap_zero" in source
    assert "theorem jcAdjoint_cutoff_gap : 14 - 6 = 8" in source
    assert "import Mathlib" not in source
