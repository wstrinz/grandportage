import importlib.util
import json
from pathlib import Path
from types import SimpleNamespace

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "experiments" / "jc_h3_depth8_fiber" / "adapter.py"


def _load():
    spec = importlib.util.spec_from_file_location("jc_h3_depth8_fiber_test", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _fixture(module):
    return json.loads(module.DEFAULT_FIXTURE.read_text(encoding="utf-8"))


def test_entire_named_first_order_fiber_is_scoped_and_lean_backed():
    module = _load()
    report = module.verify_fixture()

    assert report["verdict"] == (
        "VERIFIED_CONDITIONAL_FIRST_ORDER_EMPTY_EXACT_BASE_FIBER")
    assert report["semantic_layer"] == "FIRST_ORDER_DEPTH8_COMPATIBILITY"
    assert report["point_universe"] == "L = K[y]/(y^2-d)"
    assert report["base_scope"]["other_base_points"] == "OPEN"
    assert report["fiber_scope"] == {
        "coordinate": "c8_5",
        "quantifier": "ALL_VALUES_IN_L",
        "dependent_coordinate": "c7_4",
        "dependent_status": "SOLVED_AFFINELY_FROM_ZERO_BLOCK",
        "compatible_first_order_fiber": "EMPTY",
    }
    assert report["lean_backing"]["first_order"] == (
        "fiberEmpty_of_base_obstruction")
    assert report["graph_effect"] == report["evidence_envelope"][
        "graph_effect"] == "NONE"


@pytest.mark.parametrize("mutate", [
    lambda value: value["projection"].update(
        {"semantic_layer": "NONLINEAR_FORMAL_LIFT"}),
    lambda value: value["projection"]["base_scope"].update(
        {"other_base_points": "EMPTY"}),
    lambda value: value["projection"]["base_scope"].update(
        {"selected": "entire 12-dimensional survivor locus"}),
    lambda value: value["projection"]["fiber_scope"].update(
        {"dependent_status": "FREE_RESCUE_DIRECTION"}),
    lambda value: value["projection"].update({"point_universe": "K"}),
    lambda value: value["projection"].update({"graph_effect": "LOCAL_EMPTY"}),
    lambda value: value["projection"]["outstanding_premises"].remove("H8"),
    lambda value: value["projection"]["does_not_license"].remove(
        "component emptiness"),
])
def test_scope_widening_mutations_are_refused(mutate):
    module = _load()
    value = _fixture(module)
    mutate(value)
    with pytest.raises(module.FiberEvidenceError, match="M1"):
        module.validate_fixture_value(value)


def test_zeroed_omega_comb_is_refused():
    module = _load()
    value = _fixture(module)
    value["native_certificate"]["witness_values"]["omega_comb"] = [
        ["0", "0", "0"], ["0", "0", "0"]]
    with pytest.raises(module.FiberEvidenceError, match="N8"):
        module.validate_fixture_value(value)


def test_authorizing_depth9_pair_is_refused():
    module = _load()
    value = _fixture(module)
    value["native_certificate"]["verdict"][
        "depth9_additive_pair_authorized"] = True
    with pytest.raises(module.FiberEvidenceError, match="N7"):
        module.validate_fixture_value(value)


def test_default_replay_does_not_execute_native_checker(monkeypatch):
    module = _load()
    monkeypatch.setattr(module.subprocess, "run", lambda *_a, **_k:
                        pytest.fail("default replay spawned native checker"))
    assert module.verify_fixture()["graph_effect"] == "NONE"


def test_native_replay_requires_current_summary(monkeypatch):
    module = _load()
    output = ("STRAGGLER/ZERO-BLOCK COMPOSITION: Omega_comb != 0\n" +
              "CHECKS: 24/24 pass")
    monkeypatch.setattr(module.subprocess, "run", lambda *_a, **_k:
                        SimpleNamespace(returncode=0, stderr="", stdout=output))
    assert module.native_replay()["verdict"] == "VERIFIED_NATIVE_24_OF_24"


def test_frozen_digest_and_native_bindings_are_checked(tmp_path):
    module = _load()
    value = _fixture(module)
    path = tmp_path / "fiber.json"
    path.write_text(json.dumps(value, sort_keys=True), encoding="utf-8")
    with pytest.raises(module.FiberEvidenceError, match="F4"):
        module.verify_fixture(path)

    if not module.NATIVE_ROOT.exists():
        pytest.skip("sibling JC checkout is not present")
    fixture, _checked = module.validate_fixture_value(value)
    module.check_native_bindings(fixture)


def test_lean_shadow_keeps_first_order_and_nonlinear_bridge_separate():
    source = (ROOT / "lean" / "GrandPortage" /
              "FirstOrderFiber.lean").read_text(encoding="utf-8")
    assert "theorem fiberEmpty_of_base_obstruction" in source
    assert "theorem nonlinearFiberEmpty_of_sound_linearization" in source
    assert "import Mathlib" not in source
