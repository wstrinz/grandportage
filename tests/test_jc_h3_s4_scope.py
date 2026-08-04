import copy
import importlib.util
import json
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "experiments" / "jc_h3_s4_scope" / "adapter.py"


def _load():
    spec = importlib.util.spec_from_file_location("jc_h3_s4_scope_test", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _fixture(module):
    return json.loads(module.DEFAULT_FIXTURE.read_text(encoding="utf-8"))


def test_frozen_scope_verifies_one_piece_and_keeps_other_open():
    module = _load()
    report = module.verify_fixture()

    assert report["verdict"] == "VERIFIED_ONE_PIECE_OPEN_OTHER_PIECE"
    assert report["graph_effect"] == "NONE"
    assert report["closed_piece"]["claim"] == "NONEMPTY"
    assert report["closed_piece"]["status"] == "VERIFIED_EXACT_K_POINT"
    assert report["open_piece"]["claim"] is None
    assert report["open_piece"]["status"] == "OPEN"
    assert report["cover"]["union_claim"] is None
    assert report["evidence_envelope"]["graph_effect"] == "NONE"
    assert "t" not in report["evidence_envelope"]["context"]["ring_vars"]
    assert "K-point existence or emptiness on C=0 and C2!=0" in (
        report["evidence_envelope"]["outstanding_premises"])


@pytest.mark.parametrize("mutate,match", [
    (lambda value: value["projection"]["open_piece"].update(
        {"status": "EMPTY"}), "M5"),
    (lambda value: value["projection"]["open_piece"].update(
        {"claim": "EMPTY"}), "M5"),
    (lambda value: value["projection"]["open_piece"]["search_evidence"].update(
        {"authority": "REFUTATION"}), "M6"),
    (lambda value: value["projection"]["cover"].update(
        {"union_claim": "ALL_K_POINTS_HAVE_C2_ZERO"}), "M7"),
    (lambda value: value["projection"]["cover"].update(
        {"branches": ["S4_C_ZERO__C2_ZERO"]}), "M7"),
    (lambda value: value["projection"].update(
        {"point_universe": "ALGEBRAIC_CLOSURE"}), "M1"),
    (lambda value: value["projection"].update(
        {"graph_effect": "PROMOTE_PARENT_EMPTY"}), "M2"),
    (lambda value: value["projection"]["guards"].update(
        {"c3_5_nonzero": False}), "M8"),
    (lambda value: value["projection"]["closed_piece"].update(
        {"relation": "EQUIVALENCE"}), "M4"),
    (lambda value: value["projection"]["parent"].update(
        {"status": "EMPTY"}), "M3"),
])
def test_authority_widening_mutations_are_refused(mutate, match):
    module = _load()
    value = _fixture(module)
    mutate(value)

    with pytest.raises(module.S4ScopeError, match=match):
        module.validate_fixture_value(value)


def test_sparse_body_mutation_is_refused():
    module = _load()
    value = _fixture(module)
    value["polynomials"]["C"]["terms"][0][1] = "2"

    with pytest.raises(module.S4ScopeError, match="P9"):
        module.validate_fixture_value(value)


def test_frozen_digest_is_a_checked_boundary(tmp_path):
    module = _load()
    value = _fixture(module)
    path = tmp_path / "scope.json"
    path.write_text(json.dumps(value, sort_keys=True), encoding="utf-8")

    with pytest.raises(module.S4ScopeError, match="F5"):
        module.verify_fixture(path)


def test_default_replay_never_executes_native_producer(monkeypatch):
    module = _load()
    monkeypatch.setattr(module.runpy, "run_path", lambda *_a, **_k:
                        pytest.fail("default replay executed native producer"))
    monkeypatch.setattr(module.subprocess, "run", lambda *_a, **_k:
                        pytest.fail("default replay spawned a subprocess"))

    assert module.verify_fixture()["verdict"] == (
        "VERIFIED_ONE_PIECE_OPEN_OTHER_PIECE")


def test_report_write_is_atomic_and_refuses_overwrite(tmp_path):
    module = _load()
    path = tmp_path / "report.json"
    report = module.verify_fixture()

    module.write_report(path, report)
    assert json.loads(path.read_text(encoding="utf-8")) == report
    assert not list(tmp_path.glob("*.tmp"))
    with pytest.raises(module.S4ScopeError, match="output exists"):
        module.write_report(path, report)


def test_checked_in_native_bindings_are_current():
    module = _load()
    fixture = module.validate_fixture_value(_fixture(module))
    module.check_native_bindings(fixture)
