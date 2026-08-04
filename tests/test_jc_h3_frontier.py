import copy
import importlib.util
import json
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "experiments" / "jc_h3_frontier" / "adapter.py"


def _load():
    spec = importlib.util.spec_from_file_location("jc_h3_frontier_test", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _by_id(report):
    return {item["id"]: item for item in report["items"]}


def test_h8_discharge_updates_downstream_without_rewriting_history():
    report = _load().verify_fixture()
    items = _by_id(report)

    assert items["JC.H3.H8"]["historical_status"] == "OPEN_PREMISE"
    assert items["JC.H3.H8"]["effective_status"] == "DISCHARGED"
    assert items["JC.H3.OPERATOR_SCHEDULE.D8-15"][
        "effective_status"] == "VERIFIED"
    assert items["JC.H3.D9.PAIRING.DEG34"][
        "effective_status"] == "VERIFIED"
    assert report["history"]["immutable"] is True


def test_h8_scope_does_not_discharge_residual_source_or_h3_work():
    report = _load().verify_fixture()
    refusal = set(report["discharges"][0]["does_not_discharge"])

    assert {"additive residual bodies", "actual-source membership",
            "source sufficiency", "H3"} <= refusal
    assert "JC.H3.B0.SOURCE.EXCLUSION" in report["open_items"]


def test_c79_family_is_closed_but_pin_ablation_and_b0_are_open():
    items = _by_id(_load().verify_fixture())

    assert items["JC.H3.C79.SOURCE.FACE81.UNIT"][
        "effective_status"] == "CLOSED"
    assert items["JC.H3.C79.SOURCE.FACE81.PIN_ABLATION"][
        "effective_status"] == "OPEN"
    assert items["JC.H3.B0.SOURCE.EXCLUSION"][
        "effective_status"] == "OPEN"


def test_pin_ablation_names_ranked_scope_defect_and_cost():
    item = _by_id(_load().verify_fixture())[
        "JC.H3.C79.SOURCE.FACE81.PIN_ABLATION"]

    assert "c2_1" in item["scope"]["description"]
    assert "first nonzero defect term" in item[
        "smallest_next_artifact"]["description"]
    assert item["estimated_cost"]["load_bearing_replay_seconds"] == 140
    assert len(item["potential_impact"]) == 2


def test_fixture_mutation_is_refused_before_projection(tmp_path):
    module = _load()
    value = json.loads(module.DEFAULT_FIXTURE.read_text(encoding="utf-8"))
    value["items"][0]["scope"]["description"] = "silently widened"
    path = tmp_path / "mutated.json"
    path.write_text(json.dumps(value), encoding="utf-8")

    with pytest.raises(module.JCFrontierError, match="digest changed"):
        module.verify_fixture(path)


def test_projection_is_stable_and_native_binding_is_opt_in():
    module = _load()
    first = module.verify_fixture()
    second = module.verify_fixture()

    assert first == second
    assert first["native_bindings_checked"] == []
    assert first["counts"] == {
        "items": 6, "open": 2, "changed": 3, "premise_discharges": 1}


def test_native_receipt_bindings_match_without_running_release_suite():
    report = _load().verify_fixture(check_native_bindings=True)

    assert len(report["native_bindings_checked"]) == 5
    assert any(path.endswith("depths10_15_transfer_receipt.json")
               for path in report["native_bindings_checked"])
    assert report["graph_effect"] == "NONE"


def test_checked_in_review_receipt_is_exactly_regenerated():
    module = _load()
    expected = json.loads((ROOT / "review" /
                           "jc-h3-h8-c79-frontier-v1.json").read_text(
                               encoding="utf-8"))

    assert expected == module.review_receipt(module.verify_fixture())
