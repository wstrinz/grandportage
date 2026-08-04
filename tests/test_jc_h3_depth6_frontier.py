import importlib.util
import json
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = (ROOT / "experiments" / "jc_h3_source_depth6" /
          "frontier_adapter.py")
H8_SCRIPT = ROOT / "experiments" / "jc_h3_frontier" / "adapter.py"


def _load(path=SCRIPT, name="jc_h3_depth6_frontier_test"):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _by_id(report):
    return {item["id"]: item for item in report["items"]}


def test_all_five_depth6_statuses_remain_open_and_domain_specific():
    report = _load().verify_ledger()
    items = _by_id(report)

    assert report["counts"] == {
        "items": 5, "open": 5, "changed": 0, "premise_discharges": 0}
    assert items["JC.H3.D6.R5.CUBIC_FACE"]["effective_status"] == (
        "CHECKED_PREMISE_BOUND")
    assert items["JC.H3.D6.R7.75_125_IDENTIFICATION"][
        "effective_status"] == "INFERRED_UNBOUND_75_125_IDENTIFICATION"
    assert all(item["frontier_state"] == "OPEN" for item in items.values())


def test_r6_premises_are_stable_ids_and_q_relocation_stays_separate():
    items = _by_id(_load().verify_ledger())
    expected = {
        "JC.H3.SOURCE.ACTUAL_PAIR",
        "JC.H3.SOURCE.POLYNOMIALITY",
        "JC.H3.SOURCE.GAP5",
    }

    assert {premise["id"] for premise in items[
        "JC.H3.D6.R6.NONMONOMIAL_FRAME"]["premises"]} == expected
    assert {premise["id"] for premise in items[
        "JC.H3.D6.R6.Q_SIDE_RELOCATION"]["premises"]} == expected
    assert items["JC.H3.D6.R6.Q_SIDE_RELOCATION"][
        "blocked_downstream"] == ["Q-side positive-j relocation"]


def test_parent_source_seam_has_distinct_scope_and_no_promotion():
    report = _load().verify_ledger()
    item = _by_id(report)[
        "JC.H3.SOURCE.TARGET_PAIR_TO_NORMALIZED_LAURENT_ROOT"]

    assert item["scope"]["id"] == "JC.H3.SOURCE.TARGET_PAIR.SEAM"
    assert item["effective_status"] == "UNMATERIALIZED_OPEN"
    assert "H3 promotion" in item["blocked_downstream"]
    assert report["source_authority_ceiling"] == (
        "CONDITIONAL_NORMALIZED_ROOT_TO_DEPTH6_BOUNDARY_ONLY")
    assert report["graph_effect"] == "NONE"


def test_ledger_mutation_refuses_before_compilation(tmp_path):
    module = _load()
    value = json.loads(module.DEFAULT_LEDGER.read_text(encoding="utf-8"))
    value["open_frontier"][0]["status"] = "CLOSED"
    path = tmp_path / "mutated.json"
    path.write_text(json.dumps(value), encoding="utf-8")

    with pytest.raises(module.Depth6FrontierError, match="digest changed"):
        module.verify_ledger(path)


def test_checked_in_depth6_frontier_receipt_exactly_regenerates():
    module = _load()
    expected = json.loads((ROOT / "review" /
                           "jc-h3-depth6-frontier-v1.json").read_text(
                               encoding="utf-8"))

    assert expected == module.review_receipt(module.verify_ledger())


def test_depth6_and_h8_are_independent_consumers_of_one_schema():
    depth6 = _load().verify_ledger()
    h8_module = _load(H8_SCRIPT, "jc_h3_h8_frontier_second_consumer")
    h8 = h8_module.verify_fixture()

    assert depth6["schema"] == h8["schema"] == "frontier/v1"
    assert depth6["consumer"] != h8["consumer"]
    assert depth6["changes"] == []
    assert h8["changes"]
