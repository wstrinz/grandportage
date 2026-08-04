import copy
import json

import pytest

from grandportage import cli
from grandportage import frontier as F


def _item(identifier, scope="scope.exact", premise=None,
          status="OPEN_PREMISE", target="DISCHARGED", exports=()):
    return {
        "id": identifier,
        "proposition": "a bounded proposition",
        "status": status,
        "status_when_premises_discharged": target,
        "scope": {"id": scope, "description": "one exact scope"},
        "exports_to_scopes": list(exports),
        "premises": ([] if premise is None else [
            {"id": premise, "status": "OPEN"}]),
        "blocked_downstream": [],
        "superseding_evidence": ["receipt"] if exports else [],
        "smallest_next_artifact": None,
        "estimated_cost": None,
        "potential_impact": [],
    }


def _discharge(premise="P", scope="scope.exact"):
    return {
        "id": "D", "premise_id": premise, "status": "DISCHARGED",
        "applies_to_scopes": [scope], "evidence": ["receipt"],
        "does_not_discharge": ["anything outside the exact scope"],
    }


def test_scoped_discharge_changes_status_without_mutating_history():
    items = [_item("A", premise="P")]
    before = copy.deepcopy(items)

    result = F.build(items, [_discharge()])

    assert items == before
    assert result["authority"] == "DERIVED_READ_MODEL_ONLY"
    assert result["graph_effect"] == "NONE"
    assert result["items"][0]["historical_status"] == "OPEN_PREMISE"
    assert result["items"][0]["effective_status"] == "DISCHARGED"
    assert result["history"]["immutable"] is True


def test_discharge_does_not_infer_scope_containment():
    result = F.build(
        [_item("A", scope="scope.narrow", premise="P")],
        [_discharge(scope="scope.wide")],
    )

    assert result["items"][0]["effective_status"] == "OPEN_PREMISE"
    assert result["items"][0]["remaining_open_premises"] == ["P"]


def test_closed_item_propagates_only_to_explicit_export_scope():
    premise = _item("A", premise="P", exports=("scope.consumer",))
    consumer = _item(
        "B", scope="scope.consumer", premise="A",
        status="VERIFIED_CONDITIONAL", target="VERIFIED")
    outside = _item(
        "C", scope="scope.other", premise="A",
        status="VERIFIED_CONDITIONAL", target="VERIFIED")

    result = F.build([premise, consumer, outside], [_discharge()])
    by_id = {item["id"]: item for item in result["items"]}

    assert by_id["A"]["effective_status"] == "DISCHARGED"
    assert by_id["B"]["effective_status"] == "VERIFIED"
    assert by_id["C"]["effective_status"] == "VERIFIED_CONDITIONAL"


def test_projection_is_deterministic_under_input_order():
    a = _item("A", premise="P")
    b = _item("B", status="OPEN", target=None)
    b.pop("status_when_premises_discharged")

    first = F.build([a, b], [_discharge()], [{"path": "z"}, {"path": "a"}])
    second = F.build([b, a], [_discharge()], [{"path": "a"}, {"path": "z"}])

    assert F.canonical_json(first) == F.canonical_json(second)


def test_duplicate_item_and_discharge_targets_refuse():
    with pytest.raises(F.FrontierError, match="item ids"):
        F.build([_item("A"), _item("A")])
    with pytest.raises(F.FrontierError, match="multiple discharges"):
        F.build([_item("A", premise="P")], [_discharge(), {
            **_discharge(), "id": "D2"}])


def test_unstable_id_and_missing_research_fields_refuse():
    bad = _item("not an id")
    with pytest.raises(F.FrontierError, match="stable semantic id"):
        F.build([bad])
    incomplete = _item("A")
    del incomplete["potential_impact"]
    with pytest.raises(F.FrontierError, match="missing"):
        F.build([incomplete])


def test_cli_compiles_frontier_input(capsys, tmp_path):
    path = tmp_path / "frontier.json"
    path.write_text(json.dumps({
        "schema": "frontier-input/v1",
        "items": [_item("A", premise="P")],
        "discharges": [_discharge()],
    }), encoding="utf-8")

    assert cli.main(["frontier", str(path), "--compact"]) == 0
    output = json.loads(capsys.readouterr().out)
    assert output["schema"] == "frontier/v1"
    assert output["items"][0]["effective_status"] == "DISCHARGED"


def test_explicit_frontier_state_preserves_domain_status_vocabulary():
    item = _item("A", status="CHECKED_PREMISE_BOUND", target=None)
    item.pop("status_when_premises_discharged")
    item["frontier_state"] = "OPEN"

    result = F.build([item])

    assert result["items"][0]["historical_status"] == (
        "CHECKED_PREMISE_BOUND")
    assert result["open_items"] == ["A"]
