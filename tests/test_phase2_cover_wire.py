"""Native production cover routing, dependencies and earned consequences."""
import copy
import importlib.util
import json
from pathlib import Path
import pytest
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("scoped_wire", ROOT / "tests/test_phase2_scoped_wire.py")
wire = importlib.util.module_from_spec(spec)
spec.loader.exec_module(wire)

def prepared():
    old, _, _ = wire.prepared()
    original = old["clauses"][0]
    rows = []
    for key, scope in ((1, [1]), (2, [2]), (3, [1, 2]), (4, [1])):
        row = copy.deepcopy(original)
        row["algebra"]["key"] = key
        row["scope"] = scope
        row["algebra"]["binding"]["scopeHash"] = wire.bridge.digest(scope)
        rows.append(row)
    receipts = []
    for key in (1, 2):
        receipt = copy.deepcopy(old["receipts"][0])
        receipt.update(name="root-" + str(key), claim=key,
                       binding=copy.deepcopy(rows[key-1]["algebra"]["binding"]))
        receipts.append(receipt)
    rules = [{"name": "cover-1", "destination": 3, "branches": [1, 2]}]
    events = []
    for row, ident, evidence in (
        (rows[0], 10, {"kind": "receipt", "data": "root-1"}),
        (rows[1], 20, {"kind": "receipt", "data": "root-2"}),
        (rows[2], 30, {"kind": "derived", "premises": [10, 20], "sideReceipt": "cover-1"}),
        (rows[3], 40, {"kind": "narrow", "premise": 30})):
        binding = copy.deepcopy(row["algebra"]["binding"])
        events.extend([
            {"kind": "current", "value": {"claim": row["algebra"]["key"], "version": 1, "binding": binding}},
            {"kind": "warrant", "value": {"id": ident, "claim": row["algebra"]["key"],
                "version": 1, "binding": copy.deepcopy(binding), "evidence": evidence}}])
    query = {"schema_version": 1, "why_not": [3, 4], "claimed": [1, 2],
        "links": [{"claim": 3, "obligations": [7, 8]}, {"claim": 4, "obligations": [7]}],
        "open_obligations": [7, 8]}
    return {"schema_version": 3, "clauses": rows, "receipts": receipts, "rules": rules}, {"schema_version": 1, "events": events}, query

def test_actual_roots_cover_narrow_and_rank_earned(tmp_path):
    out = wire.execute(tmp_path, *prepared())
    assert out["state"]["held"] == [1, 2, 3, 4]
    assert out["release"] == {"allowed": True, "findings": []}
    assert out["state"]["supports"] == [10, 20, 30, 40]
    assert out["earned"] == [{"claim": 3, "open_obligations": [7, 8]},
                             {"claim": 4, "open_obligations": [7]}]

@pytest.mark.parametrize("cause", ["uncovered_context", "missing_receipt", "failed_branch", "retracted_branch", "missing_record"])
def test_cover_cannot_supply_its_own_branch_truth(tmp_path, cause):
    registry, events, query = prepared()
    if cause == "uncovered_context":
        registry["clauses"][2]["scope"].append(3)
    elif cause == "missing_receipt":
        registry["receipts"].pop()
    elif cause == "failed_branch":
        events["events"][3]["value"]["evidence"] = {"kind": "attempt", "status": "failed"}
    elif cause == "retracted_branch":
        events["events"].append({"kind": "retract", "target": 20})
    else:
        del events["events"][3]
    out = wire.execute(tmp_path, registry, events, query)
    assert 3 not in out["state"]["held"] and 4 not in out["state"]["held"]
    assert out["earned"] == []

@pytest.mark.parametrize("mutation", ["rule_name", "destination", "branch_order", "branch_count", "object", "input_binding"])
def test_rule_contract_and_actual_identity_are_checked(tmp_path, mutation):
    registry, events, query = prepared()
    rule = registry["rules"][0]
    if mutation == "rule_name":
        rule["name"] = "other"
    elif mutation == "destination":
        rule["destination"] = 4
    elif mutation == "branch_order":
        rule["branches"].reverse()
    elif mutation == "branch_count":
        rule["branches"].pop()
    elif mutation == "object":
        registry["clauses"][2]["object"] = "B"
    else:
        row = registry["clauses"][2]["algebra"]
        row["binding"]["inputHashes"] = ["different"]
        for event in events["events"][4:6]:
            event["value"]["binding"] = copy.deepcopy(row["binding"])
    out = wire.execute(tmp_path, registry, events, query)
    assert out["state"]["held"] == [1, 2] and out["earned"] == []

def test_independent_support_survives_but_exact_descendants_do_not(tmp_path):
    registry, events, query = prepared()
    extra = copy.deepcopy(events["events"][3])
    extra["value"]["id"] = 21
    events["events"].extend([extra, {"kind": "retract", "target": 20}])
    out = wire.execute(tmp_path, registry, events, query)
    assert out["state"]["held"] == [1, 2]
    assert out["state"]["supports"] == [10, 21]

def test_failed_retry_cannot_revoke_success(tmp_path):
    registry, events, query = prepared()
    baseline = wire.execute(tmp_path, registry, events, query)
    retry = copy.deepcopy(events["events"][3])
    retry["value"].update(id=21, evidence={"kind": "attempt", "status": "failed"})
    events["events"].append(retry)
    out = wire.execute(tmp_path, registry, events, query)
    assert out["state"]["held"] == baseline["state"]["held"]
    assert out["state"]["supports"] == baseline["state"]["supports"]

def test_set_order_and_duplicate_events_preserve_outputs(tmp_path):
    registry, events, query = prepared()
    baseline = wire.execute(tmp_path, registry, events, query)
    assert baseline["state"]["status"] == "OK"
    events["events"] = events["events"][::-1] * 2
    assert wire.execute(tmp_path, registry, events, query) == baseline

@pytest.mark.parametrize("defect", ["duplicate_rule", "extra_rule_field", "wrong_branch_type", "missing_rules"])
def test_rule_wire_malformed_is_explicit(tmp_path, defect):
    registry, events, query = prepared()
    if defect == "duplicate_rule":
        registry["rules"] *= 2
    elif defect == "extra_rule_field":
        registry["rules"][0]["success"] = True
    elif defect == "wrong_branch_type":
        registry["rules"][0]["branches"] = ["1", "2"]
    else:
        del registry["rules"]
    out = wire.execute(tmp_path, registry, events, query)
    assert out["status"] == "MALFORMED" and "state" not in out


def test_forged_premise_record_cannot_reuse_an_existing_id(tmp_path):
    registry, events, query = prepared()
    forged = copy.deepcopy(events["events"][3])
    forged["value"]["claim"] = 3
    events["events"].append(forged)
    out = wire.execute(tmp_path, registry, events, query)
    assert out["status"] == "MALFORMED" and "state" not in out

@pytest.mark.parametrize("one_root", [False, True])
def test_production_cover_cycles_do_not_bootstrap(tmp_path, one_root):
    registry, events, query = prepared()
    registry["receipts"] = registry["receipts"][:1] if one_root else []
    registry["rules"].append({"name": "cycle-2", "destination": 2, "branches": [3]})
    events["events"][3]["value"]["evidence"] = {
        "kind": "derived", "premises": [30], "sideReceipt": "cycle-2"}
    if not one_root:
        registry["rules"].append({"name": "cycle-1", "destination": 1, "branches": [3]})
        events["events"][1]["value"]["evidence"] = {
            "kind": "derived", "premises": [30], "sideReceipt": "cycle-1"}
    out = wire.execute(tmp_path, registry, events, query)
    assert out["state"]["held"] == ([1] if one_root else [])
    assert out["state"]["supports"] == ([10] if one_root else [])
