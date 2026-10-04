"""Native scoped rational registration, dependency closure, and query boundaries."""
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import pytest
EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("receipt_bridge", ROOT / "tools/run-phase2-slice.py")
bridge = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bridge)
EXE = ROOT / ("phase2/lean/.lake/build/bin/gp_scoped_runner" + EXE_SUFFIX)

def prepared():
    registry, events = bridge.prepared([copy.deepcopy(bridge.POLYNOMIALS["x"])],
                                      copy.deepcopy(bridge.POLYNOMIALS["x"]))
    root = registry["clauses"][0]
    root["binding"]["statementHash"] = bridge.digest({"object": "A", "generators": root["generators"],
                                                     "target": root["target"]})
    root["binding"]["scopeHash"] = bridge.digest([1, 2])
    root["binding"]["inputHashes"].append(bridge.digest("A"))
    registry["receipts"][0]["binding"] = copy.deepcopy(root["binding"])
    for event in events["events"]:
        event["value"]["binding"] = copy.deepcopy(root["binding"])
    dest = copy.deepcopy(root)
    dest["key"] = 2
    dest["binding"]["scopeHash"] = bridge.digest([1])
    registry = {"schema_version": 2, "clauses": [
        {"algebra": root, "object": "A", "scope": [1, 2]},
        {"algebra": dest, "object": "A", "scope": [1]}], "receipts": registry["receipts"]}
    events["events"].extend([
        {"kind": "current", "value": {"claim": 2, "version": 1, "binding": copy.deepcopy(dest["binding"])}},
        {"kind": "warrant", "value": {"id": 11, "claim": 2, "version": 1,
          "binding": copy.deepcopy(dest["binding"]), "evidence": {"kind": "narrow", "premise": 10}}}])
    query = {"schema_version": 1, "why_not": [2, 99], "claimed": [1],
             "links": [{"claim": 2, "obligations": [7, 8, 7]}], "open_obligations": [7]}
    return registry, events, query

def execute(folder, registry, events, query):
    paths = []
    for name, value in (("registry", registry), ("events", events), ("query", query)):
        path = folder / (name + ".json")
        path.write_text(value if isinstance(value, str) else json.dumps(value), encoding="utf-8")
        paths.append(path)
    result = subprocess.run([str(EXE), *map(str, paths)], cwd=ROOT,
                            text=True, encoding="utf-8", capture_output=True, check=True)
    return json.loads(result.stdout)

def test_actual_receipt_narrows_and_is_earned(tmp_path):
    out = execute(tmp_path, *prepared())
    assert out["state"]["held"] == [1, 2]
    assert out["release"] == {"allowed": True, "findings": []}
    assert out["state"]["supports"] == [10, 11]
    assert out["earned"] == [{"claim": 2, "open_obligations": [7]}]
    assert out["why_not"] == [
        {"claim": 2, "held": True, "warrants": [{"id": 11, "supported": True, "reasons": []}]},
        {"claim": 99, "held": False, "warrants": []}]

@pytest.mark.parametrize("mutation", ["object", "target", "scope", "statementHash",
                                      "modelHash", "inputHashes", "kernelVersion"])
def test_narrowing_does_not_change_objects_or_expand_scope(tmp_path, mutation):
    registry, events, query = prepared()
    dest = registry["clauses"][1]
    if mutation == "object":
        dest["object"] = "B"
    elif mutation == "target":
        dest["algebra"]["target"] = copy.deepcopy(bridge.POLYNOMIALS["x^2"])
    elif mutation == "scope":
        dest["scope"] = [1, 2, 3]
    else:
        dest["algebra"]["binding"][mutation] = (
            ["changed"] if mutation == "inputHashes" else 2 if mutation == "kernelVersion" else "changed")
        for event in events["events"][2:]:
            event["value"]["binding"] = copy.deepcopy(dest["algebra"]["binding"])
    out = execute(tmp_path, registry, events, query)
    assert out["state"]["held"] == [1]
    assert out["why_not"][0]["warrants"][0]["reasons"] == [
        {"kind": "refused_or_unregistered_evidence"}]

@pytest.mark.parametrize("cause", ["failed", "retracted", "absent", "bad_receipt"])
def test_missing_source_authority_blocks_descendant(tmp_path, cause):
    registry, events, query = prepared()
    if cause == "failed":
        events["events"][1]["value"]["evidence"] = {"kind": "attempt", "status": "failed"}
    elif cause == "retracted":
        events["events"].append({"kind": "retract", "target": 10})
    elif cause == "absent":
        del events["events"][1]
    else:
        registry["receipts"][0]["cofactors"] = []
    out = execute(tmp_path, registry, events, query)
    assert out["state"]["held"] == [] and out["earned"] == []
    assert out["why_not"][0]["warrants"][0]["reasons"] == [
        {"kind": "missing_premise_record" if cause == "absent" else "unsupported_premise", "id": 10}]

def test_queries_cannot_create_or_remove_held_authority(tmp_path):
    registry, events, query = prepared()
    baseline = execute(tmp_path, registry, events, query)
    query.update(claimed=[1, 2], links=[{"claim": 999, "obligations": [1, 2, 3]}],
                 open_obligations=[1, 2, 3], why_not=[999])
    out = execute(tmp_path, registry, events, query)
    assert out["state"] == baseline["state"]
    assert out["earned"] == []

def test_event_and_query_order_duplicates_preserve_results(tmp_path):
    registry, events, query = prepared()
    baseline = execute(tmp_path, registry, events, query)
    events["events"] = events["events"][::-1] * 2
    query["why_not"] = [99, 2, 2]
    query["links"] *= 2
    query["open_obligations"] *= 2
    assert execute(tmp_path, registry, events, query) == baseline

@pytest.mark.parametrize("defect", ["duplicate_id", "negative_scope", "scope_string",
                                    "extra_clause_field", "zero_den", "bad_query_version",
                                    "unknown_query_field", "bad_obligation_type", "raw_duplicate_query"])
def test_scoped_wire_malformed_is_explicit(tmp_path, defect):
    registry, events, query = prepared()
    if defect == "duplicate_id":
        registry["clauses"].append(copy.deepcopy(registry["clauses"][0]))
    elif defect == "negative_scope":
        registry["clauses"][1]["scope"] = [-1]
    elif defect == "scope_string":
        registry["clauses"][1]["scope"] = "tight"
    elif defect == "extra_clause_field":
        registry["clauses"][1]["success"] = True
    elif defect == "zero_den":
        registry["clauses"][0]["algebra"]["target"][0]["den"] = 0
    elif defect == "bad_query_version":
        query["schema_version"] = 2
    elif defect == "unknown_query_field":
        query["success"] = True
    elif defect == "bad_obligation_type":
        query["links"][0]["obligations"] = ["7"]
    else:
        query = '{"schema_version":1,' + json.dumps(query)[1:]
    out = execute(tmp_path, registry, events, query)
    assert out["status"] == "MALFORMED" and "state" not in out
