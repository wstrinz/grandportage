"""Finite native custody replay of three unchanged declaration fixtures."""
import argparse
import ast
import copy
import hashlib
import json
from pathlib import Path
import subprocess

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / ("phase2/lean/.lake/build/bin/gp_lifecycle_runner" + EXE_SUFFIX)
SCRATCH = ROOT / "tmp/phase2-declaration-slice"
CASES = ("GP-A25a", "GP-C03", "GP-X143")
PIN = "ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
SOURCE = "tests/test_store.py"
AUTHORITY = "gp50-inert-declaration-custody"
ANCHORS = {
    "identical": (36, "test_identical_redeclaration_is_idempotent"),
    "conflicting": (43, "test_conflicting_redeclaration_is_a_hard_error"),
}
CASE_HASHES = {
    "GP-A25a": "c9c6ae9adecb86d5b2f1dca8ce4a657742bff99f9e1f29363e336861a54bcabd",
    "GP-C03": "d81d7dcead2a1e42fba49d4a2017c2b2257a468bb6c99c344667bc442f0a8b16",
    "GP-X143": "316c7ad6376c90b0ed974620fe6434a13e6d1fc8d49a5538b92a1598b5deb5c8",
}
ROUTES = {
    "GP-A25a": {"kind": "redeclaration", "layer": "graph_validation", "conflict": True},
    "GP-C03": {"kind": "redeclaration", "layer": "graph_validation", "conflict": False},
    "GP-X143": {"kind": "lifecycle", "action": "fold", "layer": "lifecycle_contract",
        "limitation": "Frozen v0.37 lifecycle/binding contract, not a GP 0.50 held claim. No external backend. Receipt routes explicitly use fabricated historical backend descriptors; section arithmetic is replayed separately by the fold."},
}

def require(condition, message):
    if not condition:
        raise ValueError(message)

def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def digest(value):
    return sha(encoded(value).encode("utf-8"))

def source_contract():
    pin_raw = (ROOT / "oracle/PIN.json").read_bytes()
    require(json.loads(pin_raw)["commit"] == PIN, "source pin changed")
    checkout = ROOT / "oracle/checkout"
    git = ["git", "-c", "safe.directory=" + str(checkout), "-C", str(checkout)]
    require(subprocess.check_output(git + ["rev-parse", "HEAD"], text=True).strip() in ORACLE_COMMITS,
            "source checkout is not pinned")
    raw = subprocess.check_output(git + ["show", "HEAD:" + SOURCE])
    require((checkout / SOURCE).read_bytes() == raw, "pinned source file modified")
    text = raw.decode("utf-8")
    tree = ast.parse(text)
    functions = {}
    for kind, (line, name) in ANCHORS.items():
        node = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == name)
        require(node.lineno == line, "source anchor moved")
        segment = "\n".join(text.splitlines()[node.lineno - 1:node.end_lineno])
        if kind == "identical":
            require("dict(MODEL_A)" in segment and "len(g.models) == 2" in segment,
                    "pinned idempotence contract changed")
        else:
            require("pytest.raises(S.GraphError)" in segment and
                    '"conflicting redeclaration"' in segment and "SOMETHING ELSE" in segment,
                    "pinned collision contract changed")
        functions[kind] = {"line": line, "anchor": "def " + name + "(",
                           "function_sha256": sha(segment.encode("utf-8"))}
    return {"commit": PIN, "path": SOURCE, "file_sha256": sha(raw),
            "pin_file_sha256": sha(pin_raw), "functions": functions,
            "boundary": "Replay the unchanged fixture declarations, not a reconstruction of predecessor MODEL_A/MODEL_B or EDGE_AB."}

def checked_case(case_id, tags, routes):
    require(case_id in CASES, "uncommissioned fixture")
    raw = (ROOT / "corpus/must" / (case_id + ".json")).read_bytes()
    case = json.loads(raw)
    row = next(row for row in tags["cases"] if row["id"] == case_id)
    require(sha(raw) == CASE_HASHES[case_id] == row["sha256"], "fixture bytes changed")
    require(row["primary_layer"] == "kernel" and row["full_contract_required"] is True
            and row["g2_kernel_eligible"] is True, "layer contract changed")
    require(routes["commit"] == PIN and routes["routes"][case_id] == ROUTES[case_id],
            "legacy route changed")
    require(case["id"] == case_id and case["schema_version"] == 1 and
            case["expected"]["verdict"] == ("ACCEPT" if case_id == "GP-C03" else "REFUSE"),
            "fixture identity/expectation changed")
    anchor_kind = "identical" if case_id == "GP-C03" else "conflicting"
    line, name = ANCHORS[anchor_kind]
    sources = [{"repository": "gp-v037", "commit": PIN, "path": SOURCE,
                "line": line, "anchor": "def " + name + "("}]
    if case_id == "GP-A25a":
        sources.insert(0, {"repository": "rework-packet", "path": "docs/GP-0.50-REWORK-PACKET.md",
                           "line": 565, "anchor": "| A25 |"})
    require(case["sources"] == sources, "fixture source pointers changed")
    return case, raw, row

def declarations(case):
    require(case["id"] in CASES, "uncommissioned fixture")
    inputs = case["inputs"]
    require(isinstance(inputs, dict), "inputs must be an object")
    result = []
    if case["id"] == "GP-A25a":
        require(set(inputs) == {"declarations"} and isinstance(inputs["declarations"], list)
                and len(inputs["declarations"]) == 2, "unsupported declaration input")
        for obj in inputs["declarations"]:
            require(isinstance(obj, dict) and set(obj) == {"id", "description"},
                    "unsupported declaration fields")
            require(all(isinstance(obj[k], str) and obj[k] for k in obj),
                    "declaration identifiers/descriptions must be nonempty strings")
            result.append({"identifier": obj["id"], "description": obj["description"]})
    elif case["id"] == "GP-C03":
        require(set(inputs) == {"id", "description", "repetitions"} and
                type(inputs["repetitions"]) is int and inputs["repetitions"] == 2,
                "unsupported repetition contract")
        require(all(isinstance(inputs[k], str) and inputs[k] for k in ("id", "description")),
                "declaration identifiers/descriptions must be nonempty strings")
        result = [{"identifier": inputs["id"], "description": inputs["description"]}] * 2
    else:
        require(set(inputs) == {"vocabulary", "objects", "history", "question"} and
                inputs["vocabulary"] == "lifecycle-scenario/v1" and inputs["question"] == {},
                "unsupported lifecycle input")
        objects, history = inputs["objects"], inputs["history"]
        require(isinstance(objects, dict) and len(objects) == 2 and isinstance(history, list)
                and len(history) == 2, "unsupported object/history cardinality")
        keys = []
        for step in history:
            require(isinstance(step, dict) and set(step) == {"object"} and
                    isinstance(step["object"], str) and step["object"] in objects,
                    "unsupported declaration history")
            keys.append(step["object"])
        require(len(set(keys)) == len(keys) and set(keys) == set(objects),
                "history must retain each source object once")
        for key in keys:
            obj = objects[key]
            require(isinstance(obj, dict) and set(obj) == {"category", "name", "properties"} and
                    obj["category"] == "context" and isinstance(obj["name"], str) and obj["name"],
                    "unsupported object declaration")
            require(isinstance(obj["properties"], dict) and set(obj["properties"]) == {"description"}
                    and isinstance(obj["properties"]["description"], str)
                    and obj["properties"]["description"], "unsupported object properties")
            result.append({"identifier": obj["name"], **copy.deepcopy(obj)})
    return result

def translate(case, source_sha256):
    payloads = declarations(case)
    identifiers = sorted({payload["identifier"] for payload in payloads})
    ids = {name: index + 1 for index, name in enumerate(identifiers)}
    records, groups = [], []
    for payload in payloads:
        identity = {"fixture": case["id"], "declaration": payload}
        binding = {"statementHash": digest(identity),
            "scopeHash": digest({"mode": "inert-declaration-custody"}),
            "modelHash": digest({"identifier": payload["identifier"]}),
            "inputHashes": [source_sha256, digest(payload)], "authority": AUTHORITY,
            "authorityVersion": 1, "kernelVersion": 1}
        record = {"id": ids[payload["identifier"]], "claim": ids[payload["identifier"]],
                  "version": 1, "binding": binding,
                  "evidence": {"kind": "citation", "text": encoded(identity)}}
        records.append(record)
        groups.append([{"kind": "declare_claim", "claim": record["claim"]},
                       {"kind": "warrant", "value": copy.deepcopy(record)}])
    forward = [event for group in groups for event in group]
    backward = [event for group in reversed(groups) for event in group]
    orders = {"forward": forward, "reverse": backward,
              "forward_duplicates": forward + copy.deepcopy(forward),
              "reverse_duplicates": backward + copy.deepcopy(backward)}
    return payloads, records, {label: {"schema_version": 1, "events": events}
                              for label, events in orders.items()}

def execute(label, wire, runner=EXE):
    SCRATCH.mkdir(parents=True, exist_ok=True)
    path = SCRATCH / (label + ".events.json")
    path.write_bytes((encoded(wire) + "\n").encode("utf-8"))
    result = subprocess.run([str(runner), str(path)], cwd=ROOT, capture_output=True,
                            text=True, encoding="utf-8", check=True)
    return json.loads(result.stdout), sha(path.read_bytes())

def verify_ok(observed, records):
    unique = {encoded(record): record for record in records}
    retained = sorted(unique.values(), key=lambda record: record["id"])
    require(len({r["id"] for r in retained}) == len(retained),
            "positive comparison requires unambiguous identifiers")
    ids = [record["id"] for record in retained]
    expected = {"status": "OK", "admission": "refuseAll", "resolve_fold_snapshot_equal": True,
                "snapshot": {"domain": ids, "currents": [], "warrants": retained,
                             "retracted": [], "successors": []},
                "supports": [], "held": [], "live_warrants": [],
                "held_queries": [{"claim": key, "held": False} for key in ids]}
    require(observed == expected, "complete native custody records or authority outputs differ")
    return expected

def verify_collision(observed, records):
    # Expected diagnostics are computed only after the native run; no host refusal replaces it.
    collisions = sorted({a["id"] for a in records for b in records
                         if a["id"] == b["id"] and a != b})
    require(bool(collisions), "collision comparison requires conflicting contents")
    expected = {"status": "MALFORMED", "error": "conflicting warrant contents: " + str(collisions[0])}
    require(observed == expected, "native collision diagnostic differs")
    return expected

def repaired_case(case, rename=False):
    repaired = copy.deepcopy(case)
    inputs = repaired["inputs"]
    if case["id"] == "GP-A25a":
        if rename:
            inputs["declarations"][1]["id"] += "-distinct"
        else:
            inputs["declarations"][1] = copy.deepcopy(inputs["declarations"][0])
    elif case["id"] == "GP-X143":
        keys = [step["object"] for step in inputs["history"]]
        if rename:
            inputs["objects"][keys[1]]["name"] += "-distinct"
        else:
            inputs["objects"][keys[1]] = copy.deepcopy(inputs["objects"][keys[0]])
    else:
        raise ValueError("repair controls are only for the two collision fixtures")
    return repaired

def run(output, runner=EXE):
    source = source_contract()
    metadata = {name: (ROOT / path).read_bytes() for name, path in {
        "layer_tags": "corpus/LAYER-TAGS.json", "routes": "oracle/ROUTES.json",
        "pin": "oracle/PIN.json"}.items()}
    tags, routes = json.loads(metadata["layer_tags"]), json.loads(metadata["routes"])
    executable_hash = sha(runner.read_bytes())
    adapter_hash = sha(Path(__file__).read_bytes())
    results, controls = [], []
    for case_id in CASES:
        case, raw, layer = checked_case(case_id, tags, routes)
        payloads, records, orders = translate(case, sha(raw))
        outputs, inputs = {}, {}
        for order, wire in orders.items():
            observed, wire_hash = execute(case_id + "-" + order, wire, runner)
            if case["expected"]["verdict"] == "ACCEPT":
                verify_ok(observed, records)
            else:
                verify_collision(observed, records)
            outputs[order], inputs[order] = observed, wire_hash
        require(all(value == outputs["forward"] for value in outputs.values()),
                "order or exact duplicate changed native result")
        results.append({"id": case_id, "source_sha256": sha(raw), "expected": case["expected"],
            "sources": case["sources"], "layer_entry": layer, "legacy_route": routes["routes"][case_id],
            "executed": True, "observed": "ACCEPT" if outputs["forward"]["status"] == "OK" else "REFUSE", "full_fixture_contract": True,
            "literal_inputs": case["inputs"],
            "literal_declarations": payloads, "native_identity_records": records,
            "native_input_sha256": inputs, "native_results": outputs,
            "both_orders_and_duplicates_equal": True, "mathematical_authority_admitted": False})
        if case_id != "GP-C03":
            for label, rename in (("equal_contents", False), ("distinct_identifiers", True)):
                repaired = repaired_case(case, rename)
                repair_payloads, repair_records, repair_orders = translate(repaired, sha(raw))
                repair_outputs, repair_inputs = {}, {}
                for order, wire in repair_orders.items():
                    observed, wire_hash = execute(case_id + "-control-" + label + "-" + order, wire, runner)
                    verify_ok(observed, repair_records)
                    repair_outputs[order], repair_inputs[order] = observed, wire_hash
                require(all(value == repair_outputs["forward"] for value in repair_outputs.values()),
                        "repaired control depends on order or multiplicity")
                controls.append({"source_case": case_id, "repair": label, "corpus_case": False,
                    "repair_inputs": repaired["inputs"],
                    "literal_declarations": repair_payloads, "native_identity_records": repair_records,
                    "native_input_sha256": repair_inputs, "native_results": repair_outputs,
                    "retained_record_count": len(repair_outputs["forward"]["snapshot"]["warrants"])})
        require((ROOT / "corpus/must" / (case_id + ".json")).read_bytes() == raw, "fixture changed")
    require(sha(runner.read_bytes()) == executable_hash and sha(Path(__file__).read_bytes()) == adapter_hash,
            "runner/adapter changed during replay")
    for name, path in {"layer_tags": "corpus/LAYER-TAGS.json", "routes": "oracle/ROUTES.json",
                       "pin": "oracle/PIN.json"}.items():
        require((ROOT / path).read_bytes() == metadata[name], "registry/pin changed during replay")
    require(source_contract() == source, "pinned source changed during replay")
    report = {"schema": "gp-phase2-declaration-slice/v1", "case_count": 3,
        "corpus_native_executions": 12, "repaired_control_executions": 16,
        "complete_ten_case_slice": False, "g2_pass": False, "source_contract": source,
        "registry_sha256": {name: sha(raw) for name, raw in metadata.items()},
        "runner_path": str(runner), "runner_sha256": executable_hash,
        "runner_source_sha256": sha((ROOT / "phase2/lean/GP50/LifecycleRunner.lean").read_bytes()),
        "kernel_source_sha256": {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in [
            ROOT / "phase2/lean/GP50/Events.lean", ROOT / "phase2/lean/GP50/Runtime.lean",
            ROOT / "phase2/lean/GP50/Decoder.lean", ROOT / "phase2/lean/GP50/Closure.lean"]},
        "adapter_sha256": adapter_hash,
        "test_source_sha256": sha((ROOT / "tests/test_phase2_declaration_slice.py").read_bytes()),
        "cases": results, "controls": controls,
        "binding_boundary": "Host canonical JSON/SHA-256 binds literal declarations. Same identifier maps to same native warrant ID. Occurrence keys/order are provenance, not declaration content.",
        "verdict_boundary": "Complete declaration collision/idempotence fixture contracts only. Literal payloads remain inert citations; no current binding, evidence checker, mathematical claim authority, or Rat replacement is introduced."}
    output.write_bytes((json.dumps(report, indent=2) + "\n").encode("utf-8"))
    print("Declaration slice: 3 unchanged cases, 12 native original folds, 16 repaired controls; complete custody records checked, held empty.")
    return report

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "reports/PHASE-2-DECLARATION-SLICE.json")
    parser.add_argument("--runner", type=Path, default=EXE)
    args = parser.parse_args()
    run(args.output, args.runner)
