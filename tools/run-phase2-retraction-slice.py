"""Finite native targeted-retraction replay; custody is not checked support."""
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
SCRATCH = ROOT / "tmp/phase2-retraction-slice"
CASES = ("GP-X142", "GP-X147", "GP-X148")
PIN = "ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
IDENTIFIERS = {"M": 1, "N": 2, "C": 3, "I": 4, "I2": 5, "R-I": 6}
HASHES = {
    "GP-X142": "ae102b68cdc590d868863c0e0a25bc0758e9df5f9d34e6abc9979fba240bbb5d",
    "GP-X147": "65f4d458ad5facd8cc55e072003e1abf326c5696da2559fe3ec042706b8f2b8d",
    "GP-X148": "c19b97a71d30c0a0383c030dac64bf8419a8ca44206de8228e6714a1fc744946",
}
ANCHORS = {
    "GP-X142": ("tests/test_store.py", 36, "test_identical_redeclaration_is_idempotent"),
    "GP-X147": ("tests/test_supersession_noise.py", 92, "test_minimal_inference_retract_is_not_a_live_successor"),
    "GP-X148": ("tests/test_supersession_noise.py", 92, "test_minimal_inference_retract_is_not_a_live_successor"),
}
LIMITATION = "Frozen v0.37 lifecycle/binding contract, not a GP 0.50 held claim. No external backend. Receipt routes explicitly use fabricated historical backend descriptors; section arithmetic is replayed separately by the fold."

def require(condition, message):
    if not condition:
        raise ValueError(message)

def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def digest(value):
    return sha(encoded(value).encode("utf-8"))

def fields(value, keys, message):
    require(isinstance(value, dict) and set(value) == set(keys), message)

def source_contract():
    pin_raw = (ROOT / "oracle/PIN.json").read_bytes()
    require(json.loads(pin_raw)["commit"] == PIN, "source pin changed")
    checkout = ROOT / "oracle/checkout"
    git = ["git", "-c", "safe.directory=" + str(checkout), "-C", str(checkout)]
    require(subprocess.check_output(git + ["rev-parse", "HEAD"], text=True).strip() in ORACLE_COMMITS,
            "source checkout is not pinned")
    result = {}
    for path, line, name in sorted(set(ANCHORS.values())):
        raw = subprocess.check_output(git + ["show", "HEAD:" + path])
        require((checkout / path).read_bytes() == raw, "pinned source file modified")
        text = raw.decode("utf-8")
        node = next(n for n in ast.parse(text).body if isinstance(n, ast.FunctionDef) and n.name == name)
        require(node.lineno == line, "source anchor moved")
        segment = "\n".join(text.splitlines()[node.lineno - 1:node.end_lineno])
        needles = ('dict(MODEL_A)', 'len(g.models) == 2') if line == 36 else (
            'g.inference_order == ["I"]', '"R-I" not in g.inferences',
            'g.inferences["I"]["retracted_by"] == "R-I"',
            '("inference", "R-I") in g.retractions', '"I" not in C.clean_inferences')
        require(all(n in segment for n in needles), "named predecessor contract changed")
        result[path] = {"line": line, "anchor": "def " + name + "(",
                        "file_sha256": sha(raw), "function_sha256": sha(segment.encode("utf-8"))}
    return {"commit": PIN, "pin_file_sha256": sha(pin_raw), "functions": result,
            "boundary": "Only named source functions; literal fixtures remain the inputs. The withdrawal is retained separately as inert custody, not a successor inference."}

def checked_case(case_id, tags, routes):
    require(case_id in CASES, "uncommissioned fixture")
    raw = (ROOT / "corpus/must" / (case_id + ".json")).read_bytes()
    case = json.loads(raw)
    row = next(r for r in tags["cases"] if r["id"] == case_id)
    require(sha(raw) == HASHES[case_id] == row["sha256"], "fixture bytes changed")
    require(row["primary_layer"] == "kernel" and row["full_contract_required"] is True
            and row["g2_kernel_eligible"] is True, "layer contract changed")
    route = {"kind": "lifecycle", "action": "fold" if case_id == "GP-X142" else "clean",
             "layer": "lifecycle_contract", "limitation": LIMITATION}
    require(routes["commit"] == PIN and routes["routes"][case_id] == route, "route changed")
    path, line, name = ANCHORS[case_id]
    require(case["sources"] == [{"repository": "gp-v037", "commit": PIN, "path": path,
                                "line": line, "anchor": "def " + name + "("}], "source pointers changed")
    require(case["expected"]["verdict"] == ("REFUSE" if case_id == "GP-X147" else "ACCEPT"),
            "expectation changed")
    return case, raw, row

def translate(case, source_sha256):
    fields(case, ("schema_version", "id", "seed", "title", "situation", "inputs",
                  "attempted_conclusion", "expected", "scope_or_region", "sources"), "unknown fixture fields")
    require(case["id"] in CASES and case["schema_version"] == 1, "unsupported fixture")
    inputs = case["inputs"]
    fields(inputs, ("vocabulary", "objects", "history", "question"), "unsupported input fields")
    require(inputs["vocabulary"] == "lifecycle-scenario/v1", "unsupported vocabulary")
    objects, history = inputs["objects"], inputs["history"]
    require(isinstance(objects, dict) and objects and isinstance(history, list) and history,
            "empty or malformed objects/history")
    names = {}
    for key, obj in objects.items():
        require(isinstance(key, str) and key, "invalid source object key")
        fields(obj, ("category", "name", "properties"), "unknown object fields")
        require(isinstance(obj["name"], str) and obj["name"] and obj["name"] not in names,
                "ambiguous source identifier")
        names[obj["name"]] = key
        p = obj["properties"]
        if obj["category"] == "context":
            fields(p, ("description",), "unknown context properties")
        elif obj["category"] == "assertion":
            fields(p, ("context", "statement_class", "statement"), "unknown assertion properties")
            require(p["statement_class"] == "universal_property", "unsupported statement class")
        elif obj["category"] == "argument":
            if isinstance(p, dict) and "justification" in p:
                fields(p, ("justification",), "withdrawal must be inert")
            else:
                fields(p, ("premise", "transport_route", "conclusion_class", "conclusion"),
                       "unknown argument properties")
                require(p["transport_route"] == [] and p["conclusion_class"] == "universal_property",
                        "unsupported transport route/conclusion class")
        else:
            raise ValueError("unsupported category")
        require(all(isinstance(v, str) and v for k, v in p.items() if k != "transport_route"),
                "properties must retain nonempty literal strings")
    for obj in objects.values():
        p = obj["properties"]
        if obj["category"] == "assertion":
            require(p["context"] in names and objects[names[p["context"]]]["category"] == "context",
                    "unresolved assertion context")
        if "premise" in p:
            require(p["premise"] in names and objects[names[p["premise"]]]["category"] == "assertion",
                    "unresolved argument premise")
    steps, withdrawal_keys = {}, []
    for step in history:
        require(isinstance(step, dict) and set(step) in ({"object"}, {"object", "replacement"}),
                "unknown history fields")
        key = step["object"]
        require(isinstance(key, str) and key in objects, "unresolved history object")
        require(key not in steps or steps[key] == step, "inconsistent repeated history")
        steps[key] = step
        if "replacement" in step:
            r = step["replacement"]
            fields(r, ("prior", "change"), "unknown replacement fields")
            require(r["change"] == "argument_retraction" and r["prior"] in names,
                    "unresolved retraction target")
            target = objects[names[r["prior"]]]
            require(target["category"] == "argument" and "premise" in target["properties"],
                    "retraction target must be an inference")
            require(objects[key]["category"] == "argument"
                    and set(objects[key]["properties"]) == {"justification"}, "withdrawal record changed")
            withdrawal_keys.append(key)
    require(set(steps) == set(objects), "history must retain every object")
    inert = {k for k, o in objects.items() if "justification" in o["properties"]}
    require(inert == set(withdrawal_keys) and len(inert) == (0 if case["id"] == "GP-X142" else 1),
            "withdrawal history mismatch")
    question = inputs["question"]
    fields(question, () if case["id"] == "GP-X142" else ("object",), "unknown query fields")
    if question:
        require(question["object"] in names and "premise" in objects[names[question["object"]]]["properties"],
                "query must identify an inference")
    require(set(names) <= set(IDENTIFIERS), "uncommissioned source identifier")
    ids = {name: IDENTIFIERS[name] for name in names}
    records, currents, identities = [], [], []
    by_key = {}
    for key in sorted(objects, key=lambda k: ids[objects[k]["name"]]):
        obj, step = objects[key], steps[key]
        identity = {"fixture": case["id"], "source_key": key, "object": copy.deepcopy(obj),
                    "history_step": copy.deepcopy(step),
                    "role": "withdrawal-custody" if key in inert else "declaration-custody"}
        binding = {"statementHash": digest(identity), "scopeHash": digest({"mode": "inert-retraction-custody"}),
                   "modelHash": digest({"vocabulary": inputs["vocabulary"], "identifier": obj["name"]}),
                   "inputHashes": [source_sha256, digest(obj), digest(step)],
                   "authority": "gp50-inert-retraction-custody", "authorityVersion": 1, "kernelVersion": 1}
        current = {"claim": ids[obj["name"]], "version": 1, "binding": binding}
        record = dict(current, id=ids[obj["name"]], evidence={"kind": "citation", "text": encoded(identity)})
        records.append(record)
        identities.append(identity)
        if key not in inert:
            currents.append(current)
        by_key[key] = record
    def events(order):
        result = []
        for step in order:
            key = step["object"]
            record = by_key[key]
            result.append({"kind": "declare_claim", "claim": record["claim"]})
            if key not in inert:
                result.append({"kind": "current", "value": {k: record[k] for k in ("claim", "version", "binding")}})
            result.append({"kind": "warrant", "value": copy.deepcopy(record)})
            if "replacement" in step:
                result.append({"kind": "retract", "target": ids[step["replacement"]["prior"]]})
        return result
    forward, reverse = events(history), events(list(reversed(history)))
    orders = {"forward": forward, "reverse": reverse,
              "forward_duplicates": forward + copy.deepcopy(forward),
              "reverse_duplicates": reverse + copy.deepcopy(reverse)}
    targets = sorted({ids[s["replacement"]["prior"]] for s in steps.values() if "replacement" in s})
    return {"ids": ids, "records": records, "currents": currents, "identities": identities,
            "history": copy.deepcopy(history), "question": copy.deepcopy(question), "targets": targets,
            "query_id": ids[question["object"]] if question else None,
            "orders": {k: {"schema_version": 1, "events": v} for k, v in orders.items()}}

def execute(label, wire, runner=EXE):
    SCRATCH.mkdir(parents=True, exist_ok=True)
    path = SCRATCH / (label + ".events.json")
    path.write_bytes((encoded(wire) + "\n").encode("utf-8"))
    result = subprocess.run([str(runner), str(path)], cwd=ROOT, capture_output=True,
                            text=True, encoding="utf-8", check=True)
    return json.loads(result.stdout), sha(path.read_bytes())

def expected_output(plan, targets=None):
    targets = plan["targets"] if targets is None else sorted(set(targets))
    domain = sorted(plan["ids"].values())
    # This is a post-run comparison oracle only. Every warrant is sent to Lean.
    live = [r["id"] for r in plan["records"] if r["id"] in {c["claim"] for c in plan["currents"]}
            and r["id"] not in targets]
    return {"status": "OK", "admission": "refuseAll", "resolve_fold_snapshot_equal": True,
            "snapshot": {"domain": domain, "currents": plan["currents"], "warrants": plan["records"],
                         "retracted": targets, "successors": []},
            "supports": [], "held": [], "held_queries": [{"claim": i, "held": False} for i in domain],
            "live_warrants": live}

def verify(observed, plan, targets=None):
    require(observed == expected_output(plan, targets), "complete native records/bindings/liveness differ")
    return observed["live_warrants"]

def controls(plan, runner=EXE):
    base = plan["orders"]["forward"]
    result = {}
    def run(label, wire, targets):
        observed, wire_hash = execute("control-" + label, wire, runner)
        verify(observed, plan, targets)
        result[label] = {"input_sha256": wire_hash, "native_result": observed,
                         "I_live": plan["ids"]["I"] in observed["live_warrants"],
                         "I2_live": plan["ids"]["I2"] in observed["live_warrants"]}
    absent = copy.deepcopy(base)
    absent["events"] = [e for e in absent["events"] if e["kind"] != "retract"]
    run("missing_retraction", absent, [])
    wrong = copy.deepcopy(base)
    for e in wrong["events"]:
        if e["kind"] == "retract":
            e["target"] = plan["ids"]["I2"]
    run("wrong_neighbor_target", wrong, [plan["ids"]["I2"]])
    unknown = copy.deepcopy(base)
    for e in unknown["events"]:
        if e["kind"] == "retract":
            e["target"] = 999
    run("unknown_target", unknown, [999])
    collision = copy.deepcopy(base)
    changed = copy.deepcopy(plan["records"][next(i for i, r in enumerate(plan["records"]) if r["id"] == plan["ids"]["I2"])])
    changed["id"] = plan["ids"]["I"]
    collision["events"].append({"kind": "warrant", "value": changed})
    observed, wire_hash = execute("control-wrong-immutable-identity", collision, runner)
    require(observed == {"status": "MALFORMED", "error": "conflicting warrant contents: " + str(plan["ids"]["I"])},
            "identity collision escaped native validation")
    result["wrong_immutable_identity"] = {"input_sha256": wire_hash, "native_result": observed}
    for label in ("unknown_root_field", "unknown_event_field"):
        wire = copy.deepcopy(base)
        (wire if label == "unknown_root_field" else wire["events"][0])["ignored"] = True
        observed, wire_hash = execute("control-" + label, wire, runner)
        require(observed == {"status": "MALFORMED", "error": "unexpected field: ignored"},
                "unknown native input field escaped fail-closed decoding")
        result[label] = {"input_sha256": wire_hash, "native_result": observed}
    run("repaired_target_and_identity", copy.deepcopy(base), plan["targets"])
    require(result["wrong_neighbor_target"]["I_live"] and not result["wrong_neighbor_target"]["I2_live"]
            and not result["repaired_target_and_identity"]["I_live"]
            and result["repaired_target_and_identity"]["I2_live"], "controls failed to distinguish targets")
    return result

def run(output, runner=EXE):
    protected = [ROOT / p for p in ("oracle/PIN.json", "oracle/ROUTES.json", "corpus/LAYER-TAGS.json")]
    before = {str(p): p.read_bytes() for p in protected}
    source = source_contract()
    runner_hash = sha(runner.read_bytes())
    tags, routes = json.loads(protected[2].read_bytes()), json.loads(protected[1].read_bytes())
    results, plans = [], {}
    for case_id in CASES:
        case, raw, row = checked_case(case_id, tags, routes)
        plan = translate(case, sha(raw))
        plans[case_id] = plan
        outputs, hashes = {}, {}
        for label, wire in plan["orders"].items():
            observed, wire_hash = execute(case_id + "-" + label, wire, runner)
            verify(observed, plan)
            outputs[label], hashes[label] = observed, wire_hash
        require(all(o == outputs["forward"] for o in outputs.values()), "order/duplicates changed result")
        live = outputs["forward"]["live_warrants"]
        verdict = ("ACCEPT" if len(outputs["forward"]["snapshot"]["warrants"]) == 1 else "REFUSE") if case_id == "GP-X142" else ("ACCEPT" if plan["query_id"] in live else "REFUSE")
        require(verdict == case["expected"]["verdict"], "native query verdict differs")
        require((ROOT / "corpus/must" / (case_id + ".json")).read_bytes() == raw, "fixture changed")
        results.append({"id": case_id, "source_sha256": sha(raw), "expected": case["expected"],
                        "observed": verdict, "source_identifier_to_native_id": plan["ids"],
                        "literal_identity_records": plan["identities"], "literal_history": plan["history"],
                        "question": plan["question"], "query_id": plan["query_id"],
                        "query_live": plan["query_id"] in live if plan["query_id"] is not None else None,
                        "layer_entry": row, "native_inputs": hashes, "native_results": outputs,
                        "all_orders_and_duplicates_equal": True,
                        "lifecycle_contract_executed": True, "executed": True,
                        "full_fixture_contract": True, "checked_support_obligation_closed": False})
    control_results = controls(plans["GP-X148"], runner)
    require(all(p.read_bytes() == before[str(p)] for p in protected), "protected metadata changed")
    require(sha(runner.read_bytes()) == runner_hash and source_contract() == source, "source/runner changed")
    report = {"schema": "gp-phase2-retraction-slice/v1", "case_count": 3, "native_executions": 19,
              "source_contract": source, "protected_input_hashes": {k: sha(v) for k, v in before.items()},
              "runner_path": str(runner), "runner_sha256": runner_hash,
              "runner_source_sha256": sha((ROOT / "phase2/lean/GP50/LifecycleRunner.lean").read_bytes()),
              "adapter_sha256": sha(Path(__file__).read_bytes()),
              "test_source_sha256": sha((ROOT / "tests/test_phase2_retraction_slice.py").read_bytes()),
              "kernel_source_sha256": {name: sha((ROOT / ("phase2/lean/GP50/" + name + ".lean")).read_bytes())
                  for name in ("Events", "Runtime", "Closure", "Decoder")},
              "corpus_native_folds": 12, "separate_control_folds": 7,
              "cases": results, "controls": control_results,
              "g2_pass": False, "complete_ten_case_slice": False,
              "checked_support_obligation_closed": False,
              "boundary": "Admission.refuseAll: all literal objects are opaque citation custody; no checked truth or support is supplied. Native retract decides live eligibility. X148 executes lifecycle isolation only and does not close the required independent checked-support/retraction obligation.",
              "binding_boundary": "Host canonical JSON/SHA-256 bind complete objects and history steps; native Lean compares opaque identities and retains all records. No host liveness prefilter."}
    output.write_bytes((json.dumps(report, indent=2) + "\n").encode("utf-8"))
    print("Retraction slice: 3 unchanged fixtures, 19 native executions; lifecycle only, held/supports empty.")
    return report

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "reports/PHASE-2-RETRACTION-SLICE.json")
    parser.add_argument("--runner", type=Path, default=EXE)
    args = parser.parse_args()
    run(args.output, args.runner)
