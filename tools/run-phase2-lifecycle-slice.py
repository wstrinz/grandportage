"""Run three unchanged operational lifecycle fixtures through Lean custody resolution."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import subprocess

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / ("phase2/lean/.lake/build/bin/gp_lifecycle_runner" + EXE_SUFFIX)
SCRATCH = ROOT / "tmp/phase2-lifecycle-slice"
CASES = ("GP-X144", "GP-X145", "GP-X146")
PIN = "ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
SOURCE = "tests/test_adversarial.py"
ANCHOR = "test_supersession_does_not_make_the_fold_order_dependent"
AUTHORITY = "gp50-inert-lifecycle-custody"
CHANGES = {"assertion": "annotation_only", "relation": "relation_reclassification",
           "argument": "restatement"}

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
    pin = json.loads((ROOT / "oracle/PIN.json").read_bytes())
    require(pin["commit"] == PIN, "source pin changed")
    checkout = ROOT / "oracle/checkout"
    git = ["git", "-c", "safe.directory=" + str(checkout), "-C", str(checkout)]
    head = subprocess.check_output(git + ["rev-parse", "HEAD"], text=True).strip()
    require(head in ORACLE_COMMITS, "source checkout is not pinned")
    pinned = subprocess.check_output(git + ["show", "HEAD:" + SOURCE])
    require((checkout / SOURCE).read_bytes() == pinned, "pinned source file modified")
    text = pinned.decode("utf-8")
    function = next(node for node in ast.parse(text).body
                    if isinstance(node, ast.FunctionDef) and node.name == ANCHOR)
    require(function.lineno == 3297, "source anchor moved")
    segment = "\n".join(text.splitlines()[function.lineno - 1:function.end_lineno])
    require('models + old + new' in segment and 'models + new + old' in segment
            and 'superseded_by' in segment and 'sorted(getattr' in segment,
            "source retained-record/branch-pointer contract missing")
    return {"commit": PIN, "path": SOURCE, "line": function.lineno,
            "anchor": "def " + ANCHOR + "(", "file_sha256": sha(pinned),
            "function_sha256": sha(segment.encode("utf-8")),
            "contract": "Same retained records in both concatenation orders; old successor pointer exists.",
            "fixture_boundary": "Literal unchanged fixture abstraction, not a reconstruction of predecessor object data."}

def checked_case(case_id, tags):
    raw = (ROOT / "corpus/must" / (case_id + ".json")).read_bytes()
    case = json.loads(raw)
    row = next(row for row in tags["cases"] if row["id"] == case_id)
    require(row["primary_layer"] == "kernel", "fixture is not kernel-tagged")
    require(sha(raw) == row["sha256"], "fixture bytes differ from layer pin")
    require(case["id"] == case_id and case["expected"]["verdict"] == "ACCEPT",
            "fixture identity/expectation changed")
    require(case["sources"] == [{"repository": "gp-v037", "commit": PIN,
        "path": SOURCE, "line": 3297, "anchor": "def " + ANCHOR + "("}],
        "fixture source pointer changed")
    return case, raw

def translate(case, source_sha256):
    require(case["id"] in CASES, "uncommissioned fixture")
    inputs = case["inputs"]
    require(set(inputs) == {"vocabulary", "objects", "history", "question", "branch_comparison"},
            "unsupported lifecycle input fields")
    require(inputs["vocabulary"] == "lifecycle-scenario/v1" and inputs["question"] == {},
            "unsupported lifecycle question/vocabulary")
    objects, history, branches = inputs["objects"], inputs["history"], inputs["branch_comparison"]
    require(set(branches) == {"common", "first_branch", "second_branch"}, "unsupported branch fields")
    forward = branches["common"] + branches["first_branch"] + branches["second_branch"]
    backward = branches["common"] + branches["second_branch"] + branches["first_branch"]
    require(history == forward, "history differs from recorded forward branches")
    require(len(history) == len(objects) and {step["object"] for step in history} == set(objects),
            "history does not retain each source object exactly once")
    keys = sorted(objects)
    ids = {key: index + 1 for index, key in enumerate(keys)}
    names = {}
    for key, obj in objects.items():
        require(set(obj) == {"category", "name", "properties"} and isinstance(obj["properties"], dict),
                "unsupported source object shape")
        require(obj["category"] in {"context", "assertion", "relation", "argument"}, "unsupported category")
        require(obj["name"] not in names, "ambiguous prior name")
        names[obj["name"]] = key
    steps = {step["object"]: step for step in history}
    records, links = [], []
    for key in keys:
        step, obj = steps[key], objects[key]
        require(set(step) <= {"object", "replacement"}, "unsupported history property")
        replacement = step.get("replacement")
        if replacement is not None:
            require(set(replacement) == {"prior", "change"} and replacement["prior"] in names,
                    "unresolved replacement")
            prior = names[replacement["prior"]]
            require(prior != key and objects[prior]["category"] == obj["category"],
                    "replacement changes category/identity")
            require(CHANGES.get(obj["category"]) == replacement["change"], "unsupported replacement change")
            links.append([ids[prior], ids[key]])
        identity = {"fixture": case["id"], "key": key, "category": obj["category"],
                    "name": obj["name"], "properties": obj["properties"], "replacement": replacement}
        binding = {"statementHash": digest(identity),
                   "scopeHash": digest({"mode": "inert-operational-custody"}),
                   "modelHash": digest({"vocabulary": inputs["vocabulary"], "category": obj["category"]}),
                   "inputHashes": [source_sha256, digest(obj), digest(step)],
                   "authority": AUTHORITY, "authorityVersion": 1, "kernelVersion": 1}
        records.append({"id": ids[key], "identity": identity, "binding": binding})
    require(len(links) == 1, "fixture requires exactly one recorded replacement")
    by_key = {record["identity"]["key"]: record for record in records}
    def events(order):
        result = []
        for step in order:
            record = by_key[step["object"]]
            value = {"claim": record["id"], "version": 1, "binding": record["binding"]}
            result.extend([{"kind": "declare_claim", "claim": record["id"]},
                           {"kind": "current", "value": value},
                           {"kind": "warrant", "value": dict(value, id=record["id"],
                                                         evidence={"kind": "assertion"})}])
            if "replacement" in step:
                result.append({"kind": "supersede", "target": ids[names[step["replacement"]["prior"]]],
                               "successor": record["id"]})
        return {"schema_version": 1, "events": result}
    return records, sorted(links), {"old_then_new": events(forward), "new_then_old": events(backward)}

def execute(label, events, runner=EXE):
    SCRATCH.mkdir(parents=True, exist_ok=True)
    path = SCRATCH / (label + ".events.json")
    path.write_bytes((encoded(events) + "\n").encode("utf-8"))
    result = subprocess.run([str(runner), str(path)], cwd=ROOT, capture_output=True,
                            text=True, encoding="utf-8", check=True)
    return json.loads(result.stdout), sha(path.read_bytes())

def verify(observed, records, links):
    require(observed["status"] == "OK", "native resolution failed")
    require(observed["admission"] == "refuseAll" and observed["resolve_fold_snapshot_equal"] is True,
            "native resolution/fold mismatch or admission changed")
    ids = [record["id"] for record in records]
    expected_warrants = [{"id": record["id"], "claim": record["id"], "version": 1,
                         "binding": record["binding"], "evidence": {"kind": "assertion"}}
                        for record in records]
    expected_currents = [{key: w[key] for key in ("claim", "version", "binding")}
                         for w in expected_warrants]
    expected_snapshot = {"domain": ids, "currents": expected_currents,
                         "warrants": expected_warrants, "retracted": [], "successors": links}
    require(observed["snapshot"] == expected_snapshot, "complete retained-record/link contract differs")
    require(observed["supports"] == [] and observed["held"] == [], "inert custody acquired authority")
    require(observed["held_queries"] == [{"claim": i, "held": False} for i in ids],
            "held queries differ")
    require(observed["live_warrants"] == [i for i in ids if i not in {edge[0] for edge in links}],
            "targeted supersession eligibility differs")

def run(output, runner=EXE):
    source = source_contract()
    tags = json.loads((ROOT / "corpus/LAYER-TAGS.json").read_bytes())
    results = []
    for case_id in CASES:
        case, raw = checked_case(case_id, tags)
        records, links, orders = translate(case, sha(raw))
        outputs, wire_hashes = {}, {}
        for order, events in orders.items():
            observed, wire_hash = execute(case_id + "-" + order, events, runner)
            verify(observed, records, links)
            outputs[order], wire_hashes[order] = observed, wire_hash
        require(outputs["old_then_new"] == outputs["new_then_old"], "branch orders differ")
        require((ROOT / "corpus/must" / (case_id + ".json")).read_bytes() == raw, "fixture changed")
        results.append({"id": case_id, "source_sha256": sha(raw), "expected": case["expected"],
                        "observed": "ACCEPT", "question": "retained records and successor links are order-independent",
                        "full_fixture_contract": True, "identity_records": records, "expected_successors": links,
                        "native_inputs": wire_hashes, "native_results": outputs,
                        "both_orders_equal": True, "mathematical_authority_admitted": False})
    report = {"schema": "gp-phase2-lifecycle-slice/v1", "case_count": len(results),
              "branch_executions": 2 * len(results), "complete_ten_case_slice": False, "g2_pass": False,
              "source_contract": source, "runner_path": str(runner),
              "runner_sha256": sha(runner.read_bytes()),
              "runner_source_sha256": sha((ROOT / "phase2/lean/GP50/LifecycleRunner.lean").read_bytes()),
              "adapter_sha256": sha(Path(__file__).read_bytes()), "cases": results,
              "binding_boundary": "Host canonical JSON and SHA-256 bind every literal source object and replacement annotation; Lean compares opaque identities.",
              "verdict_boundary": "ACCEPT answers branch resolution only. All source entities are inert assertion custody records; held and support remain empty."}
    output.write_bytes((json.dumps(report, indent=2) + "\n").encode("utf-8"))
    print("Lifecycle slice: 3 unchanged fixtures, 6 native branch folds, complete records/links equal; held empty.")
    return report

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "reports/PHASE-2-LIFECYCLE-SLICE.json")
    parser.add_argument("--runner", type=Path, default=EXE)
    args = parser.parse_args()
    run(args.output, args.runner)
