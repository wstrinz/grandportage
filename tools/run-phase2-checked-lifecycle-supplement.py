"""Checked lifecycle supplements from unchanged X164; no corpus passes added."""
import argparse
import ast
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ROOT = Path(__file__).resolve().parents[1]
SCRATCH = ROOT / "tmp/phase2-checked-lifecycle-supplement"
BIN = ROOT / "phase2/lean/.lake/build/bin"
RUNNERS = {k: BIN / ("gp_" + k + ("_runner" + EXE_SUFFIX)) for k in ("span", "scoped", "lifecycle")}
PIN = "ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
CASE_HASH = "3380ad2566475144e05b162f3113e02ead4faf3ea5a92c568f9fa0b5e8a24fed"
HELPER = ROOT / "tools/run-phase2-slice.py"
spec = importlib.util.spec_from_file_location("reviewed_slice", HELPER)
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)

def require(condition, message):
    if not condition:
        raise ValueError(message)

def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def source_contract():
    path = "tests/test_verdict_provenance.py"
    checkout = ROOT / "oracle/checkout"
    git = ["git", "-c", "safe.directory=" + str(checkout), "-C", str(checkout)]
    require(json.loads((ROOT / "oracle/PIN.json").read_bytes())["commit"] == PIN, "pin changed")
    require(subprocess.check_output(git + ["rev-parse", "HEAD"], text=True).strip() in ORACLE_COMMITS, "checkout changed")
    raw = subprocess.check_output(git + ["show", "HEAD:" + path])
    require((checkout / path).read_bytes() == raw, "pinned provenance source modified")
    text = raw.decode("utf-8")
    functions = {}
    for node in ast.parse(text).body:
        if isinstance(node, ast.FunctionDef) and node.name in (
                "_identity_graph", "_verdict", "test_fresh_epoch1_verdict_is_active"):
            segment = "\n".join(text.splitlines()[node.lineno - 1:node.end_lineno])
            functions[node.name] = {"line": node.lineno, "sha256": sha(segment.encode("utf-8"))}
            if node.name == "_identity_graph":
                require(all(s in segment for s in ('generator="x"', '"id": "M"', '"id": "C"',
                        '"ring_vars": ["x"]', '"lhs": "x", "rhs": "0"')), "source identity changed")
            if node.name == "test_fresh_epoch1_verdict_is_active":
                require(node.lineno == 69 and '["current"] is True' in segment, "source test changed")
    require(len(functions) == 3, "source constructors missing")
    return {"commit": PIN, "path": path, "file_sha256": sha(raw), "functions": functions,
            "boundary": "Pinned M:(x), C:x=0 selected identities; native exact Rat replay replaces fabricated predecessor backend metadata. No predecessor execution is claimed."}

def prepared():
    raw = (ROOT / "corpus/must/GP-X164.json").read_bytes()
    require(sha(raw) == CASE_HASH, "X164 bytes changed")
    case = json.loads(raw)
    require(case["id"] == "GP-X164" and case["inputs"] == {}
            and case["expected"]["verdict"] == "ACCEPT", "X164 contract changed")
    registry, events, baseline, fidelity, query = helper.translate(case)
    require(baseline is None and query == 1 and registry["clauses"][0]["generators"] == [helper.POLYNOMIALS["x"]]
            and registry["clauses"][0]["target"] == helper.POLYNOMIALS["x"]
            and registry["receipts"][0]["cofactors"] == [helper.ONE], "reviewed translation changed")
    b = registry["clauses"][0]["binding"]
    require(registry["receipts"][0]["binding"] == b
            and all(e["value"]["binding"] == b for e in events["events"]), "exact bindings lost")
    return case, raw, registry, events, fidelity

def query(claimed=(), open_ids=(7,9)):
    return {"schema_version": 1, "why_not": [1,2], "claimed": list(claimed),
            "links": [{"claim": 1, "obligations": [7,8]}, {"claim": 2, "obligations": [9]}],
            "open_obligations": list(open_ids)}

def scenarios(registry, events):
    rows = []
    both_registry, both = copy.deepcopy(registry), copy.deepcopy(events)
    second = copy.deepcopy(both_registry["receipts"][0])
    second["name"] = "receipt-2"
    both_registry["receipts"].append(second)
    warrant = copy.deepcopy(both["events"][1])
    warrant["value"]["id"] = 11
    warrant["value"]["evidence"]["data"] = "receipt-2"
    both["events"].append(warrant)
    def add(label, reg, wire, supports, held, kind="span", request=None, earned=None):
        rows.append({"label": label, "registry": copy.deepcopy(reg), "wire": copy.deepcopy(wire),
                     "supports": supports, "held": held, "kind": kind,
                     "request": copy.deepcopy(request), "earned": earned})
    add("two_independent_receipts", both_registry, both, [10,11], [1])
    one = copy.deepcopy(both)
    one["events"].append({"kind": "retract", "target": 10})
    add("retract_first_support", both_registry, one, [11], [1])
    neither = copy.deepcopy(one)
    neither["events"].append({"kind": "retract", "target": 11})
    add("retract_both_supports", both_registry, neither, [], [])
    for index, support in ((0,11),(1,10)):
        broken = copy.deepcopy(both_registry)
        broken["receipts"][index]["cofactors"] = [[]]
        add("invalid_cofactor_receipt_" + str(index+1), broken, both, [support], [1])
    for status, attempt_id in (("failed",20),("timeout",21)):
        retry = copy.deepcopy(events)
        attempt = copy.deepcopy(retry["events"][1])
        attempt["value"]["id"] = attempt_id
        attempt["value"]["evidence"] = {"kind": "attempt", "status": status}
        retry["events"].append(attempt)
        add("success_then_" + status, registry, retry, [10], [1])
        only = copy.deepcopy(retry)
        only["events"].pop(1)
        absent = copy.deepcopy(registry)
        absent["receipts"] = []
        add(status + "_only", absent, only, [], [])
    scoped_registry = {"schema_version": 2, "clauses": [
        {"algebra": copy.deepcopy(registry["clauses"][0]), "object": "M", "scope": [0]}],
        "receipts": copy.deepcopy(registry["receipts"])}
    scoped_events = copy.deepcopy(events)
    scoped_events["events"].append({"kind": "declare_claim", "claim": 2})
    add("earned_unclaimed", scoped_registry, scoped_events, [10], [1], "scoped", query(),
        [{"claim": 1, "open_obligations": [7]}])
    add("earned_claimed", scoped_registry, scoped_events, [10], [1], "scoped", query([1]), [])
    add("earned_metadata_only", scoped_registry, scoped_events, [10], [1], "scoped", query([2],[8,9]),
        [{"claim": 1, "open_obligations": [8]}])
    unsupported = copy.deepcopy(scoped_events)
    unsupported["events"].pop(1)
    add("earned_unsupported_control", scoped_registry, unsupported, [], [], "scoped", query(), [])
    return rows

def write_input(label, suffix, value):
    SCRATCH.mkdir(parents=True, exist_ok=True)
    path = SCRATCH / (label + "." + suffix + ".json")
    path.write_bytes((encoded(value) + "\n").encode("utf-8"))
    return path

def native(runner, paths):
    completed = subprocess.run([str(runner), *map(str, paths)], cwd=ROOT,
                               capture_output=True, text=True, encoding="utf-8", check=True)
    return json.loads(completed.stdout)

def custody_expected(wire):
    events = wire["events"]
    currents = sorted({encoded(e["value"]): e["value"] for e in events if e["kind"] == "current"}.values(),
                      key=lambda c: c["claim"])
    warrants = sorted({encoded(e["value"]): e["value"] for e in events if e["kind"] == "warrant"}.values(),
                      key=lambda w: w["id"])
    domain = sorted({e["claim"] for e in events if e["kind"] == "declare_claim"} | {c["claim"] for c in currents})
    retracted = sorted({e["target"] for e in events if e["kind"] == "retract"})
    live = [w["id"] for w in warrants if w["id"] not in retracted and any(
        all(w[k] == c[k] for k in ("claim","version","binding")) for c in currents)]
    snapshot = {"domain": domain, "currents": currents, "warrants": warrants,
                "retracted": retracted, "successors": []}
    return {"status": "OK", "admission": "refuseAll", "resolve_fold_snapshot_equal": True,
            "snapshot": snapshot, "supports": [], "held": [], "live_warrants": live,
            "held_queries": [{"claim": c, "held": False} for c in domain]}

def verify(row, wire, observed, custody):
    expected = custody_expected(wire)
    require(custody == expected, "complete native custody snapshot/binding/liveness mismatch")
    snapshot = custody["snapshot"]
    state = {"status": "OK", "held": row["held"], "supports": row["supports"],
             "domain": snapshot["domain"], "live_warrants": custody["live_warrants"],
             "warrant_count": len(snapshot["warrants"]), "current_count": len(snapshot["currents"]),
             "retracted": snapshot["retracted"], "successors": []}
    if row["kind"] == "span":
        require(observed == state, "native checked span state differs")
    else:
        diagnostics = []
        for claim in (1,2):
            warrants = []
            for w in snapshot["warrants"]:
                if w["claim"] == claim:
                    reasons = [] if w["id"] in state["supports"] else [{"kind": "refused_or_unregistered_evidence"}]
                    warrants.append({"id": w["id"], "supported": w["id"] in state["supports"], "reasons": reasons})
            diagnostics.append({"claim": claim, "held": claim in state["held"], "warrants": warrants})
        require(observed == {"state": state, "release": {"allowed": True, "findings": []},
                             "why_not": diagnostics, "earned": row["earned"]},
                "native earned/why-not/state outputs differ")

def execute(row, label, wire):
    reg_path = write_input(label, "registry", row["registry"])
    event_path = write_input(label, "events", wire)
    paths = [reg_path, event_path]
    if row["request"] is not None:
        paths.append(write_input(label, "queries", row["request"]))
    # Identical event bytes feed checked admission and inert custody introspection.
    observed = native(RUNNERS[row["kind"]], paths)
    custody = native(RUNNERS["lifecycle"], [event_path])
    verify(row, wire, observed, custody)
    return {"native_result": observed, "native_custody_result": custody,
            "inputs": {p.name.split(".")[-2] + "_sha256": sha(p.read_bytes()) for p in paths}}

def run(output):
    protected = [ROOT / p for p in ("oracle/PIN.json","oracle/ROUTES.json","corpus/LAYER-TAGS.json")]
    before = {str(p): p.read_bytes() for p in protected}
    source = source_contract()
    case, raw, registry, events, fidelity = prepared()
    row = next(r for r in json.loads(protected[2].read_bytes())["cases"] if r["id"] == "GP-X164")
    require(row["sha256"] == CASE_HASH and row["primary_layer"] == "kernel", "X164 layer binding changed")
    hashes = {k: sha(p.read_bytes()) for k,p in RUNNERS.items()}
    helper_hash = sha(HELPER.read_bytes())
    results = []
    for scenario in scenarios(registry, events):
        forward = scenario["wire"]["events"]
        orders = {"forward": forward, "reverse": list(reversed(forward)),
                  "forward_duplicates": forward + copy.deepcopy(forward),
                  "reverse_duplicates": list(reversed(forward)) * 2}
        runs = {}
        for order, sequence in orders.items():
            runs[order] = execute(scenario, scenario["label"] + "-" + order,
                                 {"schema_version": 1, "events": sequence})
        require(all(r["native_result"] == runs["forward"]["native_result"]
                    and r["native_custody_result"] == runs["forward"]["native_custody_result"]
                    for r in runs.values()), "event order/duplicate result differs")
        results.append({"label": scenario["label"], "runner": scenario["kind"],
                        "registry": scenario["registry"], "event_contract": scenario["wire"],
                        "caller_metadata": scenario["request"], "runs": runs})
    by_name = {r["label"]: r for r in results}
    reference = by_name["earned_unclaimed"]["runs"]["forward"]["native_result"]["state"]
    require(all(by_name[n]["runs"]["forward"]["native_result"]["state"] == reference
                for n in ("earned_claimed","earned_metadata_only")), "caller metadata changed authority")
    require((ROOT / "corpus/must/GP-X164.json").read_bytes() == raw, "fixture changed")
    require(all(p.read_bytes() == before[str(p)] for p in protected), "protected metadata changed")
    require(source_contract() == source and sha(HELPER.read_bytes()) == helper_hash
            and all(sha(p.read_bytes()) == hashes[k] for k,p in RUNNERS.items()), "source/runner changed")
    report = {"schema": "gp-phase2-checked-lifecycle-supplement/v1",
              "source_fixture": {"id": case["id"], "sha256": sha(raw), "expected": case["expected"],
                                 "sources": case["sources"], "translation_fidelity": fidelity},
              "source_contract": source, "protected_input_hashes": {k: sha(v) for k,v in before.items()},
              "reviewed_adapter_path": str(HELPER), "reviewed_adapter_sha256": helper_hash,
              "adapter_sha256": sha(Path(__file__).read_bytes()),
              "tests_sha256": sha((ROOT / "tests/test_phase2_checked_lifecycle_supplement.py").read_bytes()),
              "executables": {k: {"path": str(p), "sha256": hashes[k]} for k,p in RUNNERS.items()},
              "runner_source_hashes": {p: sha((ROOT / "phase2/lean/GP50" / p).read_bytes())
                  for p in ("Runner.lean","ScopedRunner.lean","LifecycleRunner.lean",
                            "Queries.lean","BoundReplayProofs.lean","BoundReplay.lean",
                            "PolyStub.lean","Runtime.lean","ScopedSpan.lean","SpanDecoder.lean")},
              "distinct_corpus_passes_added": 0, "new_corpus_cases": 0, "component_passes_added": 0,
              "supplemental_scenario_count": len(results), "supplemental_checked_folds": 4*len(results),
              "supplemental_custody_folds": 4*len(results), "g2_pass": False,
              "whole_g2_gate": "open; parent acceptance recorded separately",
              "authority": "Existing native Rat coefficient replay checks x=1*x independently for each registered receipt; no asserted verified flag or synthetic callback.",
              "snapshot_boundary": "Checked runners expose state summaries. The lifecycle runner exposes complete resolved snapshots from the identical event-file bytes under refuseAll; it supplies custody comparison only, never checked support.",
              "scope_boundary": "Scoped runner's object M and finite named context [0] are reproduction plumbing for earned queries, not fields, geometric scopes or new profiles. X164 statement/model/input/version bindings are unchanged.",
              "count_boundary": "Supplemental scenarios remain separate from existing component and corpus counts; X164 is not counted again.",
              "scenarios": results}
    output.write_bytes((json.dumps(report, indent=2) + "\n").encode("utf-8"))
    print(str(len(results)) + " supplemental scenarios, " + str(4*len(results)) +
          " checked folds plus matching custody folds; zero corpus passes added.")
    return report

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "reports/PHASE-2-CHECKED-LIFECYCLE-SUPPLEMENT.json")
    args = parser.parse_args()
    run(args.output)
