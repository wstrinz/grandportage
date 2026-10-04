"""Three unchanged named-partition fixtures under explicit conditional hypotheses."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import subprocess

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ROOT = Path(__file__).resolve().parents[1]
SCRATCH = ROOT / "tmp/phase2-conditional-partition"
EXE = ROOT / ("phase2/lean/.lake/build/bin/gp_conditional_partition_fixture" + EXE_SUFFIX)
CASES = ("GP-X183", "GP-X184", "GP-X186")
PIN = "ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
SOURCE = "tests/test_adversarial.py"
ANCHORS = {
    "GP-X183": (3149, "test_a_partition_reports_when_it_FAILS_not_only_when_it_succeeds"),
    "GP-X184": (1348, "test_a_case_split_is_licensed_by_the_partition_not_by_an_edge"),
    "GP-X186": (1372, "test_a_case_split_without_exhaustiveness_is_refused"),
}
HASHES = {
    "GP-X183": "ba3e44a5b86e20f60e50a25b3fd0fc9c6aab4c5e93e00bfed9d9f187cdf28c78",
    "GP-X184": "97e0917f7e524cff1db7f2371b952b766f883e03da754ce4fe6b82fbee4d59f6",
    "GP-X186": "6e1ce28a406c4590fe7e17445cccb25d7f5f2c9f4699191064dcee7a1a8e0980",
}
ROUTE = {"kind": "joint_premises", "layer": "conditional_premise_routes",
    "limitation": "Legacy transport/coverage rule under declared premises; not logical entailment or GP 0.50 held authority. Partition verification is explicitly assumed for rule isolation. Whole checker and renderer also execute without an external CAS."}
MODEL = "contexts=[parent,left,right];partition=parent:[left,right]"
AUTHORITY = "test-only-named-partition-assumptions"
STATEMENTS = {1: "left branch is empty", 2: "right branch is empty",
              3: "the parent is empty", 4: "parent is covered by [left,right]"}

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def source_contract():
    checkout = ROOT / "oracle/checkout"
    pin_raw = (ROOT / "oracle/PIN.json").read_bytes()
    require(json.loads(pin_raw)["commit"] == PIN, "source pin changed")
    git = ["git", "-c", "safe.directory=" + str(checkout), "-C", str(checkout)]
    require(subprocess.check_output(git + ["rev-parse", "HEAD"], text=True).strip() in ORACLE_COMMITS,
            "source checkout is not pinned")
    raw = subprocess.check_output(git + ["show", "HEAD:" + SOURCE])
    require((checkout / SOURCE).read_bytes() == raw, "pinned source file changed")
    text = raw.decode("utf-8")
    functions = {}
    for case_id, (line, name) in ANCHORS.items():
        node = next(n for n in ast.parse(text).body if isinstance(n, ast.FunctionDef) and n.name == name)
        require(node.lineno == line, "source anchor moved")
        segment = "\n".join(text.splitlines()[line-1:node.end_lineno])
        needles = {
            "GP-X183": ['"B2" in found[0].detail', '"COVER EVERY BRANCH"'],
            "GP-X184": ['_split(["CE2", "CE3", "C-COVER"])', 'assert ok', '"COVERS"'],
            "GP-X186": ['_split(["CE2", "CE3"])', 'assert not ok', '"COVER"'],
        }[case_id]
        require(all(needle in segment for needle in needles), "named source contract changed")
        functions[case_id] = {"line": line, "anchor": "def " + name + "(",
                              "function_sha256": sha(segment.encode("utf-8"))}
    return {"commit": PIN, "path": SOURCE, "file_sha256": sha(raw),
            "pin_file_sha256": sha(pin_raw), "functions": functions,
            "boundary": "Execute the literal fixture abstraction and its stated conditional conclusion; no predecessor graph reconstruction or renderer claim."}

def checked_case(case_id, tags, routes, baseline):
    require(case_id in CASES, "uncommissioned fixture")
    raw = (ROOT / "corpus/must" / (case_id + ".json")).read_bytes()
    case = json.loads(raw)
    tag = next(row for row in tags["cases"] if row["id"] == case_id)
    prior = next(row for row in baseline["cases"] if row["id"] == case_id)
    require(sha(raw) == HASHES[case_id] == tag["sha256"] == prior["sha256"], "fixture bytes changed")
    require(tag["primary_layer"] == "kernel" and tag["full_contract_required"] is True
            and tag["g2_kernel_eligible"] is True, "layer contract changed")
    require(case["expected"] == prior["expected"], "expectation changed")
    line, name = ANCHORS[case_id]
    require(case["sources"] == [{"repository": "gp-v037", "commit": PIN, "path": SOURCE,
        "line": line, "anchor": "def " + name + "("}], "source pointer changed")
    require(routes["commit"] == PIN and routes["routes"][case_id] == ROUTE, "route changed")
    return case, raw, tag

def execute(raw, label, mode="normal", runner=EXE):
    SCRATCH.mkdir(parents=True, exist_ok=True)
    path = SCRATCH / (label + ".json")
    path.write_bytes(raw)
    completed = subprocess.run([str(runner), str(path), sha(raw), mode], cwd=ROOT,
        capture_output=True, text=True, encoding="utf-8", check=True)
    require(path.read_bytes() == raw, "native input bytes changed")
    return json.loads(completed.stdout), sha(raw)

def binding(source, claim):
    return {"statementHash": STATEMENTS[claim], "scopeHash": source, "modelHash": MODEL,
            "inputHashes": [source], "authority": AUTHORITY, "authorityVersion": 1, "kernelVersion": 1}

def expected_records(case, digest):
    inputs = case["inputs"]
    premises = inputs["premises"]
    records = []
    dependency_ids = []
    for premise in premises:
        require(premise in (
            {"context": "left", "statement_class": "empty", "statement": "left branch is empty"},
            {"context": "right", "statement_class": "empty", "statement": "right branch is empty"}),
            "unsupported premise")
        claim = 1 if premise["context"] == "left" else 2
        wid = claim * 10
        records.append({"id": wid, "claim": claim, "version": 1, "binding": binding(digest, claim),
                        "evidence": {"kind": "receipt", "data": "given:" + premise["statement"]}})
        dependency_ids.append(wid)
    records.append({"id": 40, "claim": 4, "version": 1, "binding": binding(digest, 4),
                    "evidence": {"kind": "receipt", "data": "given:exhaustive parent:[left,right]"}})
    if inputs["cover"]["include_exhaustiveness_premise"]:
        dependency_ids.append(40)
    records.append({"id": 30, "claim": 3, "version": 1, "binding": binding(digest, 3),
                    "evidence": {"kind": "derived", "premises": dependency_ids,
                                 "sideReceipt": "named-partition-composition"}})
    return sorted(records, key=lambda w: w["id"]), dependency_ids

def verify(case, raw, observed):
    digest = sha(raw)
    records, deps = expected_records(case, digest)
    require(observed["conditional"] is True and observed["case"] == case["id"] and
            observed["source_digest"] == digest and observed["literal_inputs"] == case["inputs"] and
            observed["conclusion"] == "the parent is empty", "literal fixture or conditional boundary differs")
    require(observed["argument_dependency_ids"] == deps, "argument dependency list differs")
    given = [premise["statement"] for premise in case["inputs"]["premises"]] + [
        "exhaustive parent:[left,right]"]
    require(observed["given"] == given, "named conditional hypotheses differ")
    ids = [w["id"] for w in records]
    claims = sorted(w["claim"] for w in records)
    currents = [{"claim": w["claim"], "version": w["version"], "binding": w["binding"]}
                for w in sorted(records, key=lambda w: w["claim"])]
    snapshot = {"domain": claims, "currents": currents, "warrants": records,
                "retracted": [], "successors": []}
    require(observed["snapshot"] == snapshot, "complete conditional snapshot differs")
    supported_roots = [w["id"] for w in records if w["id"] != 30]
    closes = deps == [10,20,40] and all(wid in ids for wid in (10,20,40))
    supports = supported_roots + ([30] if closes else [])
    held = sorted([w["claim"] for w in records if w["id"] in supports])
    expected_state = {"status": "OK", "held": held, "supports": supports, "domain": claims,
        "live_warrants": ids, "warrant_count": len(records), "current_count": len(records),
        "retracted": [], "successors": []}
    require(observed["state"] == expected_state, "actual fold/held closure differs")
    return "ACCEPT" if 3 in held else "REFUSE"

def run(output, runner=EXE):
    source = source_contract()
    metadata = {name: (ROOT / path).read_bytes() for name, path in {
        "layer_tags": "corpus/LAYER-TAGS.json", "routes": "oracle/ROUTES.json",
        "baseline": "reports/PHASE-2-BASELINE.json", "pin": "oracle/PIN.json"}.items()}
    tags, routes, baseline = (json.loads(metadata[key]) for key in ("layer_tags", "routes", "baseline"))
    runner_sha = sha(runner.read_bytes())
    rows = []
    for case_id in CASES:
        case, raw, tag = checked_case(case_id, tags, routes, baseline)
        outputs, input_hashes = {}, {}
        for mode in ("normal", "reverse", "duplicates"):
            observed, input_hash = execute(raw, case_id + "-" + mode, mode, runner)
            verdict = verify(case, raw, observed)
            require(verdict == case["expected"]["verdict"], "conditional fixture verdict differs")
            outputs[mode], input_hashes[mode] = observed, input_hash
        require(all({k: v for k, v in result.items() if k != "mode"} ==
                    {k: v for k, v in outputs["normal"].items() if k != "mode"}
                    for result in outputs.values()), "order/duplicate controls differ")
        require((ROOT / "corpus/must" / (case_id + ".json")).read_bytes() == raw, "fixture changed")
        rows.append({"id": case_id, "source_sha256": sha(raw), "expected": case["expected"],
            "sources": case["sources"], "layer_entry": tag, "legacy_route": routes["routes"][case_id],
            "observed": verify(case, raw, outputs["normal"]), "executed": True,
            "full_fixture_contract": True, "conditional_conclusion_only": True,
            "literal_inputs": case["inputs"], "native_results": outputs, "native_input_sha256": input_hashes,
            "theory_hypotheses": outputs["normal"]["given"],
            "translation_fidelity": "Literal parent/left/right region predicates over arbitrary Point types. Only supplied emptiness roots exist; verified coverage is a separate registered root and must appear in the actual argument dependencies."})
    require(source_contract() == source and sha(runner.read_bytes()) == runner_sha, "source/runner changed")
    for name, path in {"layer_tags": "corpus/LAYER-TAGS.json", "routes": "oracle/ROUTES.json",
                      "baseline": "reports/PHASE-2-BASELINE.json", "pin": "oracle/PIN.json"}.items():
        require((ROOT / path).read_bytes() == metadata[name], "registry/baseline/pin changed")
    report = {"schema": "gp-phase2-conditional-partition-slice/v1", "case_count": 3,
        "native_executions": 9, "cases": rows, "source_contract": source,
        "registry_sha256": {name: sha(raw) for name, raw in metadata.items()},
        "runner_path": str(runner), "runner_sha256": runner_sha,
        "adapter_sha256": sha(Path(__file__).read_bytes()),
        "harness_sha256": sha((ROOT / "phase2/lean/Tests/ConditionalPartition.lean").read_bytes()),
        "test_source_sha256": sha((ROOT / "tests/test_phase2_conditional_partition.py").read_bytes()),
        "kernel_source_sha256": {name: sha((ROOT / ("phase2/lean/GP50/" + name + ".lean")).read_bytes())
            for name in ("Events", "Runtime", "Closure", "Decoder", "AdmissionProofs", "SpanSoundnessProofs")},
        "proofs": ["ConditionalPartition.partition_composition_sound",
                   "ConditionalPartition.actual_validator_sound", "ConditionalPartition.actual_fold_held_sound"],
        "axioms": ["propext", "Quot.sound"], "production_profile_adoption": False,
        "underlying_algebraic_truth_certified": False, "g2_pass": False,
        "guarantee": "Every actual held claim has its named meaning for every Point type and every parent/left/right interpretation satisfying precisely the explicit theory hypotheses. Semantic truth alone never seeds closure.",
        "binding_boundary": "Exact literal statement/model identities plus host SHA-256 of the unchanged UTF-8 fixture bind the registered records. Byte-to-digest fidelity is a host contract. Source premise assumptions are conditional theory hypotheses, not certified underlying region emptiness."}
    output.write_bytes((json.dumps(report, indent=2) + "\n").encode("utf-8"))
    print("Conditional partition: 3 unchanged fixtures, 9 native folds; conditional REFUSE/ACCEPT/REFUSE.")
    return report

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "reports/PHASE-2-CONDITIONAL-PARTITION-SLICE.json")
    parser.add_argument("--runner", type=Path, default=EXE)
    args = parser.parse_args()
    run(args.output, args.runner)
