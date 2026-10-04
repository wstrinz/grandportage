"""Execute the unchanged A16 fixtures under their explicit conditional premises."""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import subprocess
EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / ("phase2/lean/.lake/build/bin/gp_conditional_cover_fixture" + EXE_SUFFIX)
SCRATCH = ROOT / "tmp/phase2-conditional-cover"
CASES = ("GP-A16-missing", "GP-A16-covered")
PIN = "ac4155787207e2847d248cffed7be871d5dcd577"
ORACLE_COMMITS = {PIN, __import__("json").loads((ROOT / "oracle/PIN.json").read_text(encoding="utf-8-sig")).get("public_commit", PIN)}
def sha(raw):
    return hashlib.sha256(raw).hexdigest()
def execute(raw, label):
    SCRATCH.mkdir(parents=True, exist_ok=True)
    path = SCRATCH / (label + ".json")
    path.write_bytes(raw)
    completed = subprocess.run([str(EXE), str(path), sha(raw)], cwd=ROOT, capture_output=True,
                               text=True, encoding="utf-8", check=True)
    return json.loads(completed.stdout), sha(path.read_bytes())
def source_contract():
    path = "grandportage/kernel.py"
    checkout = ROOT / "oracle/checkout"
    git = ["git", "-c", "safe.directory=" + str(checkout), "-C", str(checkout)]
    assert subprocess.check_output(git + ["rev-parse", "HEAD"], text=True).strip() in ORACLE_COMMITS
    pinned = subprocess.check_output(git + ["show", "HEAD:" + path])
    assert (checkout / path).read_bytes() == pinned
    text = pinned.decode("utf-8")
    node = next(n for n in ast.parse(text).body if isinstance(n, ast.FunctionDef)
                and n.name == "transport_over_partition")
    assert node.lineno == 1252
    block = "\n".join(text.splitlines()[node.lineno-1:node.end_lineno])
    return {"commit": PIN, "path": path, "line": node.lineno,
            "file_sha256": sha(pinned), "function_sha256": sha(block.encode("utf-8")),
            "packet_sha256": sha((ROOT / "docs/GP-0.50-REWORK-PACKET.md").read_bytes())}
def run(output):
    source = source_contract()
    tags = json.loads((ROOT / "corpus/LAYER-TAGS.json").read_bytes())
    baseline = json.loads((ROOT / "reports/PHASE-2-BASELINE.json").read_bytes())
    rows = []
    for case_id in CASES:
        path = ROOT / "corpus/must" / (case_id + ".json")
        raw = path.read_bytes(); case = json.loads(raw)
        tag = next(r for r in tags["cases"] if r["id"] == case_id)
        prior = next(r for r in baseline["cases"] if r["id"] == case_id)
        assert tag["primary_layer"] == "kernel" and sha(raw) == tag["sha256"] == prior["sha256"]
        assert case["expected"] == prior["expected"]
        assert case["inputs"] == {"all_listed_branches_empty": True,
               "checked_exhaustive_cover": case_id == "GP-A16-covered"}
        observed, input_sha = execute(raw, case_id)
        assert observed["conditional"] is True and observed["case"] == case_id
        assert observed["literal_inputs"] == case["inputs"]
        assert observed["source_digest"] == sha(raw)
        verdict = "ACCEPT" if 3 in observed["state"]["held"] else "REFUSE"
        assert verdict == case["expected"]["verdict"]
        assert observed["state"]["supports"] == ([10,20,30] if verdict == "ACCEPT" else [10])
        assert path.read_bytes() == raw
        rows.append({"id": case_id, "source_sha256": sha(raw), "expected": case["expected"],
                     "observed": verdict, "full_fixture_contract": True,
                     "conditional_conclusion_only": True, "native_result": observed,
                     "native_input_sha256": input_sha,
                     "translation_fidelity": "Original parent-emptiness formula and collective listed-branch premise; no concrete parent, branches or points invented. Named premise hypotheses delimit authority."})
    report = {"schema": "gp-phase2-conditional-cover-slice/v1", "case_count": 2, "cases": rows,
              "source_contract": source, "runner_sha256": sha(EXE.read_bytes()),
              "adapter_sha256": sha(Path(__file__).read_bytes()),
              "harness_sha256": sha((ROOT / "phase2/lean/Tests/ConditionalCover.lean").read_bytes()),
              "guarantee": "For every point type and every parent/branch interpretation satisfying the explicitly given premises, held conclusions have their literal stated meaning.",
              "proofs": ["ConditionalCover.actual_validator_sound", "ConditionalCover.actual_fold_held_sound"],
              "axioms": ["propext", "Quot.sound"], "production_profile_adoption": False,
              "underlying_algebraic_truth_certified": False,
              "binding_boundary": "Host SHA-256 binds the complete unchanged UTF-8 fixture to expected warrant input/scope identities. Lean compares that identity; host byte-to-digest fidelity is explicit.", "g2_pass": False}
    output.write_bytes((json.dumps(report, indent=2) + "\n").encode("utf-8"))
    print("Conditional cover: 2 unchanged fixtures passed under their named hypotheses.")
    return report
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "reports/PHASE-2-CONDITIONAL-COVER-SLICE.json")
    run(parser.parse_args().output)
