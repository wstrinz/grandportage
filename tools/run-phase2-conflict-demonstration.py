"""Ratified test-only faulty-checker alarm and independently checked soundness boundary."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ELAN_HOME = Path(__import__("os").environ.get("ELAN_HOME") or Path.home() / ".elan")
ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / "phase2/lean"
LAKE = (ELAN_HOME/"toolchains"/(ROOT/"phase2/lean/lean-toolchain").read_text(encoding="utf-8").strip().replace("/","--").replace(":","---"))/"bin"/("lake" + EXE_SUFFIX)
EXE = PACKAGE / (".lake/build/bin/gp_conflict_tests" + EXE_SUFFIX)
PROOF = "GP50.ConflictSoundnessProofs"
APPROVAL = "2026-10-01 conflict demonstration ratified: Will directly selected Approve faulty-checker demonstration plus soundness proof."

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def run(output):
    if APPROVAL not in (ROOT / "DECISIONS.md").read_text(encoding="utf-8"):
        raise ValueError("direct conflict-demonstration approval missing")
    env = dict(os.environ, TEMP=str(ROOT / "tmp"), TMP=str(ROOT / "tmp"))
    env["PATH"] = str(LAKE.parent) + os.pathsep + env.get("PATH", "")
    def command(args):
        return subprocess.run(args, cwd=ROOT, env=env, capture_output=True,
                              text=True, encoding="utf-8", check=True).stdout
    paths = [ROOT / "phase2/lean/GP50/ConflictSoundnessProofs.lean",
             ROOT / "phase2/lean/GP50/ConflictProofs.lean",
             ROOT / "phase2/lean/GP50/Conflict.lean",
             ROOT / "phase2/lean/Tests/Conflict.lean"]
    before = {str(p.relative_to(ROOT)): sha(p) for p in paths}
    source = paths[0].read_text(encoding="utf-8")
    if re.search(r"\b(sorry|admit|native_decide|axiom)\b", source):
        raise ValueError("prohibited proof shortcut")
    build = command([str(LAKE), "-d", str(PACKAGE), "build", PROOF, "gp_conflict_tests"])
    checked = {module: command([str(LAKE), "-d", str(PACKAGE), "env", "leanchecker", "-v", module])
               for module in (PROOF, "Tests.Conflict")}
    observed = command([str(EXE)])
    labels = [line.removeprefix("PASS: ") for line in observed.splitlines() if line.startswith("PASS: ")]
    required = {"compromised-checker test holds both before release review",
                "proved inhabited overlap freezes release", "review preserves full claims and supports",
                "finding retains exact support IDs and witness", "unknown overlap does not freeze",
                "unadmitted evidence cannot seed conflict or held"}
    if len(labels) != 15 or not required.issubset(labels) or "Conflict controls: 15 passed" not in observed:
        raise ValueError("native conflict controls incomplete")
    if any(sha(p) != before[str(p.relative_to(ROOT))] for p in paths):
        raise ValueError("source changed during execution")
    report = {"schema": "gp-phase2-conflict-demonstration/v1", "approval": APPROVAL,
              "required_slice_behavior_satisfied": True, "g2_pass": False,
              "authority_boundary": "Deliberately unsound test admission models a faulty checker; it is not admitted production evidence. Actual fold and release review execute. Sound-fold theorem uses explicit BaseValidatorSound contracts and exact registered clause semantics; confirmed alarms imply their assumptions were breached.",
              "no_gate_relaxation": "79 kernel cases and all other G2 obligations remain unchanged.",
              "source_hashes": before, "adapter_sha256": sha(Path(__file__)),
              "executable_sha256": sha(EXE), "kernel_check_results": checked,
              "compiled_proof_sha256": {module: sha(PACKAGE / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")) for module in checked},
              "axioms": ["propext", "Quot.sound"],
              "build_confirmed": "Build completed successfully" in build,
              "native_output": observed, "existing_component_controls_replayed": len(labels),
              "new_component_controls": 0, "new_compiled_proof_controls": 2,
              "new_corpus_cases": 0, "new_corpus_passes": 0}
    output.write_bytes((json.dumps(report, indent=2) + "\n").encode("utf-8"))
    print("Conflict demonstration: 15 existing native alarm controls, two new proof controls, direct approval checked; G2 remains open.")
    return report

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=ROOT / "reports/PHASE-2-CONFLICT-DEMONSTRATION.json")
    run(parser.parse_args().output)
