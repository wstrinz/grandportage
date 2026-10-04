"""Re-check every Kernel module with leanchecker and audit the axioms of every Kernel constant.

usage: python tools/check-kernel-axioms.py [--output reports/PHASE-2.5-KERNEL-AXIOMS.json]
Kernel modules come from the lakefile (via tools/kernel-pin.py). The audit walks every constant
whose defining module is in Kernel, not a curated theorem list, so an unlisted lemma cannot escape.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ELAN_HOME = Path(__import__("os").environ.get("ELAN_HOME") or Path.home() / ".elan")
ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / "phase2/lean"
SCRATCH = ROOT / "tmp/kernel-axioms"
TOOLCHAIN_NAME = (PACKAGE / "lean-toolchain").read_text(encoding="utf-8").strip()
TOOLCHAIN = ELAN_HOME / "toolchains" / TOOLCHAIN_NAME.replace("/", "--").replace(":", "---")
LAKE = TOOLCHAIN / ("bin/lake" + EXE_SUFFIX)
CHECKER = TOOLCHAIN / ("bin/leanchecker" + EXE_SUFFIX)
STANDARD = {"propext", "Quot.sound", "Classical.choice"}

spec = importlib.util.spec_from_file_location("kernel_pin", ROOT / "tools/kernel-pin.py")
pin = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pin)

AUDIT = """import Lean
{imports}
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let kernel : List Name := [{names}]
  let mut rows : Array String := #[]
  for (n, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      if kernel.contains env.header.moduleNames[idx.toNat]! then
        let axs ← Lean.collectAxioms n
        rows := rows.push (toString n ++ "\\t" ++ ",".intercalate (axs.toList.map toString))
  IO.println ("AUDIT-BEGIN\\n" ++ "\\n".intercalate rows.toList ++ "\\nAUDIT-END")
"""


def run(args, env=None):
    p = subprocess.run(list(map(str, args)), cwd=PACKAGE, env=env, capture_output=True, text=True, encoding="utf-8")
    if p.returncode != 0:
        raise SystemExit("command failed: %s\n%s%s" % (args, p.stdout, p.stderr))
    return p.stdout


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output")
    out = parser.parse_args().output
    modules = pin.kernel_modules()
    env = os.environ.copy()
    env["PATH"] = str(TOOLCHAIN / "bin") + os.pathsep + env["PATH"]
    SCRATCH.mkdir(parents=True, exist_ok=True)
    start = time.time()
    run([LAKE, "build", "Kernel"], env)
    checked = {}
    for module in modules:
        log = run([LAKE, "env", CHECKER, module], env)
        checked[module] = hashlib.sha256(log.encode()).hexdigest()
    audit = SCRATCH / "KernelAudit.lean"
    audit.write_text(AUDIT.format(imports="\n".join("import " + m for m in modules),
                                  names=", ".join("`" + m for m in modules)), encoding="utf-8")
    log = run([LAKE, "env", "lean", audit], env)
    body = log.split("AUDIT-BEGIN\n", 1)[1].split("\nAUDIT-END", 1)[0]
    rows = [line.split("\t") for line in body.splitlines() if line]
    usage = {}
    for name, axs in rows:
        for a in filter(None, axs.split(",")):
            usage[a] = usage.get(a, 0) + 1
    nonstandard = sorted(set(usage) - STANDARD)
    result = {
        "schema": "gp-kernel-axioms/v1", "toolchain": TOOLCHAIN_NAME, "module_count": len(modules),
        "leanchecker": {"modules_replayed": len(checked), "all_exit_zero": True},
        "constants_audited": len(rows), "axiom_usage": dict(sorted(usage.items())),
        "axiom_free_constants": sum(1 for _, axs in rows if not axs),
        "nonstandard_axioms": nonstandard, "pass": not nonstandard,
        "elapsed_seconds": round(time.time() - start, 1),
    }
    text = json.dumps(result, indent=2)
    print(text)
    if out:
        Path(out).write_text(text + "\n", encoding="utf-8")
    raise SystemExit(0 if result["pass"] else 1)


if __name__ == "__main__":
    main()
