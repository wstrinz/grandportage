"""Write or verify KERNEL-PIN.json: per-file SHA-256 of the Kernel tier, toolchain and commit.

usage: python tools/kernel-pin.py write | verify
At later gates "kernel unchanged" means `verify` passes, or every change is logged in PROMOTIONS.md.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PACKAGE = ROOT / "phase2/lean"
PIN = ROOT / "KERNEL-PIN.json"


def kernel_modules():
    lake = (PACKAGE / "lakefile.toml").read_text(encoding="utf-8")
    block = lake[lake.index('name = "Kernel"'):]
    block = block[:block.index("[[lean_lib]]")] if "[[lean_lib]]" in block else block
    return sorted(re.findall(r'"(GP50\.\w+)"', block))


def current():
    files = {}
    for module in kernel_modules():
        path = PACKAGE / (module.replace(".", "/") + ".lean")
        files[str(path.relative_to(ROOT)).replace("\\", "/")] = hashlib.sha256(path.read_bytes()).hexdigest()
    toolchain = (PACKAGE / "lean-toolchain").read_text(encoding="utf-8").strip()
    return {"schema": "gp-kernel-pin/v1", "toolchain": toolchain, "module_count": len(files), "files": files}


def write():
    pin = current()
    pin["commit"] = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    pin["note"] = "commit is the parent at pin time; the file hashes are authoritative."
    PIN.write_text(json.dumps(pin, indent=2) + "\n", encoding="utf-8", newline="\n")
    return pin


def verify():
    pinned = json.loads(PIN.read_text(encoding="utf-8"))
    now = current()
    changed = sorted(f for f in set(pinned["files"]) | set(now["files"])
                     if pinned["files"].get(f) != now["files"].get(f))
    return {"unchanged": not changed and pinned["toolchain"] == now["toolchain"],
            "changed": changed, "toolchain_changed": pinned["toolchain"] != now["toolchain"]}


if __name__ == "__main__":
    action = sys.argv[1] if len(sys.argv) > 1 else "verify"
    result = write() if action == "write" else verify()
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if action == "write" or result["unchanged"] else 1)
