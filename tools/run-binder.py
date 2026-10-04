"""Run the binder export and write its receipt (G3a review §5c).

usage: python tools/run-binder.py [--out reports/PHASE-3A-BINDER.json]
Builds the binding package, then runs GPBinding/Binder/Export.lean with the binding commit in the
environment. The output's environment block is what the runtime checks before trusting a record.
"""
import os
from pathlib import Path
import subprocess
import sys

EXE_SUFFIX = ".exe" if __import__("os").name == "nt" else ""
ELAN_HOME = Path(__import__("os").environ.get("ELAN_HOME") or Path.home() / ".elan")
ROOT = Path(__file__).resolve().parents[1]
BINDING = ROOT / "binding"
TOOLCHAIN = ELAN_HOME / "toolchains" / (BINDING / "lean-toolchain").read_text(
    encoding="utf-8").strip().replace("/", "--").replace(":", "---")


def main():
    out = Path(sys.argv[sys.argv.index("--out") + 1]) if "--out" in sys.argv else ROOT / "reports/PHASE-3A-BINDER.json"
    commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True,
                            check=True).stdout.strip()
    env = dict(os.environ, PATH=str(TOOLCHAIN / "bin") + os.pathsep + os.environ["PATH"],
               GP_BINDING_COMMIT=commit, XDG_CACHE_HOME=str(BINDING / "cache"),
               MATHLIB_CACHE_DIR=str(BINDING / "cache/mathlib"), TEMP=str(BINDING / "tmp"), TMP=str(BINDING / "tmp"))
    lake = str(TOOLCHAIN / ("bin/lake" + EXE_SUFFIX))
    subprocess.run([lake, "build", "GPBinding"], cwd=BINDING, env=env, check=True, capture_output=True)
    result = subprocess.run([lake, "env", "lean", "GPBinding/Binder/Export.lean"], cwd=BINDING, env=env,
                            check=True, capture_output=True, text=True, encoding="utf-8")
    out.write_text(result.stdout, encoding="utf-8", newline="\n")
    print(out)


if __name__ == "__main__":
    main()
