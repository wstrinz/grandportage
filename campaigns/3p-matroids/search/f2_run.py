"""Run a gp command list (one gp call per line; '#' lines are skipped) and record every refusal.

usage: python f2_run.py <commands.txt> [--from N]
Refusals go to search/f2-refusals.jsonl, verbatim, for classification in friction-log.jsonl.
Timings go to search/f2-timing.jsonl.
"""
import datetime
import json
import shlex
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
CAMPAIGN = HERE.parent
ROOT = CAMPAIGN.parents[1]


def now():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def log(name, obj):
    with open(HERE / name, "a", newline="\n", encoding="utf-8") as f:
        f.write(json.dumps(obj) + "\n")


def main():
    lines = [l for l in Path(sys.argv[1]).read_text(encoding="utf-8").splitlines() if l.strip() and not l.startswith("#")]
    start = int(sys.argv[sys.argv.index("--from") + 1]) if "--from" in sys.argv else 0
    for i, line in enumerate(lines[start:], start):
        args = shlex.split(line)
        # receipt and system paths are campaign-relative in the list
        args = [str(CAMPAIGN / x) if x.startswith(("receipts/", "systems/")) else x for x in args]
        cmd = [sys.executable, str(ROOT / "tools/gp.py"), "--campaign", "campaigns/3p-matroids"] + args
        t = time.time()
        r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
        dt = round(time.time() - t, 2)
        out = (r.stdout + r.stderr).strip()
        log("f2-timing.jsonl", {"i": i, "cmd": args[0], "label": args[1] if len(args) > 1 else None, "seconds": dt})
        print(f"[{i}] {dt:6.1f}s {line}\n      {out.splitlines()[-1] if out else ''}", flush=True)
        if r.returncode != 0:
            log("f2-refusals.jsonl", {"at": now(), "i": i, "command": "python tools/gp.py --campaign campaigns/3p-matroids "
                                      + line, "label": args[1] if len(args) > 1 else None, "output": out})
            if "Traceback" in out:
                print("STOP: traceback", flush=True)
                return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
