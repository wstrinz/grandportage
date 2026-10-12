"""Feed finished search entries to gp while the search workers run (campaign-op).

Each round merges the worker plans (f2-plan-*.json) into f2-plan.json. It then builds commands
for the entries that are ready (a Q point and a field point at every bad prime) and not yet
claimed in the ledger: claims one by one (no fold), then `gp submit-batch`.  Exceptions are left for f2_alg.py and
f2_empty.py.  It stops when the search logs show `--until N` entries and nothing new is ready.

usage: python f2_feed.py --until 360
"""
import glob
import json
import shlex
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
CAMPAIGN = HERE.parent


def merged():
    main = json.loads((HERE / "f2-plan.json").read_text(encoding="utf-8"))
    for f in sorted(glob.glob(str(HERE / "f2-plan-*.json"))):
        try:
            part = json.loads(Path(f).read_text(encoding="utf-8"))
        except ValueError:
            continue  # a worker is mid-write; take it next round
        for k, v in part.items():
            main.setdefault(k, v)
    (HERE / "f2-plan.json").write_bytes((json.dumps(main, indent=1) + "\n").encode("utf-8"))
    return main


def filed():
    labels = set()
    for line in (CAMPAIGN / "ledger.jsonl").read_text(encoding="utf-8").splitlines():
        if line.strip():
            labels.add(json.loads(line).get("label"))
    return labels


GP = [sys.executable, str(CAMPAIGN.parents[1] / "tools/gp.py"), "--campaign", "campaigns/3p-matroids"]
BATCH = 250


def gp(args):
    t = time.time()
    r = subprocess.run(GP + args, cwd=CAMPAIGN.parents[1], capture_output=True, text=True, encoding="utf-8")
    return r, round(time.time() - t, 2)


def log(name, obj):
    with open(HERE / name, "a", newline="\n", encoding="utf-8") as f:
        f.write(json.dumps(obj) + "\n")


def run_batched(text, rnd):
    """Claims are filed one by one (no fold). New src-* premises are submitted singly first, so no
    batch item depends on another; every other receipt goes through `gp submit-batch`."""
    lines = [l for l in text.splitlines() if l.strip() and not l.startswith("#")]
    absolute = lambda x: str(CAMPAIGN / x) if x.startswith(("receipts/", "systems/")) else x
    items = []
    for line in lines:
        args = [absolute(x) for x in shlex.split(line)]
        if args[0] == "claim" or args[1].startswith("src-"):
            r, dt = gp(args)
            if r.returncode:
                log("f2-refusals.jsonl", {"command": line, "output": (r.stdout + r.stderr).strip()})
                return 1
            if args[0] == "submit":
                log("f2-timing.jsonl", {"i": None, "cmd": "submit", "label": args[1], "seconds": dt})
        else:
            items.append({"label": args[1], "receipt": args[2]})
    for k in range(0, len(items), BATCH):
        chunk = items[k:k + BATCH]
        path = HERE / f"batch-{rnd:02d}-{k // BATCH}.json"
        path.write_bytes((json.dumps(chunk, indent=1) + "\n").encode("utf-8"))
        r, dt = gp(["submit-batch", str(path)])
        out = (r.stdout + r.stderr).strip()
        summary = next((l for l in out.splitlines() if l.startswith("batch:")), out.splitlines()[-1] if out else "")
        log("f2-timing.jsonl", {"i": None, "cmd": "submit-batch", "label": path.name, "items": len(chunk), "seconds": dt,
                                "summary": summary})
        with open(HERE / "run-feed.log", "a", encoding="utf-8", newline="\n") as f:
            f.write(out + "\n")
        print(f"  {path.name}: {len(chunk)} items, {dt} s; {summary}", flush=True)
        if r.returncode:
            log("f2-refusals.jsonl", {"command": f"submit-batch {path.name}", "output": out})
            return 1
    return 0


def main():
    until = int(sys.argv[sys.argv.index("--until") + 1])
    rnd = 0
    while True:
        plan, have = merged(), filed()
        ready = [k for k, v in plan.items() if k.startswith("C9") and v["q"] and f"{k}-q" not in have
                 and all(x is not None for x in v["fp"].values())]
        done = sum(open(f, encoding="utf-8").read().count("Q:") for f in glob.glob(str(HERE / "f2-search-*.log")))
        if not ready:
            if done >= until:
                print("feed: search finished and nothing left to file", flush=True)
                return 0
            time.sleep(60)
            continue
        rnd += 1
        cmds = HERE / f"cmds-feed-{rnd:02d}.txt"
        out = subprocess.run([sys.executable, str(HERE / "f2_build.py")] + ready, capture_output=True, text=True,
                             encoding="utf-8", check=True).stdout
        cmds.write_bytes(out.encode("utf-8"))
        print(f"feed round {rnd}: {len(ready)} matroids, {out.count('submit ')} submits", flush=True)
        rc = run_batched(out, rnd)
        if rc:
            print("feed: batch stopped", rc, flush=True)
            return rc


if __name__ == "__main__":
    sys.exit(main())
