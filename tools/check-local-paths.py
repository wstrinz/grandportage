"""Ratchet for local machine paths in tracked files (alpha prerequisite, Will 2026-10-03).

usage: python tools/check-local-paths.py [--update]
Every tracked file outside the private oracle checkouts must be free of absolute local paths
(drive-letter user or repo directories, MSYS /c/Users/...), except the files in
tools/local-paths-allowlist.json, whose occurrence counts may only fall. --update rewrites the
allowlist to the current counts; use it only to record a reduction or a reviewed exception.
"""
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWLIST = ROOT / "tools/local-paths-allowlist.json"
PATTERN = re.compile(rb"[A-Za-z]:(?:/|\\\\?)(?:Users|repos)(?:/|\\\\?)|/c/Users/")
EXCLUDED = ("oracle/checkout/", "oracle/history/checkout/")
# These files carry the patterns as examples or rules.
EXEMPT = {"tools/check-local-paths.py", "tools/local-paths-allowlist.json", "tools/neutralize-local-paths.py",
          "tests/test_gp50_local_paths.py", "reports/LOCAL-PATH-MIGRATION.json"}


def counts():
    tracked = subprocess.run(["git", "ls-files", "-z"], cwd=ROOT, capture_output=True, check=True).stdout
    result = {}
    for raw in tracked.split(b"\0"):
        path = raw.decode("utf-8")
        if not path or path.startswith(EXCLUDED) or path in EXEMPT or path.startswith("reports/LOCAL-PATH-MIGRATION"):
            continue
        try:
            data = (ROOT / path).read_bytes()
        except (FileNotFoundError, IsADirectoryError):
            continue
        n = len(PATTERN.findall(data))
        if n:
            result[path] = n
    return result


def check():
    allowed = json.loads(ALLOWLIST.read_text(encoding="utf-8"))["files"]
    current = counts()
    problems = [f"{p}: {n} local paths, not allowlisted" for p, n in current.items() if p not in allowed]
    problems += [f"{p}: {n} local paths, allowlisted {allowed[p]}" for p, n in current.items()
                 if p in allowed and n > allowed[p]]
    return current, problems


def main():
    if "--update" in sys.argv:
        current = counts()
        ALLOWLIST.write_text(json.dumps({"schema": "gp-local-paths-allowlist/v1",
                                         "policy": "Counts may only fall; the goal is an empty list.",
                                         "files": dict(sorted(current.items()))}, indent=2) + "\n",
                             encoding="utf-8", newline="\n")
        print(f"{len(current)} files, {sum(current.values())} occurrences")
        return 0
    _, problems = check()
    for p in problems:
        print(p)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
