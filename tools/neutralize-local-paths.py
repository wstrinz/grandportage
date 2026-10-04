"""Rewrite absolute local machine paths to portable forms and re-bind the SHA-256s that bound them.

usage: python tools/neutralize-local-paths.py [--dry-run] [--receipt reports/LOCAL-PATH-MIGRATION.json]

Path tokens (any separator style, including JSON-escaped backslashes) are rewritten by root:
  <drive>:/repos/grandportage-0.50/X   -> X            (the workspace itself; bare root -> $WORKSPACE)
  <drive>:/repos/OTHER/X               -> $REPOS/OTHER/X
  <drive>:/Users/<user>/dev/X          -> $DEV/X       (predecessor and campaign repositories)
  <drive>:/Users/<user>/.elan/X        -> $ELAN_HOME/X
  <drive>:/Users/<user>/AppData/X      -> $APPDATA/X
  <drive>:/Users/<user>/X, /c/Users/<user>/X -> $HOME/X
Then every 64-hex digest equal to the SHA-256 of a rewritten file's old bytes is replaced by the new
bytes' SHA-256, in every tracked file, until nothing changes. Each run is idempotent. The receipt
records the rules and every old -> new digest. Private oracle checkouts are not touched.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
WORKSPACE = "grandportage-0.50"
EXCLUDED = ("oracle/checkout/", "oracle/history/checkout/")
# These files carry the patterns as examples or rules.
EXEMPT = {"tools/check-local-paths.py", "tools/local-paths-allowlist.json", "tools/neutralize-local-paths.py",
          "tests/test_gp50_local_paths.py", "reports/LOCAL-PATH-MIGRATION.json"}
TOKEN = re.compile(r"(?i)(?:\b[a-z]:(?:\\\\|\\|/)+|/c/)(?:users|repos)(?:\\\\|\\|/)+[^\"'\s,;)\]>`|*<]*")
HEX64 = re.compile(r"\b[0-9a-f]{64}\b")
TRAIL = ".:"  # sentence punctuation that may end a token in prose


def portable(token):
    tail = ""
    while token and token[-1] in TRAIL:
        tail, token = token[-1] + tail, token[:-1]
    p = re.sub(r"[\\/]+", "/", token)
    m = re.match(r"(?i)(?:[a-z]:/|/c/)users/[^/]+(?:/(.*))?$", p)
    if m:
        rest = m.group(1) or ""
        for prefix, name in (("dev", "$DEV"), (".elan", "$ELAN_HOME"), ("appdata", "$APPDATA")):
            if rest.lower() == prefix or rest.lower().startswith(prefix + "/"):
                return name + rest[len(prefix):] + tail
        return "$HOME" + ("/" + rest if rest else "") + tail
    m = re.match(r"(?i)[a-z]:/repos(?:/(.*))?$", p)
    if m:
        rest = m.group(1) or ""
        if rest == WORKSPACE:
            return "$WORKSPACE" + tail
        if rest.startswith(WORKSPACE + "/"):
            return (rest[len(WORKSPACE) + 1:] or ".") + tail
        return "$REPOS" + ("/" + rest if rest else "") + tail
    return token + tail


def rewrite(data):
    text = data.decode("utf-8")
    return TOKEN.sub(lambda m: portable(m.group(0)), text).encode("utf-8")


def tracked():
    out = subprocess.run(["git", "ls-files", "-z"], cwd=ROOT, capture_output=True, check=True).stdout
    return [p for p in out.decode("utf-8").split("\0") if p and not p.startswith(EXCLUDED) and p not in EXEMPT
            and not p.startswith("reports/LOCAL-PATH-MIGRATION")]


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--receipt", default="reports/LOCAL-PATH-MIGRATION.json")
    args = ap.parse_args()
    files = {}
    for p in tracked():
        try:
            files[p] = (ROOT / p).read_bytes()
        except (FileNotFoundError, IsADirectoryError):
            continue
    original = dict(files)
    rewritten = []
    for p, data in files.items():
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError:
            continue  # binary: no text paths to rewrite
        if not TOKEN.search(text):
            continue
        new = rewrite(data)
        if new != data:
            files[p] = new
            rewritten.append(p)
    # Re-bind digests until no file changes.
    rebound = set()
    prev = dict(original)  # bytes as of the digests the tree currently cites
    while True:
        # Map each file's previously cited digest to its current one, so updates chain.
        mapping = {sha(prev[p]): sha(files[p]) for p in files if files[p] != prev[p]}
        if not mapping:
            break
        prev = dict(files)
        changed = False
        for p, data in files.items():
            text = data.decode("utf-8", errors="surrogateescape")
            if not HEX64.search(text):
                continue
            new = HEX64.sub(lambda m: mapping.get(m.group(0), m.group(0)), text).encode("utf-8", errors="surrogateescape")
            if new != data:
                files[p] = new
                rebound.add(p)
                changed = True
        if not changed:
            break
    digests = {p: {"old": sha(original[p]), "new": sha(files[p])} for p in sorted(files) if files[p] != original[p]}
    print(f"rewritten {len(rewritten)} files; re-bound digests in {len(rebound)} files; {len(digests)} files changed")
    if not args.dry_run:
        for p in digests:
            (ROOT / p).write_bytes(files[p])
    receipt = {"schema": "gp-local-path-migration/v1", "rules": __doc__.split("Then every")[0].strip(),
               "rewritten": sorted(rewritten), "rebound": sorted(rebound), "digests": digests}
    Path(args.receipt if Path(args.receipt).is_absolute() else ROOT / args.receipt).write_bytes((json.dumps(receipt, indent=2) + "\n").encode("utf-8"))


if __name__ == "__main__":
    main()
