"""Append schema-shaped entries to the 3P cost / friction logs (LF, one object per line)."""
import json, sys, datetime
from pathlib import Path
D = Path(__file__).resolve().parents[1].as_posix() + "/"  # the campaign directory
def now(): return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
def append(kind, obj):
    with open(D + f"{kind}-log.jsonl", "a", newline="\n") as f: f.write(json.dumps(obj) + "\n")
if __name__ == "__main__":
    append(sys.argv[1], json.loads(sys.stdin.read()))
