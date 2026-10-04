"""Validate campaign cost and friction logs (JSON Lines) against their schemas.

usage: python tools/check-campaign-logs.py <campaign-dir>
Reads <campaign-dir>/cost-log.jsonl and <campaign-dir>/friction-log.jsonl. Every friction entry
must name a task that the cost log has, and every refusal must be classified (post-G3a §3, §4.9).
"""
import json
from pathlib import Path
import sys

import jsonschema

ROOT = Path(__file__).resolve().parents[1]
SCHEMAS = ROOT / "campaigns/schemas"


def entries(path):
    if not path.exists():
        return []
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def check(campaign):
    problems = []
    logs = {}
    for name in ("cost-log", "friction-log"):
        schema = json.loads((SCHEMAS / f"{name}.schema.json").read_text(encoding="utf-8"))
        validator = jsonschema.Draft202012Validator(schema, format_checker=jsonschema.FormatChecker())
        logs[name] = entries(Path(campaign) / f"{name}.jsonl")
        for i, entry in enumerate(logs[name]):
            for error in validator.iter_errors(entry):
                problems.append(f"{name} line {i + 1}: {error.message}")
    tasks = {e.get("task") for e in logs["cost-log"]}
    for i, entry in enumerate(logs["friction-log"]):
        if entry.get("task") not in tasks:
            problems.append(f"friction-log line {i + 1}: task {entry.get('task')!r} has no cost-log entry")
    return problems


def main():
    problems = check(sys.argv[1])
    for p in problems:
        print(p)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
