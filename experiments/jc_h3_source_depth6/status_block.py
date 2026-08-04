#!/usr/bin/env python3
"""Render or refresh the generated GP promotion-firewall status block.

The block is a projection of an aggregate replay ledger.  It deliberately
contains authority and provenance, not a second hand-written account of the
JC mathematics.  Replacement is limited to one exact delimiter pair; missing,
duplicated, reversed, or nested delimiters never trigger a broad rewrite.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import tempfile
from pathlib import Path


HERE = Path(__file__).resolve().parent
BEGIN = "<!-- GP-STATUS-BLOCK:BEGIN schema=gp-status-block/v1 -->"
END = "<!-- GP-STATUS-BLOCK:END -->"
BLOCK_SCHEMA = "gp-status-block/v1"


class StatusBlockError(ValueError):
    """The ledger or exact replacement boundary is malformed."""


def _load_replay():
    path = HERE / "replay_all.py"
    spec = importlib.util.spec_from_file_location(
        "jc_h3_depth6_status_replay", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


REPLAY = _load_replay()


def _require(condition, message):
    if not condition:
        raise StatusBlockError(message)


def status_projection(ledger):
    """Return the deterministic, authority-only status projection."""
    current = REPLAY.normalize_ledger(ledger)
    _require(current.get("overall_verdict") == REPLAY.OVERALL_VERDICT,
             "ledger has not reached the expected explicit-open verdict")
    _require(current.get("aggregate_graph_effect") == "NONE",
             "aggregate ledger widened graph authority")
    frontier = current.get("open_frontier")
    _require(isinstance(frontier, list) and frontier,
             "ledger has no explicit open frontier")

    supported = []
    for stage in current.get("stages", []):
        if stage.get("status") != "VERIFIED":
            continue
        supported.append({
            "stage_id": stage.get("id"),
            "verdict": stage.get("verdict"),
            "graph_effect": stage.get("graph_effect"),
            "licenses": list(stage.get("licenses", [])),
        })

    result = {
        "schema": BLOCK_SCHEMA,
        "ledger_schema": current["schema"],
        "overall_verdict": current["overall_verdict"],
        "authority_ceiling": current.get("authority_ceiling"),
        "aggregate_graph_effect": current["aggregate_graph_effect"],
        "supported": supported,
        "not_supported": list(current.get(
            "first_missing_authority", {}).get("blocks", [])),
        "open_frontier": frontier,
        "bindings": dict(current.get("bindings", {})),
        "binding_digest_algo": current.get("binding_digest_algo"),
        "superseded_by": list(current.get("superseded_by", [])),
    }
    if "migration" in current:
        result["migration"] = current["migration"]
    return result


def render_block(ledger):
    projection = status_projection(ledger)
    payload = json.dumps(projection, indent=2, sort_keys=True)
    return "%s\n```json\n%s\n```\n%s" % (BEGIN, payload, END)


def replace_block(text, block):
    """Replace one exact block, returning ``(new_text, changed)``.

    A file without delimiters is a diagnosed no-op so this helper can be used
    as a safe status hook without claiming ownership of arbitrary Markdown.
    """
    begins = text.count(BEGIN)
    ends = text.count(END)
    if begins == 0 and ends == 0:
        return text, False
    _require(begins == 1 and ends == 1,
             "status delimiters must occur exactly once each")
    start = text.index(BEGIN)
    finish = text.index(END)
    _require(start < finish, "status delimiters are reversed")
    _require(BEGIN not in text[start + len(BEGIN):finish],
             "nested status delimiter refused")
    finish += len(END)
    return text[:start] + block + text[finish:], True


def _atomic_write(path, text):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    handle, temporary = tempfile.mkstemp(
        prefix=path.name + ".", suffix=".tmp", dir=str(path.parent))
    try:
        with os.fdopen(handle, "w", encoding="utf-8", newline="\n") as stream:
            stream.write(text)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    except BaseException:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise


def refresh_file(path, ledger):
    path = Path(path)
    original = path.read_text(encoding="utf-8")
    replacement, changed = replace_block(original, render_block(ledger))
    if changed and replacement != original:
        _atomic_write(path, replacement)
    return {
        "target": str(path),
        "delimiters_found": changed,
        "changed": changed and replacement != original,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ledger", required=True, type=Path)
    parser.add_argument("--target", type=Path,
                        help="refresh the exact delimited block in this file")
    args = parser.parse_args(argv)
    try:
        ledger = json.loads(args.ledger.read_text(encoding="utf-8"))
        if args.target is None:
            print(render_block(ledger))
        else:
            report = refresh_file(args.target, ledger)
            print(json.dumps(report, indent=2, sort_keys=True))
        return 0
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        print(json.dumps({"status": "REFUSED", "error": str(exc)},
                         indent=2, sort_keys=True), file=os.sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
