"""Append-only operational work, deliberately outside the mathematical graph.

Resolving an attempt records an operational decision, never a mathematical
claim. The graph format, verifier inputs, and hook authority do not read this
log. A lock prevents concurrent duplicate IDs and lost resolution checks.
"""
import datetime
import json
import math
import os
import uuid

SCHEMA = "grand-portage-work/v1"
REASONS = ("TIMEOUT", "CAP", "BUDGET")


class WorkError(ValueError):
    pass


def path_for(graph_path):
    directory, name = os.path.split(os.path.abspath(graph_path))
    return os.path.join(directory, "work.jsonl" if name == "graph.jsonl"
                        else name + ".work.jsonl")


def _require(ok, why):
    if not ok:
        raise WorkError(why)


def _text(value, name, limit=256):
    _require(isinstance(value, str) and bool(value.strip()) and len(value) <= limit,
             "%s must be nonblank text of at most %d characters" % (name, limit))


def fold(records, graph):
    ids, attempts, resolved = set(), {}, set()
    for item in records:
        _require(isinstance(item, dict), "work record must be an object")
        status = item.get("disposition")
        common = {"schema", "id", "created_at", "disposition"}
        fields = ({"family", "locus", "reason", "budget"} if status == "UNRESOLVED"
                  else {"resolves", "why"} if status == "RESOLVED" else set())
        _require(bool(fields), "disposition must be UNRESOLVED or RESOLVED")
        _require(set(item) == common | fields, "work fields must be exactly %s"
                 % ", ".join(sorted(common | fields)))
        _require(item["schema"] == SCHEMA, "unsupported work schema")
        _text(item["id"], "id")
        _text(item["created_at"], "created_at")
        try:
            stamp = datetime.datetime.fromisoformat(item["created_at"].replace("Z", "+00:00"))
            _require(stamp.utcoffset() == datetime.timedelta(0), "created_at must be UTC")
        except ValueError as exc:
            raise WorkError("created_at must be an ISO UTC timestamp") from exc
        _require(item["id"] not in ids, "duplicate work id %r" % item["id"])
        ids.add(item["id"])
        if status == "UNRESOLVED":
            _text(item["family"], "family")
            _text(item["locus"], "locus")
            _require(item["family"] in graph.families, "unknown family %r" % item["family"])
            _require(item["reason"] in REASONS, "reason must be TIMEOUT, CAP or BUDGET")
            budget = item["budget"]
            _require(isinstance(budget, dict) and set(budget) == {"value", "unit"},
                     "budget must contain value and unit")
            value = budget["value"]
            _require(type(value) in (int, float) and 0 <= value <= 1e100
                     and math.isfinite(value), "budget value must be finite and nonnegative")
            _text(budget["unit"], "budget unit", 64)
            attempts[item["id"]] = item
        else:
            _text(item["resolves"], "resolves")
            _text(item["why"], "why", 4000)
            _require(item["resolves"] in attempts, "resolution names no preceding attempt")
            _require(item["resolves"] not in resolved, "attempt is already resolved")
            resolved.add(item["resolves"])
    return [item for key, item in attempts.items() if key not in resolved]


def read(path):
    try:
        with open(path, encoding="utf-8") as stream:
            return [json.loads(line) for line in stream if line.strip()]
    except FileNotFoundError:
        return []
    except (OSError, ValueError) as exc:
        raise WorkError("cannot read work log %s: %s" % (path, exc)) from exc


def unresolved(graph_paths, graph):
    result = []
    for path in sorted({path_for(p) for p in graph_paths}):
        result.extend(dict(item, log=path) for item in fold(read(path), graph))
    return sorted(result, key=lambda item: (item["family"], item["locus"],
                                           item["created_at"], item["id"]))


def append(graph_path, graph, payload):
    _require(isinstance(payload, dict), "work input must be an object")
    _require(not ({"schema", "created_at"} & set(payload)),
             "work writer owns schema and created_at")
    item = dict(payload, schema=SCHEMA, created_at=datetime.datetime.now(
        datetime.timezone.utc).isoformat())
    if item.get("disposition") == "UNRESOLVED":
        family = graph.families.get(item.get("family")) if isinstance(item.get("family"), str) else None
        _require(family is not None and not family.get("superseded_by"),
                 "new work must name a live family")
    path = path_for(graph_path)
    lock = path + ".lock"
    try:
        handle = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    except FileExistsError as exc:
        raise WorkError("work log is locked; retry after the writer finishes. "
                        "A lock left by a crashed writer requires explicit recovery: %s" % lock) from exc
    try:
        os.close(handle)
        fold(read(path) + [item], graph)
        separator = ""
        if os.path.exists(path) and os.path.getsize(path):
            with open(path, "rb") as stream:
                stream.seek(-1, os.SEEK_END)
                if stream.read(1) != b"\n":
                    separator = "\n"
        with open(path, "a", encoding="utf-8", newline="\n") as stream:
            stream.write(separator + json.dumps(item, sort_keys=True, allow_nan=False) + "\n")
            stream.flush()
            os.fsync(stream.fileno())
    finally:
        os.unlink(lock)
    return item


def resolution(attempt, why):
    return {"id": "RESOLVE-" + str(uuid.uuid4()), "disposition": "RESOLVED",
            "resolves": attempt, "why": why}
