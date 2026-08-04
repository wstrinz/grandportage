"""Fail-closed aggregation of exact-scope ``frontier/v1`` receipts.

Receipts are immutable derived views.  This module does not decide which view
is newer by file order or timestamp: every repeated semantic item needs an
explicit agreement or supersession record in the bundle manifest.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import tempfile


SCHEMA = "frontier-bundle/v1"
INPUT_SCHEMA = "frontier-bundle-input/v1"
AUTHORITY = "DERIVED_READ_MODEL_ONLY"
GRAPH_EFFECT = "NONE"
DIGEST_ALGO = "sha256-lf-normalized"

_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._:-]*$")
_FINGERPRINT = re.compile(r"^sha256:[0-9a-f]{64}$")


class FrontierBundleError(ValueError):
    """A bundle source, overlap, or explicit resolution is inconsistent."""


def _require(condition, message):
    if not condition:
        raise FrontierBundleError(message)


def _stable_id(value, label):
    _require(isinstance(value, str) and _ID.match(value),
             "%s must be a stable semantic id" % label)
    return value


def _portable(value):
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if isinstance(value, dict):
        return {str(key): _portable(value[key])
                for key in sorted(value, key=lambda item: str(item))}
    if isinstance(value, (list, tuple)):
        return [_portable(item) for item in value]
    return str(value)


def _canonical_bytes(value):
    return json.dumps(_portable(value), sort_keys=True, separators=(",", ":"),
                      ensure_ascii=True).encode("ascii")


def _fingerprint(value):
    return "sha256:" + hashlib.sha256(_canonical_bytes(value)).hexdigest()


def _digest(path):
    content = Path(path).read_bytes().replace(b"\r\n", b"\n")
    return hashlib.sha256(content).hexdigest()


def _string_list(value, label):
    _require(isinstance(value, list), "%s must be a list" % label)
    _require(all(isinstance(item, str) and item for item in value),
             "%s entries must be nonempty strings" % label)
    _require(len(value) == len(set(value)),
             "%s contains duplicates" % label)
    return list(value)


def _normalize_observation(value, receipt_id):
    _require(isinstance(value, dict),
             "%s item observation must be an object" % receipt_id)
    item_id = _stable_id(value.get("id"), "%s observation id" % receipt_id)
    scope_id = _stable_id(value.get("scope_id"),
                          "%s %s scope_id" % (receipt_id, item_id))
    state = value.get("state")
    _require(state in {"OPEN", "CLOSED"},
             "%s %s state must be OPEN or CLOSED" % (receipt_id, item_id))
    status = value.get("status")
    _require(isinstance(status, str) and status,
             "%s %s status must be nonempty" % (receipt_id, item_id))
    observation = {"id": item_id, "scope_id": scope_id,
                   "state": state, "status": status}
    if "replacement_ids" in value:
        replacements = sorted(_string_list(
            value["replacement_ids"],
            "%s %s replacement_ids" % (receipt_id, item_id)))
        _require(state == "CLOSED",
                 "%s %s open observation cannot declare replacements" % (
                     receipt_id, item_id))
        _require(item_id not in replacements,
                 "%s %s cannot replace itself" % (receipt_id, item_id))
        observation["replacement_ids"] = replacements
    return observation


def _load_receipts(manifest, manifest_path):
    root_value = manifest.get("root", ".")
    _require(isinstance(root_value, str) and root_value,
             "bundle root must be a nonempty relative path")
    _require(not Path(root_value).is_absolute(),
             "bundle root must be relative to the manifest")
    repository_root = (manifest_path.parent / root_value).resolve()
    records = []
    documents = {}
    bound_paths = set()
    bound_digests = set()
    for source in manifest.get("receipts", []):
        _require(isinstance(source, dict), "receipt binding must be an object")
        receipt_id = _stable_id(source.get("id"), "receipt id")
        _require(receipt_id not in documents, "duplicate receipt id %s" % receipt_id)
        relative = source.get("path")
        _require(isinstance(relative, str) and relative and
                 not Path(relative).is_absolute(),
                 "%s receipt path must be relative" % receipt_id)
        path = (repository_root / relative).resolve()
        try:
            path.relative_to(repository_root)
        except ValueError:
            raise FrontierBundleError(
                "%s receipt escapes the bundle root" % receipt_id)
        _require(path.is_file(), "%s receipt is absent: %s" % (receipt_id, path))
        path_key = str(path).casefold()
        _require(path_key not in bound_paths,
                 "%s duplicates a normalized receipt path" % receipt_id)
        expected = source.get("sha256")
        _require(isinstance(expected, str) and re.fullmatch(r"[0-9a-f]{64}", expected),
                 "%s receipt digest is invalid" % receipt_id)
        _require(source.get("digest_algo") == DIGEST_ALGO,
                 "%s must use %s" % (receipt_id, DIGEST_ALGO))
        actual_digest = _digest(path)
        _require(actual_digest == expected,
                 "%s receipt digest changed" % receipt_id)
        _require(actual_digest not in bound_digests,
                 "%s duplicates receipt content" % receipt_id)
        try:
            document = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            raise FrontierBundleError("%s receipt is not JSON: %s" % (
                receipt_id, exc))
        _require(document.get("authority") == AUTHORITY and
                 document.get("graph_effect") == GRAPH_EFFECT,
                 "%s widened bundle authority" % receipt_id)
        _require(document.get("schema") == "frontier/v1" or
                 document.get("projection_schema") == "frontier/v1",
                 "%s is not a frontier/v1 receipt" % receipt_id)
        history = document.get("history")
        _require(isinstance(history, dict),
                 "%s history must be an object" % receipt_id)
        input_fingerprint = history.get("input_fingerprint")
        _require(isinstance(input_fingerprint, str) and
                 _FINGERPRINT.fullmatch(input_fingerprint),
                 "%s history.input_fingerprint is invalid" % receipt_id)
        observations = [_normalize_observation(item, receipt_id)
                        for item in document.get("item_observations", [])]
        ids = [item["id"] for item in observations]
        _require(observations and len(ids) == len(set(ids)),
                 "%s needs unique item_observations" % receipt_id)
        declared_open = document.get("open_items")
        _require(isinstance(declared_open, list) and
                 set(declared_open) == {item["id"] for item in observations
                                        if item["state"] == "OPEN"},
                 "%s open_items disagrees with item_observations" % receipt_id)
        documents[receipt_id] = observations
        bound_paths.add(path_key)
        bound_digests.add(actual_digest)
        records.append({
            "id": receipt_id,
            "path": relative.replace("\\", "/"),
            "sha256": "sha256:" + expected,
            "digest_algo": DIGEST_ALGO,
            "receipt_schema": document.get("schema"),
            "input_fingerprint": input_fingerprint,
            "item_count": len(observations),
            "open_count": len(declared_open),
        })
    _require(records, "bundle needs at least one receipt")
    records.sort(key=lambda item: item["id"])
    return records, documents


def _normalize_resolutions(values):
    _require(isinstance(values, list), "resolutions must be a list")
    resolutions = []
    for value in values:
        _require(isinstance(value, dict), "resolution must be an object")
        resolution_id = _stable_id(value.get("id"), "resolution id")
        item_id = _stable_id(value.get("item_id"),
                             "%s item_id" % resolution_id)
        mode = value.get("mode")
        _require(mode in {"AGREE_OPEN", "SUPERSEDE"},
                 "%s has unknown mode" % resolution_id)
        scope_id = _stable_id(value.get("scope_id"),
                              "%s scope_id" % resolution_id)
        normalized = {"id": resolution_id, "item_id": item_id,
                      "mode": mode, "scope_id": scope_id}
        if mode == "AGREE_OPEN":
            normalized["receipts"] = sorted(_string_list(
                value.get("receipts"), "%s receipts" % resolution_id))
        else:
            normalized["prior_receipts"] = sorted(_string_list(
                value.get("prior_receipts"),
                "%s prior_receipts" % resolution_id))
            normalized["current_receipt"] = _stable_id(
                value.get("current_receipt"),
                "%s current_receipt" % resolution_id)
            _require(normalized["current_receipt"] not in
                     normalized["prior_receipts"],
                     "%s repeats the current receipt as prior" % resolution_id)
            status = value.get("current_status")
            _require(isinstance(status, str) and status,
                     "%s current_status must be nonempty" % resolution_id)
            normalized["current_status"] = status
            normalized["replacements"] = sorted(_string_list(
                value.get("replacements", []),
                "%s replacements" % resolution_id))
            _require(normalized["replacements"] and
                     item_id not in normalized["replacements"],
                     "%s needs distinct replacement items" % resolution_id)
        reason = value.get("reason")
        _require(isinstance(reason, str) and reason,
                 "%s needs a reason" % resolution_id)
        normalized["reason"] = reason
        resolutions.append(normalized)
    ids = [item["id"] for item in resolutions]
    items = [item["item_id"] for item in resolutions]
    _require(len(ids) == len(set(ids)), "resolution ids must be unique")
    _require(len(items) == len(set(items)),
             "an overlapping item may have only one resolution")
    resolutions.sort(key=lambda item: item["id"])
    return resolutions


def build_path(path):
    """Load, validate, and aggregate one frontier-bundle manifest."""
    manifest_path = Path(path).resolve()
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise FrontierBundleError("bundle manifest is not JSON: %s" % exc)
    _require(manifest.get("schema") == INPUT_SCHEMA,
             "unsupported frontier bundle input schema")
    records, documents = _load_receipts(manifest, manifest_path)
    resolutions = _normalize_resolutions(manifest.get("resolutions", []))

    observations = {}
    for receipt_id, items in documents.items():
        for item in items:
            observations.setdefault(item["id"], {})[receipt_id] = item
    overlaps = {item_id: by_receipt for item_id, by_receipt in observations.items()
                if len(by_receipt) > 1}
    by_item = {item["item_id"]: item for item in resolutions}
    _require(set(by_item) == set(overlaps),
             "every and only overlapping item needs an explicit resolution")

    current_items = []
    for item_id in sorted(observations):
        by_receipt = observations[item_id]
        resolution = by_item.get(item_id)
        if resolution is None:
            receipt_id, observation = next(iter(by_receipt.items()))
            current_items.append({**observation, "receipts": [receipt_id]})
            continue
        scope_ids = {item["scope_id"] for item in by_receipt.values()}
        _require(scope_ids == {resolution["scope_id"]},
                 "%s overlap has incompatible exact scopes" % item_id)
        if resolution["mode"] == "AGREE_OPEN":
            _require(set(resolution["receipts"]) == set(by_receipt),
                     "%s agreement does not name every receipt" % item_id)
            _require(all(item["state"] == "OPEN" for item in by_receipt.values()),
                     "%s AGREE_OPEN includes a closed observation" % item_id)
            statuses = {item["status"] for item in by_receipt.values()}
            _require(len(statuses) == 1,
                     "%s AGREE_OPEN statuses conflict" % item_id)
            current_items.append({
                **next(iter(by_receipt.values())),
                "receipts": sorted(by_receipt),
                "resolution": resolution["id"],
            })
        else:
            expected = (set(resolution["prior_receipts"]) |
                        {resolution["current_receipt"]})
            _require(expected == set(by_receipt),
                     "%s supersession does not name every receipt" % item_id)
            _require(all(by_receipt[receipt]["state"] == "OPEN"
                         for receipt in resolution["prior_receipts"]),
                     "%s supersession prior state is not OPEN" % item_id)
            current = by_receipt[resolution["current_receipt"]]
            _require(current["state"] == "CLOSED" and
                     current["status"] == resolution["current_status"],
                     "%s supersession current status disagrees" % item_id)
            _require(current.get("replacement_ids") ==
                     resolution["replacements"],
                     "%s supersession replacement provenance disagrees" %
                     item_id)
            current_items.append({
                **current,
                "receipts": [resolution["current_receipt"]],
                "supersedes_receipts": resolution["prior_receipts"],
                "resolution": resolution["id"],
                "replacements": resolution["replacements"],
            })

    current_ids = {item["id"] for item in current_items}
    for resolution in resolutions:
        for replacement in resolution.get("replacements", []):
            _require(replacement in current_ids,
                     "%s replacement is absent: %s" % (
                         resolution["id"], replacement))
    open_items = [item["id"] for item in current_items
                  if item["state"] == "OPEN"]
    resolved_items = [item["id"] for item in current_items
                      if item["state"] == "CLOSED"]
    binding = {"receipts": records, "resolutions": resolutions,
               "current_items": current_items}
    return {
        "schema": SCHEMA,
        "authority": AUTHORITY,
        "graph_effect": GRAPH_EFFECT,
        "history": {"immutable": True,
                    "input_fingerprint": _fingerprint(binding)},
        "receipts": records,
        "resolutions": resolutions,
        "items": current_items,
        "open_items": open_items,
        "resolved_items": resolved_items,
        "counts": {"receipts": len(records),
                   "items": len(current_items),
                   "open": len(open_items),
                   "resolved": len(resolved_items),
                   "overlap_resolutions": len(resolutions)},
    }


def review_receipt(report):
    """Return the compact checked-in audit surface for a current bundle."""
    _require(isinstance(report, dict) and report.get("schema") == SCHEMA,
             "bundle review needs a frontier-bundle/v1 report")
    return {
        "schema": "gp-frontier-current-review/v1",
        "projection_schema": report["schema"],
        "authority": report["authority"],
        "graph_effect": report["graph_effect"],
        "history": report["history"],
        "counts": report["counts"],
        "receipts": report["receipts"],
        "resolutions": report["resolutions"],
        "open_items": report["open_items"],
        "resolved_items": report["resolved_items"],
    }


def emit_review_receipt(report, path):
    """Atomically write a digest-bound derived current-bundle review."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = canonical_json(review_receipt(report)).encode("utf-8")
    handle, temporary = tempfile.mkstemp(
        prefix=path.name + ".", suffix=".tmp", dir=str(path.parent))
    try:
        with os.fdopen(handle, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    except BaseException:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise
    return hashlib.sha256(payload.replace(b"\r\n", b"\n")).hexdigest()


def canonical_json(value, pretty=True):
    return json.dumps(value, sort_keys=True, indent=2 if pretty else None,
                      separators=None if pretty else (",", ":"),
                      ensure_ascii=True) + "\n"
