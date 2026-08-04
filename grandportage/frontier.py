"""Deterministic, read-only proof-frontier projection.

The folded graph and checked evidence remain authoritative.  This module links
already-recorded evidence envelopes into a research-facing frontier without
adding a graph event, relation, claim kind, or verifier verdict.  Premise
updates are overlays: historical input records are fingerprinted and never
rewritten.
"""

from copy import deepcopy
import hashlib
import json
import re


SCHEMA = "frontier/v1"
AUTHORITY = "DERIVED_READ_MODEL_ONLY"
GRAPH_EFFECT = "NONE"

_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._:-]*$")
_REQUIRED_ITEM_FIELDS = {
    "id", "proposition", "status", "scope", "premises",
    "blocked_downstream", "superseding_evidence",
    "smallest_next_artifact", "estimated_cost", "potential_impact",
}


class FrontierError(ValueError):
    """A frontier input is ambiguous, unscoped, or internally inconsistent."""


def _require(condition, message):
    if not condition:
        raise FrontierError(message)


def _portable(value):
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if isinstance(value, dict):
        return {
            str(key): _portable(value[key])
            for key in sorted(value, key=lambda item: str(item))
        }
    if isinstance(value, (list, tuple)):
        return [_portable(item) for item in value]
    if isinstance(value, set):
        return sorted(_portable(item) for item in value)
    return str(value)


def _canonical_bytes(value):
    return json.dumps(
        _portable(value), sort_keys=True, separators=(",", ":"),
        ensure_ascii=True,
    ).encode("ascii")


def _fingerprint(value):
    return "sha256:" + hashlib.sha256(_canonical_bytes(value)).hexdigest()


def _is_open_status(value):
    return (value.startswith("OPEN")
            or ("CONDITIONAL" in value and "UNCONDITIONAL" not in value)
            or value == "UNMATERIALIZED_OPEN")


def _stable_id(value, label):
    _require(isinstance(value, str) and _ID.match(value),
             "%s must be a stable semantic id" % label)
    return value


def _string_list(value, label):
    _require(isinstance(value, list), "%s must be a list" % label)
    _require(all(isinstance(item, str) and item for item in value),
             "%s entries must be nonempty strings" % label)
    _require(len(value) == len(set(value)),
             "%s contains duplicate entries" % label)
    return list(value)


def _normalize_scope(value, item_id):
    _require(isinstance(value, dict), "%s scope must be an object" % item_id)
    scope = _portable(value)
    _stable_id(scope.get("id"), "%s scope.id" % item_id)
    _require(isinstance(scope.get("description"), str)
             and scope["description"],
             "%s scope needs a description" % item_id)
    return scope


def _normalize_premise(value, item_id):
    _require(isinstance(value, dict),
             "%s premise must be an object" % item_id)
    premise = _portable(value)
    _stable_id(premise.get("id"), "%s premise.id" % item_id)
    _require(premise.get("status") in {"OPEN", "DISCHARGED"},
             "%s premise %s has an unknown historical status" % (
                 item_id, premise["id"]))
    return premise


def _normalize_item(value):
    _require(isinstance(value, dict), "frontier item must be an object")
    missing = _REQUIRED_ITEM_FIELDS - set(value)
    _require(not missing, "frontier item is missing: %s" %
             ", ".join(sorted(missing)))
    item = _portable(value)
    item_id = _stable_id(item.get("id"), "item.id")
    _require(isinstance(item.get("proposition"), str)
             and item["proposition"],
             "%s proposition must be nonempty" % item_id)
    _require(isinstance(item.get("status"), str) and item["status"],
             "%s status must be nonempty" % item_id)
    item["scope"] = _normalize_scope(item["scope"], item_id)
    _require(isinstance(item["premises"], list),
             "%s premises must be a list" % item_id)
    item["premises"] = [
        _normalize_premise(premise, item_id)
        for premise in item["premises"]
    ]
    premise_ids = [premise["id"] for premise in item["premises"]]
    _require(len(premise_ids) == len(set(premise_ids)),
             "%s repeats a premise" % item_id)
    for field in ("blocked_downstream", "superseding_evidence",
                  "potential_impact"):
        item[field] = _string_list(item[field], "%s %s" % (item_id, field))
    _require(item["smallest_next_artifact"] is None
             or isinstance(item["smallest_next_artifact"], dict),
             "%s smallest_next_artifact must be an object or null" % item_id)
    _require(item["estimated_cost"] is None
             or isinstance(item["estimated_cost"], dict),
             "%s estimated_cost must be an object or null" % item_id)
    exports = item.get("exports_to_scopes", [])
    item["exports_to_scopes"] = _string_list(
        exports, "%s exports_to_scopes" % item_id)
    if item.get("status_when_premises_discharged") is not None:
        _require(isinstance(item["status_when_premises_discharged"], str)
                 and item["status_when_premises_discharged"],
                 "%s status_when_premises_discharged is invalid" % item_id)
    if item.get("frontier_state") is not None:
        _require(item["frontier_state"] in {"OPEN", "CLOSED"},
                 "%s frontier_state must be OPEN or CLOSED" % item_id)
    return item


def _normalize_discharge(value):
    _require(isinstance(value, dict), "premise discharge must be an object")
    discharge = _portable(value)
    discharge_id = _stable_id(discharge.get("id"), "discharge.id")
    _stable_id(discharge.get("premise_id"),
               "%s premise_id" % discharge_id)
    _require(discharge.get("status") == "DISCHARGED",
             "%s must have status DISCHARGED" % discharge_id)
    discharge["applies_to_scopes"] = _string_list(
        discharge.get("applies_to_scopes"),
        "%s applies_to_scopes" % discharge_id)
    _require(discharge["applies_to_scopes"],
             "%s must name at least one exact scope" % discharge_id)
    discharge["evidence"] = _string_list(
        discharge.get("evidence"), "%s evidence" % discharge_id)
    _require(discharge["evidence"],
             "%s must name its superseding evidence" % discharge_id)
    discharge["does_not_discharge"] = _string_list(
        discharge.get("does_not_discharge", []),
        "%s does_not_discharge" % discharge_id)
    return discharge


def _direct_updates(discharges):
    updates = {}
    for discharge in discharges:
        for scope_id in discharge["applies_to_scopes"]:
            key = (discharge["premise_id"], scope_id)
            _require(key not in updates,
                     "multiple discharges target %s at exact scope %s" % key)
            updates[key] = discharge
    return updates


def _resolve(items, direct):
    """Resolve explicit premise links to a fixed point.

    A closed item propagates only to exact scope ids named in its
    ``exports_to_scopes`` field.  There is deliberately no inferred geometric
    containment or assumption weakening here.
    """
    by_id = {item["id"]: item for item in items}
    effective = {item["id"]: item["status"] for item in items}
    limit = len(items) + 1
    for _step in range(limit):
        changed = False
        for item in items:
            scope_id = item["scope"]["id"]
            resolved = []
            for premise in item["premises"]:
                status = premise["status"]
                if (premise["id"], scope_id) in direct:
                    status = "DISCHARGED"
                source = by_id.get(premise["id"])
                if (source is not None
                        and scope_id in source["exports_to_scopes"]
                        and effective[source["id"]] == "DISCHARGED"):
                    status = "DISCHARGED"
                resolved.append(status)
            target = item["status"]
            if (resolved and all(status == "DISCHARGED" for status in resolved)
                    and item.get("status_when_premises_discharged")):
                target = item["status_when_premises_discharged"]
            if effective[item["id"]] != target:
                effective[item["id"]] = target
                changed = True
        if not changed:
            return effective
    raise FrontierError("premise propagation did not reach a fixed point")


def build(items, discharges=(), sources=()):
    """Compile historical envelopes and scoped premise updates to frontier/v1."""
    historical = [_normalize_item(item) for item in items]
    ids = [item["id"] for item in historical]
    _require(len(ids) == len(set(ids)), "frontier item ids must be unique")
    historical.sort(key=lambda item: item["id"])

    overlays = [_normalize_discharge(item) for item in discharges]
    discharge_ids = [item["id"] for item in overlays]
    _require(len(discharge_ids) == len(set(discharge_ids)),
             "premise discharge ids must be unique")
    overlays.sort(key=lambda item: item["id"])
    direct = _direct_updates(overlays)
    effective_status = _resolve(historical, direct)
    by_id = {item["id"]: item for item in historical}

    projected = []
    changes = []
    for original in historical:
        item = deepcopy(original)
        scope_id = item["scope"]["id"]
        remaining = []
        premise_updates = []
        for premise in item["premises"]:
            historical_status = premise["status"]
            effective = historical_status
            update = direct.get((premise["id"], scope_id))
            resolution = None
            if update is not None:
                effective = "DISCHARGED"
                resolution = {
                    "kind": "SCOPED_PREMISE_DISCHARGE",
                    "by": update["id"],
                    "evidence": list(update["evidence"]),
                }
            source = by_id.get(premise["id"])
            if (source is not None
                    and scope_id in source["exports_to_scopes"]
                    and effective_status[source["id"]] == "DISCHARGED"):
                effective = "DISCHARGED"
                resolution = {
                    "kind": "EXPLICIT_ITEM_LINK",
                    "by": source["id"],
                    "evidence": list(source["superseding_evidence"]),
                }
            premise["effective_status"] = effective
            if resolution is not None:
                premise["resolution"] = resolution
            if effective != "DISCHARGED":
                remaining.append(premise["id"])
            if effective != historical_status:
                premise_updates.append(premise["id"])
        item["historical_status"] = item.pop("status")
        item["effective_status"] = effective_status[item["id"]]
        item["remaining_open_premises"] = remaining
        item["premise_updates"] = premise_updates
        item["status_changed"] = (
            item["historical_status"] != item["effective_status"])
        if item["status_changed"] or premise_updates:
            changes.append({
                "id": item["id"],
                "historical_status": item["historical_status"],
                "effective_status": item["effective_status"],
                "premises_discharged": premise_updates,
                "scope_id": scope_id,
            })
        projected.append(item)

    open_ids = [
        item["id"] for item in projected
        if (item.get("frontier_state") == "OPEN"
            or (item.get("frontier_state") is None
                and _is_open_status(item["effective_status"])))
    ]
    sources = [_portable(source) for source in sources]
    sources.sort(key=lambda source: json.dumps(source, sort_keys=True))
    return {
        "schema": SCHEMA,
        "authority": AUTHORITY,
        "graph_effect": GRAPH_EFFECT,
        "history": {
            "immutable": True,
            "input_fingerprint": _fingerprint(historical),
            "item_count": len(historical),
        },
        "sources": sources,
        "discharges": overlays,
        "items": projected,
        "changes": changes,
        "open_items": open_ids,
        "counts": {
            "items": len(projected),
            "open": len(open_ids),
            "changed": len(changes),
            "premise_discharges": len(overlays),
        },
    }


def build_document(value):
    """Build from a JSON-shaped input document."""
    _require(isinstance(value, dict), "frontier input must be an object")
    _require(value.get("schema") in {None, "frontier-input/v1"},
             "unsupported frontier input schema")
    return build(
        value.get("items", []), value.get("discharges", []),
        value.get("sources", []),
    )


def item_observations(report):
    """Return the minimal exact-scope item surface needed for aggregation."""
    _require(isinstance(report, dict) and report.get("schema") == SCHEMA,
             "item observations need a frontier/v1 report")
    open_ids = report.get("open_items")
    _require(isinstance(open_ids, list) and len(open_ids) == len(set(open_ids)),
             "frontier open_items must be a unique list")
    open_ids = set(open_ids)
    observations = []
    for item in report.get("items", []):
        item_id = _stable_id(item.get("id"), "observation item.id")
        scope = item.get("scope", {})
        scope_id = _stable_id(
            scope.get("id"), "%s observation scope.id" % item_id)
        status = item.get("effective_status")
        _require(isinstance(status, str) and status,
                 "%s observation status is invalid" % item_id)
        observation = {
            "id": item_id,
            "scope_id": scope_id,
            "state": "OPEN" if item_id in open_ids else "CLOSED",
            "status": status,
        }
        if "replacement_ids" in item:
            replacements = _string_list(
                item["replacement_ids"],
                "%s observation replacement_ids" % item_id)
            _require(observation["state"] == "CLOSED",
                     "%s open observation cannot declare replacements" % item_id)
            _require(item_id not in replacements,
                     "%s cannot replace itself" % item_id)
            observation["replacement_ids"] = sorted(replacements)
        observations.append(observation)
    observations.sort(key=lambda item: item["id"])
    _require({item["id"] for item in observations} >= open_ids,
             "frontier open_items names an absent item")
    return observations


def canonical_json(value, pretty=True):
    return json.dumps(
        value, sort_keys=True, indent=2 if pretty else None,
        separators=None if pretty else (",", ":"), ensure_ascii=True,
    ) + "\n"
