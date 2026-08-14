"""Deterministic campaign packets and attempt ledgers over proof frontiers.

This is a zone-4 research-operations surface.  It binds exact frontier
observations and evidence-envelope ceilings, but it never grants mathematical
authority or writes a graph event.  Workers return artifacts; this module only
records what was requested, how an attempt was checked, and what should be
shown to a planner or projection.
"""

from __future__ import annotations

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re

from . import frontier_bundle as FRONTIER_BUNDLE


CATALOG_SCHEMA = "campaign-task-catalog/v0"
PACKET_INPUT_SCHEMA = "campaign-packet-input/v0"
PACKET_SCHEMA = "campaign-packet/v0"
PACKET_SET_SCHEMA = "campaign-packet-set/v0"
LEDGER_INPUT_SCHEMA = "campaign-ledger-input/v0"
LEDGER_SCHEMA = "campaign-ledger/v0"
OVERLAY_SCHEMA = "campaign-overlay/v0"
AUTHORITY = "DERIVED_READ_MODEL_ONLY"
GRAPH_EFFECT = "NONE"
DIGEST_ALGO = "sha256-lf-normalized"

MATURITIES = {"PACKETIZED", "DECOMPOSABLE", "UNPACKETIZED", "FOG"}
COST_CLASSES = {"SMALL", "MEDIUM", "LARGE", "SIEGE"}
LIFECYCLES = {"ACTIVE", "COMPLETE", "SUPERSEDED"}
OUTCOMES = {
    "ACCEPTED_ARTIFACT",
    "USEFUL_REFUTATION",
    "CORRECT_REFUSAL",
    "PACKET_DEFECT",
    "WORKER_DEFECT",
    "UNVERIFIABLE_RETURN",
    "PENDING_VERIFICATION",
    "SUPERSEDED",
}
VALUE_CATEGORIES = {
    "FRONTIER_CLOSURE",
    "SCOPE_EXPANSION",
    "PROOF_COMPRESSION",
    "NEGATIVE_THEOREM",
    "UNSAFE_INFERENCE_COUNTEREXAMPLE",
    "IMPROVED_PACKETIZATION",
    "INDEPENDENT_REPLICATION",
    "DEBT_REDUCTION",
    "MAP_REFINEMENT",
}

_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._:-]*$")
_SHA = re.compile(r"^(?:sha256:)?([0-9a-f]{64})$")


class CampaignError(ValueError):
    """A campaign record drifted, widened authority, or became ambiguous."""


def _require(condition, message):
    if not condition:
        raise CampaignError(message)


def _portable(value):
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if isinstance(value, dict):
        return {str(key): _portable(value[key])
                for key in sorted(value, key=lambda item: str(item))}
    if isinstance(value, (list, tuple)):
        return [_portable(item) for item in value]
    if isinstance(value, set):
        return sorted(_portable(item) for item in value)
    return str(value)


def _canonical_bytes(value):
    return json.dumps(_portable(value), sort_keys=True,
                      separators=(",", ":"), ensure_ascii=True).encode("ascii")


def _fingerprint(value):
    return "sha256:" + hashlib.sha256(_canonical_bytes(value)).hexdigest()


def _digest(path):
    payload = Path(path).read_bytes().replace(b"\r\n", b"\n")
    return hashlib.sha256(payload).hexdigest()


def _stable_id(value, label):
    _require(isinstance(value, str) and _ID.fullmatch(value),
             "%s must be a stable semantic id" % label)
    return value


def _string(value, label):
    _require(isinstance(value, str) and value.strip(),
             "%s must be a nonempty string" % label)
    return value


def _string_list(value, label, *, sort=False):
    _require(isinstance(value, list), "%s must be a list" % label)
    _require(all(isinstance(item, str) and item for item in value),
             "%s entries must be nonempty strings" % label)
    _require(len(value) == len(set(value)), "%s contains duplicates" % label)
    result = list(value)
    return sorted(result) if sort else result


def _sha(value, label):
    match = _SHA.fullmatch(value) if isinstance(value, str) else None
    _require(match is not None, "%s must be a SHA-256 digest" % label)
    return match.group(1)


def _root(manifest, manifest_path):
    root_value = manifest.get("root", ".")
    _require(isinstance(root_value, str) and root_value,
             "campaign root must be a nonempty relative path")
    _require(not Path(root_value).is_absolute(),
             "campaign root must be relative to the manifest")
    return (manifest_path.parent / root_value).resolve()


def _bound_path(root, binding, label):
    _require(isinstance(binding, dict), "%s binding must be an object" % label)
    relative = binding.get("path")
    _require(isinstance(relative, str) and relative and
             not Path(relative).is_absolute(),
             "%s path must be relative" % label)
    path = (root / relative).resolve()
    try:
        path.relative_to(root)
    except ValueError:
        raise CampaignError("%s path escapes the campaign root" % label)
    _require(path.is_file(), "%s is absent: %s" % (label, path))
    _require(binding.get("digest_algo") == DIGEST_ALGO,
             "%s must use %s" % (label, DIGEST_ALGO))
    expected = _sha(binding.get("sha256"), "%s sha256" % label)
    _require(_digest(path) == expected, "%s digest changed" % label)
    return path, expected


def _load_json(path, label):
    try:
        return json.loads(Path(path).read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise CampaignError("%s is not JSON: %s" % (label, exc))


def _receipt_document(bundle_manifest_path, receipt_id):
    manifest = _load_json(bundle_manifest_path, "frontier bundle manifest")
    bundle_root = _root(manifest, bundle_manifest_path)
    matches = [item for item in manifest.get("receipts", [])
               if item.get("id") == receipt_id]
    _require(len(matches) == 1,
             "frontier receipt %s is absent or duplicated" % receipt_id)
    path, digest = _bound_path(bundle_root, matches[0],
                               "frontier receipt %s" % receipt_id)
    return _load_json(path, "frontier receipt %s" % receipt_id), digest


def _normalize_source_binding(value, task_id):
    _require(isinstance(value, dict),
             "%s source binding must be an object" % task_id)
    result = {
        "id": _stable_id(value.get("id"), "%s source id" % task_id),
        "path": _string(value.get("path"), "%s source path" % task_id),
        "sha256": "sha256:" + _sha(value.get("sha256"),
                                    "%s source sha256" % task_id),
    }
    if value.get("commit") is not None:
        result["commit"] = _string(value["commit"], "%s source commit" % task_id)
    return result


def _normalize_task(value):
    _require(isinstance(value, dict), "campaign task must be an object")
    task_id = _stable_id(value.get("id"), "task id")
    frontier = value.get("frontier")
    _require(isinstance(frontier, dict), "%s frontier must be an object" % task_id)
    expected = {
        "id": _stable_id(frontier.get("id"), "%s frontier id" % task_id),
        "scope_id": _stable_id(frontier.get("scope_id"),
                               "%s frontier scope_id" % task_id),
        "state": frontier.get("state"),
        "status": _string(frontier.get("status"),
                          "%s frontier status" % task_id),
        "receipt_id": _stable_id(frontier.get("receipt_id"),
                                 "%s frontier receipt_id" % task_id),
    }
    _require(expected["state"] in {"OPEN", "CLOSED"},
             "%s frontier state must be OPEN or CLOSED" % task_id)
    statement = value.get("statement")
    _require(isinstance(statement, dict), "%s statement must be an object" % task_id)
    scope = statement.get("scope")
    _require(isinstance(scope, dict), "%s statement scope must be an object" % task_id)
    normalized_statement = {
        "proposition": _string(statement.get("proposition"),
                               "%s proposition" % task_id),
        "scope": _portable(scope),
    }
    _require(scope.get("id") == expected["scope_id"],
             "%s statement scope disagrees with frontier scope" % task_id)
    _string(scope.get("description"), "%s scope description" % task_id)

    requested = value.get("requested_output")
    _require(isinstance(requested, dict),
             "%s requested_output must be an object" % task_id)
    requested_output = {
        "acceptable_forms": _string_list(
            requested.get("acceptable_forms"),
            "%s acceptable_forms" % task_id, sort=True),
        "must_identify": _string_list(
            requested.get("must_identify"),
            "%s must_identify" % task_id, sort=True),
    }
    _require(requested_output["acceptable_forms"],
             "%s needs at least one acceptable output form" % task_id)

    acceptance = value.get("acceptance")
    _require(isinstance(acceptance, dict),
             "%s acceptance must be an object" % task_id)
    kind = acceptance.get("kind")
    _require(kind in {"NATIVE_REPLAY", "GP_EVIDENCE_CONTRACT"},
             "%s acceptance kind is unknown" % task_id)
    replay = acceptance.get("replay")
    _require(isinstance(replay, dict), "%s replay must be an object" % task_id)
    normalized_acceptance = {
        "kind": kind,
        "replay": {
            "command": _string(replay.get("command"),
                               "%s replay command" % task_id),
            "success": _string(replay.get("success"),
                               "%s replay success" % task_id),
        },
    }
    if kind == "GP_EVIDENCE_CONTRACT":
        normalized_acceptance["contract"] = _stable_id(
            acceptance.get("contract"), "%s evidence contract" % task_id)
    mutations = acceptance.get("required_mutations")
    _require(isinstance(mutations, list) and mutations,
             "%s requires at least one mutation" % task_id)
    normalized_mutations = []
    for mutation in mutations:
        _require(isinstance(mutation, dict),
                 "%s mutation must be an object" % task_id)
        normalized_mutations.append({
            "id": _stable_id(mutation.get("id"),
                             "%s mutation id" % task_id),
            "description": _string(mutation.get("description"),
                                   "%s mutation description" % task_id),
        })
    mutation_ids = [item["id"] for item in normalized_mutations]
    _require(len(mutation_ids) == len(set(mutation_ids)),
             "%s repeats a required mutation" % task_id)
    normalized_acceptance["required_mutations"] = sorted(
        normalized_mutations, key=lambda item: item["id"])

    planning = value.get("planning")
    _require(isinstance(planning, dict), "%s planning must be an object" % task_id)
    maturity = planning.get("maturity")
    cost = planning.get("cost_class")
    lifecycle = planning.get("lifecycle")
    _require(maturity in MATURITIES, "%s maturity is unknown" % task_id)
    _require(cost in COST_CLASSES, "%s cost_class is unknown" % task_id)
    _require(lifecycle in LIFECYCLES, "%s lifecycle is unknown" % task_id)
    normalized_planning = {
        "maturity": maturity,
        "cost_class": cost,
        "lifecycle": lifecycle,
        "downstream": _string_list(planning.get("downstream", []),
                                   "%s downstream" % task_id, sort=True),
        "attack_log": _string_list(planning.get("attack_log", []),
                                   "%s attack_log" % task_id, sort=True),
        "argument": _string(planning.get("argument"),
                            "%s planning argument" % task_id),
    }
    sources = [_normalize_source_binding(item, task_id)
               for item in value.get("source_bindings", [])]
    source_ids = [item["id"] for item in sources]
    _require(sources and len(source_ids) == len(set(source_ids)),
             "%s needs unique source bindings" % task_id)
    sources.sort(key=lambda item: item["id"])
    return {
        "id": task_id,
        "frontier": expected,
        "statement": normalized_statement,
        "source_bindings": sources,
        "requested_output": requested_output,
        "acceptance": normalized_acceptance,
        "planning": normalized_planning,
    }


def _normalize_catalog(value):
    _require(isinstance(value, dict) and value.get("schema") == CATALOG_SCHEMA,
             "unsupported campaign task catalog schema")
    _require(value.get("authority") == AUTHORITY and
             value.get("graph_effect") == GRAPH_EFFECT,
             "campaign task catalog widened authority")
    tasks = [_normalize_task(item) for item in value.get("tasks", [])]
    ids = [item["id"] for item in tasks]
    _require(tasks and len(ids) == len(set(ids)),
             "campaign task ids must be unique")
    tasks.sort(key=lambda item: item["id"])
    return tasks


def _build_packet(task, bundle, bundle_digest, catalog_digest,
                  bundle_manifest_path):
    frontier_id = task["frontier"]["id"]
    matches = [item for item in bundle["items"] if item["id"] == frontier_id]
    _require(len(matches) == 1,
             "%s frontier item is absent or duplicated" % frontier_id)
    observation = matches[0]
    for field in ("scope_id", "state", "status"):
        _require(observation.get(field) == task["frontier"][field],
                 "%s frontier %s drifted" % (task["id"], field))
    receipt_id = task["frontier"]["receipt_id"]
    _require(receipt_id in observation.get("receipts", []),
             "%s frontier receipt does not observe the item" % task["id"])
    receipt, receipt_digest = _receipt_document(bundle_manifest_path, receipt_id)
    envelope = receipt.get("evidence_envelope")
    _require(isinstance(envelope, dict),
             "%s source receipt lacks an evidence envelope" % task["id"])
    boundary = _string(envelope.get("authority_boundary"),
                       "%s authority boundary" % task["id"])
    _require(envelope.get("graph_effect") == GRAPH_EFFECT,
             "%s evidence envelope widened graph effect" % task["id"])
    binding = {
        "bundle": {
            "sha256": "sha256:" + bundle_digest,
            "input_fingerprint": bundle["history"]["input_fingerprint"],
        },
        "observation": deepcopy(observation),
        "source_receipt": {
            "id": receipt_id,
            "sha256": "sha256:" + receipt_digest,
            "input_fingerprint": receipt["history"]["input_fingerprint"],
        },
    }
    body = {
        "schema": PACKET_SCHEMA,
        "authority": AUTHORITY,
        "graph_effect": GRAPH_EFFECT,
        "packet_id": task["id"],
        "frontier_binding": binding,
        "catalog_binding": {"sha256": "sha256:" + catalog_digest},
        "statement": task["statement"],
        "inputs": {"artifacts": task["source_bindings"]},
        "requested_output": task["requested_output"],
        "acceptance": task["acceptance"],
        "authority_ceiling": {
            "source_receipt": receipt_id,
            "boundary": boundary,
            "source_label": receipt.get("source_authority_ceiling"),
        },
        "planning": task["planning"],
    }
    body["history"] = {
        "immutable_inputs": True,
        "input_fingerprint": _fingerprint({"task": task, "binding": binding}),
    }
    body["packet_fingerprint"] = _fingerprint(body)
    return body


def build_packets_path(path, packet_ids=None):
    """Compile a digest-bound packet set from a frontier and task catalog."""
    manifest_path = Path(path).resolve()
    manifest = _load_json(manifest_path, "campaign packet manifest")
    _require(manifest.get("schema") == PACKET_INPUT_SCHEMA,
             "unsupported campaign packet input schema")
    root = _root(manifest, manifest_path)
    bundle_path, bundle_digest = _bound_path(
        root, manifest.get("frontier_bundle"), "frontier bundle")
    catalog_path, catalog_digest = _bound_path(
        root, manifest.get("task_catalog"), "task catalog")
    try:
        bundle = FRONTIER_BUNDLE.build_path(bundle_path)
    except FRONTIER_BUNDLE.FrontierBundleError as exc:
        raise CampaignError("frontier bundle refused: %s" % exc)
    tasks = _normalize_catalog(_load_json(catalog_path, "task catalog"))
    requested = set(packet_ids or manifest.get("packets", []))
    if requested:
        known = {task["id"] for task in tasks}
        _require(requested <= known,
                 "unknown campaign packet ids: %s" %
                 ", ".join(sorted(requested - known)))
        tasks = [task for task in tasks if task["id"] in requested]
    packets = [_build_packet(task, bundle, bundle_digest, catalog_digest,
                             bundle_path) for task in tasks]
    packets.sort(key=lambda item: item["packet_id"])
    result = {
        "schema": PACKET_SET_SCHEMA,
        "authority": AUTHORITY,
        "graph_effect": GRAPH_EFFECT,
        "packets": packets,
        "counts": {"packets": len(packets),
                   "active": sum(item["planning"]["lifecycle"] == "ACTIVE"
                                 for item in packets)},
    }
    result["history"] = {"immutable": True,
                         "input_fingerprint": _fingerprint(packets)}
    return result


def _packet_map(packet_set):
    _require(isinstance(packet_set, dict) and
             packet_set.get("schema") == PACKET_SET_SCHEMA,
             "attempt ledger needs a campaign-packet-set/v0")
    return {packet["packet_id"]: packet for packet in packet_set["packets"]}


def _normalize_artifacts(values, attempt_id):
    _require(isinstance(values, list),
             "%s artifact_bindings must be a list" % attempt_id)
    result = []
    for value in values:
        _require(isinstance(value, dict),
                 "%s artifact binding must be an object" % attempt_id)
        result.append({
            "id": _stable_id(value.get("id"), "%s artifact id" % attempt_id),
            "sha256": "sha256:" + _sha(value.get("sha256"),
                                        "%s artifact sha256" % attempt_id),
        })
    ids = [item["id"] for item in result]
    _require(len(ids) == len(set(ids)), "%s repeats an artifact" % attempt_id)
    return sorted(result, key=lambda item: item["id"])


def _normalize_attempt(value, packets):
    _require(isinstance(value, dict), "campaign attempt must be an object")
    attempt_id = _stable_id(value.get("id"), "attempt id")
    packet_id = _stable_id(value.get("packet_id"), "%s packet_id" % attempt_id)
    _require(packet_id in packets, "%s names an absent packet" % attempt_id)
    outcome = value.get("outcome")
    _require(outcome in OUTCOMES, "%s outcome is unknown" % attempt_id)
    replay = value.get("replay")
    _require(isinstance(replay, dict), "%s replay must be an object" % attempt_id)
    status = replay.get("status")
    _require(status in {"PASS", "FAIL", "NOT_RUN"},
             "%s replay status is unknown" % attempt_id)
    replay_command = _string(replay.get("command"),
                             "%s replay command" % attempt_id)
    _require(replay_command == packets[packet_id]["acceptance"]["replay"]["command"],
             "%s replay command disagrees with the packet" % attempt_id)
    normalized = {
        "id": attempt_id,
        "packet_id": packet_id,
        "packet_fingerprint": packets[packet_id]["packet_fingerprint"],
        "worker_ref": _string(value.get("worker_ref"),
                              "%s worker_ref" % attempt_id),
        "outcome": outcome,
        "summary": _string(value.get("summary"), "%s summary" % attempt_id),
        "artifact_bindings": _normalize_artifacts(
            value.get("artifact_bindings", []), attempt_id),
        "replay": {
            "status": status,
            "command": replay_command,
            "receipt": replay.get("receipt"),
        },
        "refused_mutations": sorted(_string_list(
            value.get("refused_mutations", []),
            "%s refused_mutations" % attempt_id)),
        "value_categories": sorted(_string_list(
            value.get("value_categories", []),
            "%s value_categories" % attempt_id)),
        "successor_packet_ids": sorted(_string_list(
            value.get("successor_packet_ids", []),
            "%s successor_packet_ids" % attempt_id)),
    }
    _require(all(item in VALUE_CATEGORIES
                 for item in normalized["value_categories"]),
             "%s names an unknown value category" % attempt_id)
    _require(all(item in packets for item in normalized["successor_packet_ids"]),
             "%s names an absent successor packet" % attempt_id)
    required = {item["id"] for item in
                packets[packet_id]["acceptance"]["required_mutations"]}
    refused = set(normalized["refused_mutations"])
    _require(refused <= required,
             "%s reports a mutation the packet did not require" % attempt_id)
    checked = outcome in {"ACCEPTED_ARTIFACT", "USEFUL_REFUTATION"}
    if checked:
        _require(status == "PASS" and normalized["artifact_bindings"],
                 "%s checked outcome needs passing replay and artifacts" % attempt_id)
        _require(refused == required,
                 "%s checked outcome did not refuse every required mutation" %
                 attempt_id)
    if outcome == "PENDING_VERIFICATION":
        _require(status == "NOT_RUN" and normalized["artifact_bindings"],
                 "%s pending verification needs an unchecked artifact" % attempt_id)
    if status == "PASS":
        _string(replay.get("receipt"), "%s replay receipt" % attempt_id)
    return normalized


def _load_prior(root, binding):
    path, digest = _bound_path(root, binding, "prior campaign ledger")
    prior = _load_json(path, "prior campaign ledger")
    _require(prior.get("schema") == LEDGER_SCHEMA and
             prior.get("authority") == AUTHORITY and
             prior.get("graph_effect") == GRAPH_EFFECT,
             "prior campaign ledger is not a derived v0 ledger")
    return prior, digest


def build_ledger_path(path):
    """Compile an attempt ledger, optionally proving append-only extension."""
    manifest_path = Path(path).resolve()
    manifest = _load_json(manifest_path, "campaign ledger manifest")
    _require(manifest.get("schema") == LEDGER_INPUT_SCHEMA,
             "unsupported campaign ledger input schema")
    root = _root(manifest, manifest_path)
    packet_path, packet_digest = _bound_path(
        root, manifest.get("packet_manifest"), "campaign packet manifest")
    packet_set = build_packets_path(packet_path)
    packets = _packet_map(packet_set)
    attempts = [_normalize_attempt(value, packets)
                for value in manifest.get("attempts", [])]
    ids = [item["id"] for item in attempts]
    _require(len(ids) == len(set(ids)), "campaign attempt ids must be unique")
    attempts.sort(key=lambda item: item["id"])
    prior_binding = None
    if manifest.get("prior_ledger") is not None:
        prior, prior_digest = _load_prior(root, manifest["prior_ledger"])
        current = {item["id"]: item for item in attempts}
        for old in prior.get("attempts", []):
            _require(current.get(old["id"]) == old,
                     "prior attempt changed or disappeared: %s" % old["id"])
        prior_binding = {"sha256": "sha256:" + prior_digest,
                         "input_fingerprint": prior["history"]["input_fingerprint"]}
    outcome_counts = {name: 0 for name in sorted(OUTCOMES)}
    for attempt in attempts:
        outcome_counts[attempt["outcome"]] += 1
    result = {
        "schema": LEDGER_SCHEMA,
        "authority": AUTHORITY,
        "graph_effect": GRAPH_EFFECT,
        "packet_set": {
            "sha256": "sha256:" + packet_digest,
            "input_fingerprint": packet_set["history"]["input_fingerprint"],
        },
        "attempts": attempts,
        "counts": {
            "attempts": len(attempts),
            "verification_debt": outcome_counts["PENDING_VERIFICATION"],
            "outcomes": outcome_counts,
        },
    }
    if prior_binding is not None:
        result["extends"] = prior_binding
    result["history"] = {"immutable": True,
                         "input_fingerprint": _fingerprint({
                             "packet_set": result["packet_set"],
                             "attempts": attempts,
                             "extends": prior_binding,
                         })}
    return result


def build_overlay(packet_set, ledger):
    """Project maturity, outcomes, and verification debt for a console layer."""
    packets = _packet_map(packet_set)
    _require(isinstance(ledger, dict) and ledger.get("schema") == LEDGER_SCHEMA,
             "campaign overlay needs a campaign-ledger/v0")
    by_packet = {packet_id: [] for packet_id in packets}
    for attempt in ledger.get("attempts", []):
        _require(attempt["packet_id"] in by_packet,
                 "ledger attempt names a packet outside the overlay")
        by_packet[attempt["packet_id"]].append(attempt)
    items = []
    for packet_id, packet in sorted(packets.items()):
        attempts = sorted(by_packet[packet_id], key=lambda item: item["id"])
        debt = sum(item["outcome"] == "PENDING_VERIFICATION"
                   for item in attempts)
        items.append({
            "packet_id": packet_id,
            "packet_fingerprint": packet["packet_fingerprint"],
            "frontier_id": packet["frontier_binding"]["observation"]["id"],
            "frontier_state": packet["frontier_binding"]["observation"]["state"],
            "maturity": packet["planning"]["maturity"],
            "cost_class": packet["planning"]["cost_class"],
            "lifecycle": packet["planning"]["lifecycle"],
            "attempt_ids": [item["id"] for item in attempts],
            "outcomes": [item["outcome"] for item in attempts],
            "verification_debt": debt,
            "downstream": packet["planning"]["downstream"],
            "authority_ceiling": packet["authority_ceiling"],
        })
    result = {
        "schema": OVERLAY_SCHEMA,
        "authority": AUTHORITY,
        "graph_effect": GRAPH_EFFECT,
        "items": items,
        "counts": {"packets": len(items),
                   "active": sum(item["lifecycle"] == "ACTIVE" for item in items),
                   "verification_debt": sum(item["verification_debt"]
                                            for item in items)},
    }
    result["history"] = {"immutable": True,
                         "input_fingerprint": _fingerprint({
                             "packets": packet_set["history"]["input_fingerprint"],
                             "ledger": ledger["history"]["input_fingerprint"],
                         })}
    return result


def _render_packet(packet, audience):
    observation = packet["frontier_binding"]["observation"]
    receipt = packet["frontier_binding"]["source_receipt"]
    artifacts = "\n".join(
        "- `%s`: `%s` at `%s` (%s)" % (
            item["id"], item["path"], item.get("commit", "unversioned"),
            item["sha256"])
        for item in packet["inputs"]["artifacts"])
    mutations = "\n".join("- `%s`: %s" % (item["id"], item["description"])
                            for item in packet["acceptance"]["required_mutations"])
    forms = "\n".join("- `%s`" % item
                      for item in packet["requested_output"]["acceptable_forms"])
    must = "\n".join("- %s" % item
                     for item in packet["requested_output"]["must_identify"])
    prefix = ("Execute this bounded research packet. Return artifacts, not "
              "mathematical authority.\n\n" if audience == "agent" else "")
    return (prefix + "# %s\n\n" % packet["packet_id"] +
            "Packet fingerprint: `%s`\n\n" % packet["packet_fingerprint"] +
            "## Bound frontier and inputs\n\n" +
            "Frontier `%s` is `%s` with status `%s` at scope `%s`.\n\n" % (
                observation["id"], observation["state"],
                observation["status"], observation["scope_id"]) +
            "Bundle: `%s`; source receipt `%s`: `%s`.\n\n" % (
                packet["frontier_binding"]["bundle"]["sha256"],
                receipt["id"], receipt["sha256"]) +
            artifacts + "\n\n" +
            "## Exact obligation\n\n%s\n\n" % packet["statement"]["proposition"] +
            "Scope `%s`: %s\n\n" % (
                packet["statement"]["scope"]["id"],
                packet["statement"]["scope"]["description"]) +
            "## Acceptable outputs\n\n%s\n\n" % forms +
            "Must identify:\n\n%s\n\n" % must +
            "## Replay and refusal controls\n\nRun: `%s`\n\nSuccess: %s\n\n%s\n\n" % (
                packet["acceptance"]["replay"]["command"],
                packet["acceptance"]["replay"]["success"], mutations) +
            "## Authority ceiling\n\n%s\n\n" %
            packet["authority_ceiling"]["boundary"] +
            "Graph effect: `NONE`.\n\n" +
            "## Planning context (advisory)\n\n%s\n\n" %
            packet["planning"]["argument"] +
            "Maturity `%s`; cost `%s`; lifecycle `%s`.\n" % (
                packet["planning"]["maturity"],
                packet["planning"]["cost_class"],
                packet["planning"]["lifecycle"]))


def render_packets(packet_set, audience="human"):
    _require(audience in {"human", "agent"}, "unknown packet audience")
    packets = packet_set.get("packets", [])
    _require(packets, "cannot render an empty packet set")
    return "\n\n---\n\n".join(_render_packet(item, audience)
                                      for item in packets) + "\n"


def canonical_json(value, pretty=True):
    return json.dumps(value, sort_keys=True, indent=2 if pretty else None,
                      separators=None if pretty else (",", ":"),
                      ensure_ascii=True) + "\n"
