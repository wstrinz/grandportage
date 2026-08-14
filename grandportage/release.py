"""Content-addressed campaign release planning and safe materialization.

Release plans are derived read models.  They package files and replay
instructions, but neither their coverage verdict nor their archive grants
mathematical or graph authority.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile

from . import dossier as DOSSIER
from . import publication as PUBLICATION


INPUT_SCHEMA = "campaign-release-input/v0"
OUTPUT_SCHEMA = "campaign-release/v0"
AUTHORITY = "DERIVED_READ_MODEL_ONLY"
GRAPH_EFFECT = "NONE"
DIGEST_ALGO = DOSSIER.DIGEST_ALGO

ITEM_KINDS = {"SOURCE", "ARTIFACT"}
PAYLOAD_CLASSES = {
    "SOURCE", "COMPACT_RECEIPT", "REGENERABLE", "HEAVY_DISCOVERY",
    "EXTERNAL",
}
LICENSE_STATUSES = {"CLEAR", "REVIEW", "EXCLUDE"}
REPLAY_CLASSES = {"FAST", "FORMAL", "REPLAY", "EXHAUSTIVE", "EXTERNAL"}
GENERATORS = PUBLICATION.DOCUMENTS - {"FULL_REPORT"} | {"RELEASE_MANIFEST"}
RESOURCE_ROLES = {"CHECKER", "CERTIFICATE", "INPUT", "RECEIPT", "ENVIRONMENT"}
NETWORK_POLICIES = {"FORBIDDEN", "OPTIONAL", "REQUIRED"}
LOAD_BEARING_ROLES = {"CLAIM_SUPPORT", "FORMAL_INTERFACE", "MECHANISM_CEILING"}
LOAD_BEARING_GRADES = {"PROVED", "CHECKED", "CONDITIONAL"}
RESERVED_PATHS = {"manifest.json", "replay.md", "sha256sums"}


class ReleaseError(ValueError):
    """A release plan is ambiguous, unsafe, stale, or not materializable."""


def _require(condition, message):
    if not condition:
        raise ReleaseError(message)


def _string(value, label):
    _require(isinstance(value, str) and value.strip(),
             "%s must be a nonempty string" % label)
    return value


def _id(value, label):
    try:
        return DOSSIER._stable_id(value, label)
    except DOSSIER.DossierError as exc:
        raise ReleaseError(str(exc)) from exc


def _sha(value, label):
    try:
        return DOSSIER._sha(value, label)
    except DOSSIER.DossierError as exc:
        raise ReleaseError(str(exc)) from exc


def _relative(value, label, *, reserved=False):
    _require(isinstance(value, str) and value, "%s must be a path" % label)
    path = Path(value)
    _require(not path.is_absolute(), "%s must be relative" % label)
    _require(".." not in path.parts, "%s must not escape its root" % label)
    normalized = path.as_posix()
    _require(normalized not in {"", "."}, "%s must name a file" % label)
    _require(".git" not in {part.lower() for part in path.parts},
             "%s cannot package git metadata" % label)
    if reserved:
        _require(normalized.lower() not in RESERVED_PATHS,
                 "%s is reserved for generated release metadata" % label)
    return normalized


def _string_list(value, label, *, allow_empty=True, preserve=False):
    _require(isinstance(value, list), "%s must be a list" % label)
    _require(all(isinstance(item, str) and item for item in value),
             "%s entries must be nonempty strings" % label)
    _require(len(value) == len(set(value)), "%s contains duplicates" % label)
    _require(allow_empty or value, "%s must not be empty" % label)
    return list(value) if preserve else sorted(value)


def _digest(path):
    payload = Path(path).read_bytes().replace(b"\r\n", b"\n")
    return hashlib.sha256(payload).hexdigest()


def _canonical_bytes(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=True).encode("ascii")


def _fingerprint(value):
    return "sha256:" + hashlib.sha256(_canonical_bytes(value)).hexdigest()


def _manifest_root(manifest_path, root_value):
    manifest_path = Path(manifest_path).resolve()
    root_value = root_value or "."
    _require(isinstance(root_value, str) and root_value,
             "release root must be a relative path")
    root_path = Path(root_value)
    _require(not root_path.is_absolute(), "release root must be relative")
    return (manifest_path.parent / root_path).resolve()


def _inside(root, relative, label):
    target = (root / relative).resolve()
    try:
        target.relative_to(root)
    except ValueError as exc:
        raise ReleaseError("%s escapes the release root" % label) from exc
    return target


def _normalize_item(value, known):
    _require(isinstance(value, dict), "release item must be an object")
    item_id = _id(value.get("id"), "release item id")
    _require(item_id in known, "%s is not a dossier source or artifact" % item_id)
    kind = value.get("kind")
    _require(kind in ITEM_KINDS, "%s item kind is unknown" % item_id)
    _require(kind == known[item_id]["kind"],
             "%s is %s, not %s" % (item_id, known[item_id]["kind"], kind))
    payload_class = value.get("payload_class")
    license_status = value.get("license_status")
    _require(payload_class in PAYLOAD_CLASSES,
             "%s payload class is unknown" % item_id)
    _require(license_status in LICENSE_STATUSES,
             "%s license status is unknown" % item_id)
    return {
        "id": item_id,
        "kind": kind,
        "release_path": _relative(value.get("release_path"),
                                  "%s release_path" % item_id, reserved=True),
        "payload_class": payload_class,
        "license_status": license_status,
        "provenance": _string(value.get("provenance"),
                              "%s provenance" % item_id),
    }


def _normalize_resource(value):
    _require(isinstance(value, dict), "replay resource must be an object")
    resource_id = _id(value.get("id"), "replay resource id")
    role = value.get("role")
    _require(role in RESOURCE_ROLES,
             "%s resource role is unknown" % resource_id)
    license_status = value.get("license_status")
    _require(license_status in LICENSE_STATUSES,
             "%s license status is unknown" % resource_id)
    _require(value.get("digest_algo") == DIGEST_ALGO,
             "%s must use %s" % (resource_id, DIGEST_ALGO))
    embedded = value.get("embedded_text")
    if embedded is not None:
        _require(isinstance(embedded, str) and embedded,
                 "%s embedded_text must be nonempty" % resource_id)
        _require(value.get("source_path") is None,
                 "%s embedded resource cannot bind source_path" % resource_id)
        source_path = None
        origin = "EMBEDDED"
    else:
        source_path = _relative(value.get("source_path"),
                                "%s source_path" % resource_id)
        origin = "SOURCE"
    result = {
        "id": resource_id,
        "role": role,
        "origin": origin,
        "source_path": source_path,
        "release_path": _relative(value.get("release_path"),
                                  "%s release_path" % resource_id,
                                  reserved=True),
        "digest_algo": DIGEST_ALGO,
        "sha256": "sha256:" + _sha(value.get("sha256"),
                                     "%s sha256" % resource_id),
        "license_status": license_status,
        "provenance": _string(value.get("provenance"),
                              "%s provenance" % resource_id),
    }
    if embedded is not None:
        _require(hashlib.sha256(embedded.encode("utf-8")).hexdigest() ==
                 result["sha256"].removeprefix("sha256:"),
                 "%s embedded_text digest changed" % resource_id)
        result["embedded_text"] = embedded
    return result


def _load_resource_manifest(binding, root):
    _require(isinstance(binding, dict),
             "replay resource manifest binding must be an object")
    _require(binding.get("digest_algo") == DIGEST_ALGO,
             "replay resource manifest must use %s" % DIGEST_ALGO)
    relative = _relative(binding.get("path"), "replay resource manifest path")
    path = _inside(root, relative, "replay resource manifest path")
    _require(path.is_file(), "replay resource manifest does not exist: %s" % path)
    expected = _sha(binding.get("sha256"), "replay resource manifest sha256")
    _require(_digest(path) == expected, "replay resource manifest digest changed")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ReleaseError("replay resource manifest is not JSON: %s" % exc) from exc
    _require(value.get("schema") == "campaign-replay-resources/v0",
             "unsupported replay resource manifest schema")
    _require(value.get("authority") == AUTHORITY and
             value.get("graph_effect") == GRAPH_EFFECT,
             "replay resource manifest widened authority")
    resources = value.get("resources", [])
    _require(isinstance(resources, list),
             "replay resource manifest resources must be a list")
    sets = value.get("sets", [])
    _require(isinstance(sets, list),
             "replay resource manifest sets must be a list")
    return relative, expected, resources, sets


def _normalize_environment(value, lane_id):
    _require(isinstance(value, dict),
             "%s environment must be an object" % lane_id)
    network = value.get("network")
    _require(network in NETWORK_POLICIES,
             "%s network policy is unknown" % lane_id)
    return {
        "runtime": _string(value.get("runtime"), "%s runtime" % lane_id),
        "external_dependencies": _string_list(
            value.get("external_dependencies", []),
            "%s external_dependencies" % lane_id),
        "network": network,
        "notes": _string_list(value.get("notes", []), "%s notes" % lane_id,
                              preserve=True),
    }


def _normalize_lane(value, artifact_ids, selected_ids, resource_ids,
                    resource_sets):
    _require(isinstance(value, dict), "replay lane must be an object")
    lane_id = _id(value.get("id"), "replay lane id")
    lane_class = value.get("class")
    _require(lane_class in REPLAY_CLASSES,
             "%s replay class is unknown" % lane_id)
    commands = _string_list(value.get("commands", []),
                            "%s commands" % lane_id,
                            allow_empty=False, preserve=True)
    ids = _string_list(value.get("artifact_ids", []),
                       "%s artifact_ids" % lane_id, allow_empty=False)
    unknown = sorted(set(ids) - artifact_ids)
    _require(not unknown, "%s names unknown artifacts: %s" %
             (lane_id, ", ".join(unknown)))
    set_ids = _string_list(value.get("resource_set_ids", []),
                           "%s resource_set_ids" % lane_id)
    unknown_sets = sorted(set(set_ids) - set(resource_sets))
    _require(not unknown_sets, "%s names unknown resource sets: %s" %
             (lane_id, ", ".join(unknown_sets)))
    resources = _string_list(value.get("resource_ids", []),
                             "%s resource_ids" % lane_id)
    resources = sorted(set(resources) | {
        resource_id for set_id in set_ids for resource_id in resource_sets[set_id]})
    _require(resources, "%s must bind replay resources" % lane_id)
    unknown_resources = sorted(set(resources) - resource_ids)
    _require(not unknown_resources, "%s names unknown resources: %s" %
             (lane_id, ", ".join(unknown_resources)))
    receipts = _string_list(value.get("receipt_ids", []),
                            "%s receipt_ids" % lane_id, allow_empty=False)
    _require(set(receipts) <= set(resources),
             "%s receipts must also be lane resources" % lane_id)
    _require(set(ids) <= selected_ids,
             "%s names unselected artifact payloads" % lane_id)
    return {
        "id": lane_id,
        "class": lane_class,
        "title": _string(value.get("title"), "%s title" % lane_id),
        "working_directory": _relative(
            value.get("working_directory"), "%s working_directory" % lane_id),
        "environment": _normalize_environment(value.get("environment"), lane_id),
        "commands": commands,
        "artifact_ids": ids,
        "resource_ids": resources,
        "resource_set_ids": set_ids,
        "receipt_ids": receipts,
    }


def _normalize_generated(value, known):
    _require(isinstance(value, dict), "generated artifact must be an object")
    artifact_id = _id(value.get("id"), "generated artifact id")
    _require(artifact_id in known and known[artifact_id]["kind"] == "ARTIFACT",
             "%s is not a dossier artifact" % artifact_id)
    record = known[artifact_id]
    generator = value.get("generator")
    _require(generator in GENERATORS,
             "%s generator is unknown" % artifact_id)
    _require(record["availability"] == "MISSING" and
             record["role"] == "PUBLICATION",
             "%s is not a missing publication placeholder" % artifact_id)
    _require(record.get("generated_by") == generator,
             "%s dossier contract does not permit %s" %
             (artifact_id, generator))
    release_path = value.get("release_path")
    if generator == "RELEASE_MANIFEST":
        _require(release_path == "manifest.json",
                 "%s release manifest path must be manifest.json" % artifact_id)
    else:
        release_path = _relative(release_path,
                                 "%s release_path" % artifact_id,
                                 reserved=True)
    license_status = value.get("license_status")
    _require(license_status in LICENSE_STATUSES,
             "%s license status is unknown" % artifact_id)
    return {
        "id": artifact_id,
        "generator": generator,
        "release_path": release_path,
        "license_status": license_status,
        "public_disposition": record["public_disposition"],
        "provenance": _string(value.get("provenance"),
                              "%s provenance" % artifact_id),
    }


def _known_records(dossier):
    known = {}
    for source in dossier["source"]["canonical_sources"]:
        known[source["id"]] = {**source, "kind": "SOURCE",
                                "availability": "PRESENT",
                                "public_disposition": "INCLUDE"}
    for artifact in dossier["artifacts"]:
        known[artifact["id"]] = {**artifact, "kind": "ARTIFACT"}
    return known


def _required_records(profile, dossier):
    claims = {item["id"]: item for item in dossier["claims"]}
    leaves = {item["id"]: item for item in dossier["leaves"]}
    required = set()
    reasons = {}

    def add(record_id, reason):
        required.add(record_id)
        reasons.setdefault(record_id, set()).add(reason)

    # A release cannot be replayed from a portrait alone.  Its canonical
    # authority sources are an unconditional archival dependency, even when a
    # permissive policy profile does not itself include SOURCE_FRESH.
    for source in dossier["source"]["canonical_sources"]:
        add(source["id"], "DOSSIER_CANONICAL_SOURCE")

    for criterion in profile["criteria"]:
        kind = criterion["kind"]
        if kind == "SOURCE_FRESH":
            for source in dossier["source"]["canonical_sources"]:
                add(source["id"], criterion["id"])
        elif kind == "CLAIMS_PRESENT":
            for claim_id in criterion["claim_ids"]:
                for evidence_id in claims[claim_id]["evidence_ids"]:
                    add(evidence_id, "%s via %s" % (criterion["id"], claim_id))
        elif kind in {"LEAVES_PRICED", "LEAVES_CLOSED"}:
            for leaf_id in criterion["leaf_ids"]:
                leaf = leaves[leaf_id]
                for evidence_id in leaf["evidence_ids"]:
                    add(evidence_id, "%s via %s" % (criterion["id"], leaf_id))
                for retired in leaf["retired_representations"]:
                    for evidence_id in retired["evidence_ids"]:
                        add(evidence_id, "%s via %s/%s" %
                            (criterion["id"], leaf_id, retired["id"]))
        elif kind in {"ARTIFACTS_PRESENT", "ARTIFACT_REPLAY_PASS"}:
            for artifact_id in criterion["artifact_ids"]:
                add(artifact_id, criterion["id"])
    return sorted(required), {
        item: sorted(reasons[item]) for item in sorted(reasons)
    }


def _project_profile(profile, provided_ids):
    criteria = []
    for original in profile["criteria"]:
        criterion = dict(original)
        blockers = list(original["blockers"])
        if original["kind"] == "ARTIFACTS_PRESENT":
            blockers = [blocker for blocker in blockers
                        if not any(blocker == "%s is missing" % artifact_id
                                   for artifact_id in provided_ids)]
        criterion["blockers"] = blockers
        criterion["passed"] = not blockers
        criteria.append(criterion)
    return {
        "id": profile["id"],
        "kind": profile["kind"],
        "title": profile["title"],
        "original_status": profile["status"],
        "status": "READY" if all(item["passed"] for item in criteria)
                  else "NOT_READY",
        "criteria": criteria,
        "counts": {
            "criteria": len(criteria),
            "passed": sum(item["passed"] for item in criteria),
            "blocked": sum(not item["passed"] for item in criteria),
            "blockers": sum(len(item["blockers"]) for item in criteria),
        },
    }


def _block(code, detail, record_id=None):
    result = {"code": code, "detail": detail}
    if record_id is not None:
        result["record_id"] = record_id
    return result


def build(value, *, manifest_path, source_root=None):
    """Compile one release plan against an exact dossier binding."""
    _require(isinstance(value, dict) and value.get("schema") == INPUT_SCHEMA,
             "unsupported campaign release input schema")
    _require(value.get("authority") == AUTHORITY and
             value.get("graph_effect") == GRAPH_EFFECT,
             "campaign release widened authority")
    manifest_path = Path(manifest_path).resolve()
    root = _manifest_root(manifest_path, value.get("root", "."))
    binding = value.get("dossier")
    _require(isinstance(binding, dict), "release dossier binding must be an object")
    _require(binding.get("digest_algo") == DIGEST_ALGO,
             "release dossier binding must use %s" % DIGEST_ALGO)
    dossier_path = _inside(root, _relative(binding.get("path"), "dossier path"),
                           "dossier path")
    expected_dossier_digest = _sha(binding.get("sha256"), "dossier sha256")
    _require(dossier_path.is_file(), "bound dossier does not exist: %s" % dossier_path)
    observed_dossier_digest = _digest(dossier_path)
    _require(observed_dossier_digest == expected_dossier_digest,
             "bound dossier digest changed")
    try:
        dossier = DOSSIER.build_path(dossier_path, source_root=source_root)
    except DOSSIER.DossierError as exc:
        raise ReleaseError(str(exc)) from exc

    profiles = {item["id"]: item for item in dossier["profiles"]}
    profile_id = _id(value.get("profile_id"), "release profile_id")
    _require(profile_id in profiles, "release profile_id is absent from dossier")
    profile = profiles[profile_id]
    known = _known_records(dossier)

    package = value.get("package")
    _require(isinstance(package, dict), "release package must be an object")
    package = {
        "id": _id(package.get("id"), "package id"),
        "title": _string(package.get("title"), "package title"),
        "version": _string(package.get("version"), "package version"),
    }

    _require("provides_artifact_ids" not in value,
             "provides_artifact_ids is replaced by bound generated_artifacts")
    generated = [_normalize_generated(item, known)
                 for item in value.get("generated_artifacts", [])]
    generated_ids = [item["id"] for item in generated]
    _require(len(generated_ids) == len(set(generated_ids)),
             "generated artifact ids must be unique")
    generated_paths = [item["release_path"].lower() for item in generated]
    _require(len(generated_paths) == len(set(generated_paths)),
             "generated artifact paths must be portably unique")
    generated = sorted(generated, key=lambda item: item["id"])
    provided_ids = sorted(generated_ids)

    items = [_normalize_item(item, known) for item in value.get("items", [])]
    item_ids = [item["id"] for item in items]
    _require(len(item_ids) == len(set(item_ids)), "release item ids must be unique")
    release_paths = [item["release_path"].lower() for item in items]
    _require(len(release_paths) == len(set(release_paths)),
             "release paths must be portably unique")
    items = sorted(items, key=lambda item: item["id"])
    collisions = sorted(set(release_paths) & set(generated_paths))
    _require(not collisions, "selected and generated release paths collide")

    resource_manifest_bindings = []
    resource_values = list(value.get("replay_resources", []))
    resource_set_values = []
    for binding_value in value.get("replay_resource_manifests", []):
        relative, digest, loaded, loaded_sets = _load_resource_manifest(
            binding_value, root)
        resource_manifest_bindings.append({
            "path": relative, "digest_algo": DIGEST_ALGO,
            "sha256": "sha256:" + digest,
        })
        resource_values.extend(loaded)
        resource_set_values.extend(loaded_sets)
    resources = [_normalize_resource(item) for item in resource_values]
    resource_ids_list = [item["id"] for item in resources]
    _require(len(resource_ids_list) == len(set(resource_ids_list)),
             "replay resource ids must be unique")
    _require(not (set(resource_ids_list) & set(item_ids)),
             "replay resource ids collide with release item ids")
    resource_paths = [item["release_path"].lower() for item in resources]
    _require(len(resource_paths) == len(set(resource_paths)),
             "replay resource paths must be portably unique")
    _require(not (set(resource_paths) &
                  (set(release_paths) | set(generated_paths))),
             "replay resource paths collide with release payload paths")
    resources = sorted(resources, key=lambda item: item["id"])
    resource_ids = set(resource_ids_list)
    resource_sets = {}
    for value_set in resource_set_values:
        _require(isinstance(value_set, dict),
                 "replay resource set must be an object")
        set_id = _id(value_set.get("id"), "replay resource set id")
        _require(set_id not in resource_sets,
                 "replay resource set ids must be unique")
        members = _string_list(value_set.get("resource_ids", []),
                               "%s resource_ids" % set_id, allow_empty=False)
        unknown = sorted(set(members) - resource_ids)
        _require(not unknown, "%s names unknown resources: %s" %
                 (set_id, ", ".join(unknown)))
        resource_sets[set_id] = members

    artifact_ids = {item["id"] for item in dossier["artifacts"]}
    lanes = [_normalize_lane(lane, artifact_ids, set(item_ids), resource_ids,
                             resource_sets)
             for lane in value.get("replay_lanes", [])]
    lane_ids = [lane["id"] for lane in lanes]
    _require(len(lane_ids) == len(set(lane_ids)), "replay lane ids must be unique")
    lanes = sorted(lanes, key=lambda lane: lane["id"])
    resources_by_id = {item["id"]: item for item in resources}
    for lane in lanes:
        bad_receipts = [resource_id for resource_id in lane["receipt_ids"]
                        if resources_by_id[resource_id]["role"] != "RECEIPT"]
        _require(not bad_receipts,
                 "%s receipt_ids name non-receipts: %s" %
                 (lane["id"], ", ".join(bad_receipts)))
        prefix = lane["working_directory"].rstrip("/") + "/"
        outside = [resource_id for resource_id in lane["resource_ids"]
                   if not (resources_by_id[resource_id]["release_path"] ==
                           lane["working_directory"] or
                           resources_by_id[resource_id]["release_path"].startswith(prefix))]
        _require(not outside,
                 "%s resources must live under its working directory: %s" %
                 (lane["id"], ", ".join(outside)))
    unused_resources = sorted(resource_ids - {
        resource_id for lane in lanes for resource_id in lane["resource_ids"]})
    _require(not unused_resources, "replay resources are unused: %s" %
             ", ".join(unused_resources))

    required, reasons = _required_records(profile, dossier)
    selected = sorted(set(item_ids) | set(provided_ids))
    missing_coverage = sorted(set(required) - set(selected))
    projected = _project_profile(profile, set(provided_ids))

    audit_files = {item["id"]: item
                   for item in dossier["source"]["audit"]["files"]}
    inventory = []
    blockers = []
    for item in items:
        record = known[item["id"]]
        file_audit = audit_files.get(item["id"], {})
        availability = record.get("availability", "PRESENT")
        file_status = file_audit.get("status", "UNCHECKED")
        inventory_item = {
            **item,
            "source_path": record.get("path"),
            "digest_algo": record.get("digest_algo"),
            "sha256": record.get("sha256"),
            "availability": availability,
            "file_status": file_status,
            "public_disposition": record.get("public_disposition", "INCLUDE"),
        }
        inventory.append(inventory_item)
        if availability != "PRESENT":
            blockers.append(_block("ITEM_MISSING",
                                   "%s has no source payload" % item["id"], item["id"]))
        if file_status != "MATCH":
            blockers.append(_block("ITEM_NOT_AUDITED",
                                   "%s file status is %s" %
                                   (item["id"], file_status), item["id"]))
        if item["license_status"] != "CLEAR":
            blockers.append(_block("LICENSE_DEBT",
                                   "%s license is %s" %
                                   (item["id"], item["license_status"]), item["id"]))
        disposition = record.get("public_disposition", "INCLUDE")
        if disposition != "INCLUDE":
            blockers.append(_block("PUBLICATION_DEBT",
                                   "%s public disposition is %s" %
                                   (item["id"], disposition), item["id"]))

    resource_inventory = []
    source_root_path = Path(source_root).resolve() if source_root is not None else None
    for resource in resources:
        if resource["origin"] == "EMBEDDED":
            file_status = "MATCH"
        elif source_root_path is None:
            file_status = "UNCHECKED"
        else:
            resource_path = _inside(source_root_path, resource["source_path"],
                                    "%s source path" % resource["id"])
            if not resource_path.is_file():
                file_status = "MISSING"
            elif _digest(resource_path) != resource["sha256"].removeprefix("sha256:"):
                file_status = "DIGEST_MISMATCH"
            else:
                file_status = "MATCH"
        resource_item = {**resource, "file_status": file_status}
        resource_inventory.append(resource_item)
        if file_status != "MATCH":
            blockers.append(_block(
                "REPLAY_RESOURCE_NOT_AUDITED",
                "%s file status is %s" % (resource["id"], file_status),
                resource["id"]))
        if resource["license_status"] != "CLEAR":
            blockers.append(_block(
                "LICENSE_DEBT", "%s license is %s" %
                (resource["id"], resource["license_status"]), resource["id"]))

    for record_id in missing_coverage:
        blockers.append(_block("COVERAGE_MISSING",
                               "%s is required by the selected profile" % record_id,
                               record_id))
    for criterion in projected["criteria"]:
        for detail in criterion["blockers"]:
            blockers.append(_block("PROFILE_BLOCKED",
                                   "%s: %s" % (criterion["id"], detail)))
    source_status = dossier["source"]["audit"]["status"]
    if source_status != "CURRENT_CLEAN":
        blockers.append(_block("SOURCE_NOT_CLEAN",
                               "source audit is %s" % source_status))
    for item in generated:
        if item["license_status"] != "CLEAR":
            blockers.append(_block("LICENSE_DEBT",
                                   "%s generated license is %s" %
                                   (item["id"], item["license_status"]),
                                   item["id"]))
        if item["public_disposition"] != "INCLUDE":
            blockers.append(_block(
                "PUBLICATION_DEBT",
                "%s generated public disposition is %s" %
                (item["id"], item["public_disposition"]), item["id"]))

    selected_artifacts = sorted(set(item_ids) & artifact_ids)
    replay_debt = []
    for artifact_id in selected_artifacts:
        artifact = known[artifact_id]
        if not (artifact["role"] in LOAD_BEARING_ROLES and
                artifact["grade"] in LOAD_BEARING_GRADES):
            continue
        replay = artifact["replay"]
        if replay["status"] == "NOT_APPLICABLE":
            continue
        covering = [lane for lane in lanes if artifact_id in lane["artifact_ids"]]
        if replay["status"] != "PASS":
            detail = "%s replay is %s" % (artifact_id, replay["status"])
        elif not covering:
            detail = "%s has no replay lane" % artifact_id
        elif not any(replay["command"] in lane["commands"] for lane in covering):
            detail = "%s replay command is absent from its lanes" % artifact_id
        else:
            continue
        replay_debt.append({"artifact_id": artifact_id, "detail": detail})
        blockers.append(_block("REPLAY_DEBT", detail, artifact_id))

    blockers = sorted(blockers, key=lambda item: (
        item["code"], item.get("record_id", ""), item["detail"]))
    license_debt = [item for item in blockers if item["code"] == "LICENSE_DEBT"]
    publication_debt = [item for item in blockers
                        if item["code"] == "PUBLICATION_DEBT"]
    # A replay kit carries every selected source payload.  Lanes name the
    # load-bearing artifacts they verify, while other selected payloads may be
    # inputs reached by those checkers (the synthetic authority file is the
    # minimal example).
    replay_artifact_ids = set(item_ids)
    replay_resource_ids = {
        resource_id for lane in lanes for resource_id in lane["resource_ids"]
    }
    replay_blockers = []
    if not lanes:
        replay_blockers.append(_block(
            "REPLAY_KIT_EMPTY", "release declares no replay lanes"))
    for blocker in blockers:
        record_id = blocker.get("record_id")
        if blocker["code"] == "SOURCE_NOT_CLEAN":
            replay_blockers.append(blocker)
        elif blocker["code"] == "REPLAY_DEBT":
            replay_blockers.append(blocker)
        elif record_id in replay_artifact_ids and blocker["code"] in {
                "ITEM_MISSING", "ITEM_NOT_AUDITED", "LICENSE_DEBT",
                "PUBLICATION_DEBT"}:
            replay_blockers.append(blocker)
        elif record_id in replay_resource_ids and blocker["code"] in {
                "REPLAY_RESOURCE_NOT_AUDITED", "LICENSE_DEBT"}:
            replay_blockers.append(blocker)
    replay_blockers = sorted(replay_blockers, key=lambda item: (
        item["code"], item.get("record_id", ""), item["detail"]))
    portable_audit = dict(dossier["source"]["audit"])
    portable_audit["root"] = "." if source_root is not None else None
    publication = PUBLICATION.build(
        dossier, package=package, profile=projected,
        coverage={
            "required_ids": required,
            "selected_ids": selected,
            "missing_ids": missing_coverage,
            "reasons": reasons,
        },
        inventory=inventory, replay_lanes=lanes, blockers=blockers,
        generated_artifact_ids=provided_ids)
    generated_output = []
    for item in generated:
        digest = None
        if item["generator"] != "RELEASE_MANIFEST":
            digest = "sha256:" + hashlib.sha256(
                PUBLICATION.render(publication, item["generator"])
                .encode("utf-8")).hexdigest()
        generated_output.append({**item, "digest_algo": DIGEST_ALGO,
                                 "sha256": digest})

    body = {
        "schema": OUTPUT_SCHEMA,
        "authority": AUTHORITY,
        "graph_effect": GRAPH_EFFECT,
        "package": package,
        "dossier": {
            "path": binding["path"],
            "digest_algo": DIGEST_ALGO,
            "sha256": "sha256:" + observed_dossier_digest,
            "input_fingerprint": dossier["history"]["input_fingerprint"],
        },
        "source_audit": portable_audit,
        "profile": projected,
        "provides_artifact_ids": provided_ids,
        "generated_artifacts": generated_output,
        "coverage": {
            "required_ids": required,
            "selected_ids": selected,
            "missing_ids": missing_coverage,
            "reasons": reasons,
        },
        "inventory": inventory,
        "replay_resources": resource_inventory,
        "replay_resource_manifests": sorted(
            resource_manifest_bindings, key=lambda item: item["path"]),
        "replay_lanes": lanes,
        "replay_debt": replay_debt,
        "license_debt": license_debt,
        "publication_debt": publication_debt,
        "publication": publication,
        "blockers": blockers,
        "materializable": not blockers,
        "replay_blockers": replay_blockers,
        "replay_materializable": not replay_blockers,
        "counts": {
            "required": len(required),
            "selected": len(selected),
            "inventory": len(inventory),
            "replay_resources": len(resource_inventory),
            "generated_artifacts": len(generated_output),
            "missing_coverage": len(missing_coverage),
            "replay_debt": len(replay_debt),
            "license_debt": len(license_debt),
            "publication_debt": len(publication_debt),
            "blockers": len(blockers),
            "replay_blockers": len(replay_blockers),
        },
    }
    body["history"] = {
        "immutable_inputs": True,
        "plan_fingerprint": _fingerprint(body),
    }
    return body


def build_path(path, source_root=None):
    path = Path(path)
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ReleaseError("campaign release is not JSON: %s" % exc) from exc
    return build(value, manifest_path=path, source_root=source_root)


def _replay_markdown(release):
    lines = ["# Replay lanes", "",
             "Generated from `%s`." % release["history"]["plan_fingerprint"], ""]
    for lane in release["replay_lanes"]:
        lines.extend(["## %s (`%s`)" % (lane["title"], lane["class"]), ""])
        lines.append("Working directory: `%s`." % lane["working_directory"])
        lines.append("Runtime: `%s`; network: `%s`." % (
            lane["environment"]["runtime"], lane["environment"]["network"]))
        if lane["environment"]["external_dependencies"]:
            lines.append("External dependencies: %s." % ", ".join(
                "`%s`" % item
                for item in lane["environment"]["external_dependencies"]))
        lines.append("Receipts: %s." % ", ".join(
            "`%s`" % item for item in lane["receipt_ids"]))
        lines.append("")
        for command in lane["commands"]:
            lines.append("- `%s`" % command)
        lines.append("")
    return "\n".join(lines)


def _materialize(release, source_root, output_dir, *, replay_only):
    """Atomically write a full release or replay kit into a new directory."""
    _require(isinstance(release, dict) and release.get("schema") == OUTPUT_SCHEMA,
             "materializer needs a campaign-release/v0")
    readiness_key = "replay_materializable" if replay_only else "materializable"
    refusal = ("replay kit has blockers and cannot be materialized" if replay_only
               else "release has blockers and cannot be materialized")
    _require(release.get(readiness_key), refusal)
    source_root = Path(source_root).resolve()
    _require(source_root.is_dir(), "source root is not a directory")
    head, head_error = DOSSIER._git(source_root, "rev-parse", "HEAD")
    status, status_error = DOSSIER._git(
        source_root, "status", "--porcelain", "--untracked-files=all")
    _require(not head_error and head and
             head.startswith(release["source_audit"]["expected_commit"]),
             "source commit changed after planning")
    _require(not status_error and not (status or "").splitlines(),
             "source tree changed after planning")
    output_dir = Path(output_dir).resolve()
    _require(not output_dir.exists(), "output directory already exists")
    output_dir.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=".gp-release-", dir=output_dir.parent))
    try:
        checksums = []
        inventory = release["inventory"]
        generated = [] if replay_only else release["generated_artifacts"]
        for item in inventory:
            source = _inside(source_root, item["source_path"],
                             "%s source path" % item["id"])
            _require(source.is_file(), "%s source payload is missing" % item["id"])
            observed = _digest(source)
            expected = item["sha256"].removeprefix("sha256:")
            _require(observed == expected,
                     "%s source payload changed after planning" % item["id"])
            target = _inside(staging, item["release_path"],
                             "%s release path" % item["id"])
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
            checksums.append((observed, item["release_path"]))

        for item in release["replay_resources"]:
            if item["origin"] == "EMBEDDED":
                payload = item["embedded_text"]
                observed = hashlib.sha256(payload.encode("utf-8")).hexdigest()
            else:
                source = _inside(source_root, item["source_path"],
                                 "%s source path" % item["id"])
                _require(source.is_file(), "%s replay resource is missing" % item["id"])
                observed = _digest(source)
            expected = item["sha256"].removeprefix("sha256:")
            _require(observed == expected,
                     "%s replay resource changed after planning" % item["id"])
            target = _inside(staging, item["release_path"],
                             "%s release path" % item["id"])
            target.parent.mkdir(parents=True, exist_ok=True)
            if item["origin"] == "EMBEDDED":
                target.write_text(item["embedded_text"], encoding="utf-8",
                                  newline="\n")
            else:
                shutil.copyfile(source, target)
            checksums.append((observed, item["release_path"]))

        for item in generated:
            if item["generator"] == "RELEASE_MANIFEST":
                continue
            content = PUBLICATION.render(
                release["publication"], item["generator"])
            observed = hashlib.sha256(content.encode("utf-8")).hexdigest()
            expected = item["sha256"].removeprefix("sha256:")
            _require(observed == expected,
                     "%s generated payload changed after planning" % item["id"])
            target = _inside(staging, item["release_path"],
                             "%s generated path" % item["id"])
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(content, encoding="utf-8", newline="\n")
            checksums.append((observed, item["release_path"]))

        replay_text = _replay_markdown(release)
        replay_path = staging / "REPLAY.md"
        replay_path.write_text(replay_text, encoding="utf-8", newline="\n")
        checksums.append((_digest(replay_path), "REPLAY.md"))
        (staging / "manifest.json").write_text(
            canonical_json(release), encoding="utf-8", newline="\n")
        checksum_text = "# %s\n%s" % (
            DIGEST_ALGO,
            "".join("%s  %s\n" % item for item in sorted(checksums,
                                                           key=lambda pair: pair[1])),
        )
        (staging / "SHA256SUMS").write_text(
            checksum_text, encoding="utf-8", newline="\n")
        os.replace(staging, output_dir)
    except Exception:
        if staging.exists():
            shutil.rmtree(staging)
        raise
    return {
        "output_dir": str(output_dir),
        "manifest": str(output_dir / "manifest.json"),
        "checksums": str(output_dir / "SHA256SUMS"),
        "replay": str(output_dir / "REPLAY.md"),
        "mode": "REPLAY_KIT" if replay_only else "FULL_RELEASE",
        "files": (len(inventory) + len(release["replay_resources"]) + 3 +
                  sum(item["generator"] != "RELEASE_MANIFEST"
                      for item in generated)),
        "plan_fingerprint": release["history"]["plan_fingerprint"],
    }


def materialize(release, source_root, output_dir):
    """Atomically write a publication-ready release into a new directory."""
    return _materialize(release, source_root, output_dir, replay_only=False)


def materialize_replay_kit(release, source_root, output_dir):
    """Atomically write replay closure without requiring publication readiness."""
    return _materialize(release, source_root, output_dir, replay_only=True)


def render(release):
    _require(isinstance(release, dict) and release.get("schema") == OUTPUT_SCHEMA,
             "renderer needs a campaign-release/v0")
    lines = [
        "# %s" % release["package"]["title"], "",
        "Release plan: `%s`" % release["history"]["plan_fingerprint"],
        "Authority: `DERIVED_READ_MODEL_ONLY`; graph effect: `NONE`.",
        "Profile: `%s` (original `%s`, projected `%s`)." % (
            release["profile"]["id"], release["profile"]["original_status"],
            release["profile"]["status"]),
        "Source: `%s`; materializable: `%s`; replay kit: `%s`." % (
            release["source_audit"]["status"],
            "YES" if release["materializable"] else "NO",
            "YES" if release["replay_materializable"] else "NO"), "",
        "## Coverage", "",
        "%d required; %d selected; %d missing." % (
            release["counts"]["required"], release["counts"]["selected"],
            release["counts"]["missing_coverage"]), "",
    ]
    if release["blockers"]:
        lines.extend(["## Blockers", ""])
        for blocker in release["blockers"]:
            lines.append("- `%s` %s" % (blocker["code"], blocker["detail"]))
        lines.append("")
    lines.extend(["## Inventory", ""])
    for item in release["inventory"]:
        lines.append("- `%s / %s / %s` **%s** -> `%s`" % (
            item["file_status"], item["license_status"], item["payload_class"],
            item["id"], item["release_path"]))
    if release["replay_resources"]:
        lines.extend(["", "## Replay closure", ""])
        for item in release["replay_resources"]:
            lines.append("- `%s / %s / %s` **%s** -> `%s`" % (
                item["file_status"], item["license_status"], item["role"],
                item["id"], item["release_path"]))
    if release["provides_artifact_ids"]:
        lines.extend(["", "Generated artifacts:", ""])
        for item in release["generated_artifacts"]:
            lines.append("- `%s` **%s** -> `%s`" % (
                item["generator"], item["id"], item["release_path"]))
    return "\n".join(lines) + "\n"


def canonical_json(value, pretty=True):
    return json.dumps(value, sort_keys=True, indent=2 if pretty else None,
                      separators=None if pretty else (",", ":"),
                      ensure_ascii=True) + "\n"
