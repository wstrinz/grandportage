"""Campaign portraits, residual price cards, and closeout profiles.

This module is a zone-4 derived read surface.  It checks that a campaign's
publication or maintenance story is explicit and internally consistent; it
does not prove any campaign claim and never writes a graph event.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess


INPUT_SCHEMA = "campaign-dossier-input/v0"
OUTPUT_SCHEMA = "campaign-dossier/v0"
AUTHORITY = "DERIVED_READ_MODEL_ONLY"
GRAPH_EFFECT = "NONE"
DIGEST_ALGO = "sha256-lf-normalized"

CLAIM_GRADES = {
    "PROVED", "CHECKED", "CONDITIONAL", "CITED", "RECONNAISSANCE",
}
ARTIFACT_GRADES = CLAIM_GRADES | {"ADVISORY"}
ARTIFACT_ROLES = {
    "AUTHORITY_SOURCE",
    "CLAIM_SUPPORT",
    "FORMAL_INTERFACE",
    "MECHANISM_CEILING",
    "RECONNAISSANCE",
    "PUBLICATION",
    "EXTERNAL_ASSUMPTION",
}
PUBLIC_DISPOSITIONS = {"INCLUDE", "EXCLUDE", "REVIEW"}
AVAILABILITY = {"PRESENT", "MISSING"}
REPLAY_STATUSES = {"PASS", "FAIL", "NOT_RUN", "NOT_APPLICABLE"}
LEAF_STATES = {"OPEN", "CLOSED"}
PRICE_STATUSES = {"PRICED", "PARTIAL", "UNPRICED"}
COST_CLASSES = {"SMALL", "MEDIUM", "LARGE", "SIEGE", "UNKNOWN"}
PROFILE_KINDS = {"SHORT_OF_SUMMIT", "GOLD", "MAINTENANCE", "CUSTOM"}
CRITERION_KINDS = {
    "SOURCE_FRESH",
    "CLAIMS_PRESENT",
    "LEAVES_PRICED",
    "LEAVES_CLOSED",
    "ARTIFACTS_PRESENT",
    "ARTIFACT_REPLAY_PASS",
}
SOURCE_STATUSES = {
    "UNCHECKED", "UNAVAILABLE", "STALE", "CURRENT_DIRTY", "CURRENT_CLEAN",
}

_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._:-]*$")
_SHA = re.compile(r"^(?:sha256:)?([0-9a-f]{64})$")
_COMMIT = re.compile(r"^[0-9a-f]{7,40}$")


class DossierError(ValueError):
    """A dossier is ambiguous, incomplete at its declared type, or unsafe."""


def _require(condition, message):
    if not condition:
        raise DossierError(message)


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


def _optional_string(value, label):
    if value is None:
        return None
    return _string(value, label)


def _string_list(value, label, *, sort=True, allow_empty=True):
    _require(isinstance(value, list), "%s must be a list" % label)
    _require(all(isinstance(item, str) and item for item in value),
             "%s entries must be nonempty strings" % label)
    _require(len(value) == len(set(value)), "%s contains duplicates" % label)
    _require(allow_empty or value, "%s must not be empty" % label)
    return sorted(value) if sort else list(value)


def _sha(value, label):
    match = _SHA.fullmatch(value) if isinstance(value, str) else None
    _require(match is not None, "%s must be a SHA-256 digest" % label)
    return match.group(1)


def _relative_path(value, label):
    _require(isinstance(value, str) and value, "%s must be a path" % label)
    path = Path(value)
    _require(not path.is_absolute(), "%s must be relative" % label)
    _require(".." not in path.parts, "%s must not escape its source root" % label)
    return path.as_posix()


def _unique(items, label):
    ids = [item["id"] for item in items]
    _require(len(ids) == len(set(ids)), "%s ids must be unique" % label)
    return sorted(items, key=lambda item: item["id"])


def _normalize_binding(value, label):
    _require(isinstance(value, dict), "%s must be an object" % label)
    _require(value.get("digest_algo") == DIGEST_ALGO,
             "%s must use %s" % (label, DIGEST_ALGO))
    return {
        "id": _stable_id(value.get("id"), "%s id" % label),
        "path": _relative_path(value.get("path"), "%s path" % label),
        "digest_algo": DIGEST_ALGO,
        "sha256": "sha256:" + _sha(value.get("sha256"), "%s sha256" % label),
    }


def _normalize_source(value):
    _require(isinstance(value, dict), "dossier source must be an object")
    commit = value.get("expected_commit")
    _require(isinstance(commit, str) and _COMMIT.fullmatch(commit),
             "source expected_commit must be a 7-40 digit lowercase git id")
    sources = [_normalize_binding(item, "canonical source")
               for item in value.get("canonical_sources", [])]
    _require(sources, "dossier needs at least one canonical source")
    return {
        "id": _stable_id(value.get("id"), "source id"),
        "repository": _string(value.get("repository"), "source repository"),
        "expected_commit": commit,
        "canonical_sources": _unique(sources, "canonical source"),
    }


def _normalize_replay(value, artifact_id):
    _require(isinstance(value, dict), "%s replay must be an object" % artifact_id)
    status = value.get("status")
    _require(status in REPLAY_STATUSES,
             "%s replay status is unknown" % artifact_id)
    command = _optional_string(value.get("command"), "%s replay command" % artifact_id)
    receipt = _optional_string(value.get("receipt"), "%s replay receipt" % artifact_id)
    if status == "PASS":
        _require(command and receipt,
                 "%s passing replay needs a command and receipt" % artifact_id)
    if status == "NOT_APPLICABLE":
        _require(command is None and receipt is None,
                 "%s non-applicable replay cannot claim a command or receipt" % artifact_id)
    return {"status": status, "command": command, "receipt": receipt}


def _normalize_artifact(value):
    _require(isinstance(value, dict), "dossier artifact must be an object")
    artifact_id = _stable_id(value.get("id"), "artifact id")
    availability = value.get("availability")
    grade = value.get("grade")
    role = value.get("role")
    disposition = value.get("public_disposition")
    _require(availability in AVAILABILITY,
             "%s availability is unknown" % artifact_id)
    _require(grade in ARTIFACT_GRADES, "%s grade is unknown" % artifact_id)
    _require(role in ARTIFACT_ROLES, "%s role is unknown" % artifact_id)
    _require(disposition in PUBLIC_DISPOSITIONS,
             "%s public disposition is unknown" % artifact_id)
    result = {
        "id": artifact_id,
        "availability": availability,
        "role": role,
        "grade": grade,
        "description": _string(value.get("description"),
                               "%s description" % artifact_id),
        "public_disposition": disposition,
        "replay": _normalize_replay(value.get("replay", {}), artifact_id),
        "generated_by": _optional_string(
            value.get("generated_by"), "%s generated_by" % artifact_id),
    }
    if availability == "PRESENT":
        result.update(_normalize_binding(value, "artifact %s" % artifact_id))
        result["availability"] = availability
        result["role"] = role
        result["grade"] = grade
        result["description"] = value["description"]
        result["public_disposition"] = disposition
        result["replay"] = _normalize_replay(value.get("replay", {}), artifact_id)
        _require(result["generated_by"] is None,
                 "%s is present and cannot declare a generator" % artifact_id)
    else:
        _require(value.get("path") is None and value.get("sha256") is None,
                 "%s is missing and cannot bind a path or digest" % artifact_id)
        _require(result["replay"]["status"] in {"NOT_RUN", "NOT_APPLICABLE"},
                 "%s is missing and cannot have a completed replay" % artifact_id)
        if result["generated_by"] is not None:
            _require(role == "PUBLICATION",
                     "%s generator contract requires a publication artifact" %
                     artifact_id)
    return result


def _normalize_claim(value, artifacts):
    _require(isinstance(value, dict), "portrait claim must be an object")
    claim_id = _stable_id(value.get("id"), "claim id")
    grade = value.get("grade")
    _require(grade in CLAIM_GRADES, "%s claim grade is unknown" % claim_id)
    evidence = _string_list(value.get("evidence_ids", []),
                            "%s evidence_ids" % claim_id, allow_empty=False)
    missing = sorted(set(evidence) - set(artifacts))
    _require(not missing, "%s names absent evidence: %s" %
             (claim_id, ", ".join(missing)))
    unavailable = [item for item in evidence
                   if artifacts[item]["availability"] != "PRESENT"]
    _require(not unavailable, "%s names missing evidence: %s" %
             (claim_id, ", ".join(unavailable)))
    if grade != "RECONNAISSANCE":
        recon = [item for item in evidence
                 if artifacts[item]["grade"] == "RECONNAISSANCE"]
        _require(not recon,
                 "%s launders reconnaissance evidence into %s: %s" %
                 (claim_id, grade, ", ".join(recon)))
    if grade == "PROVED":
        _require(any(artifacts[item]["grade"] == "PROVED" for item in evidence),
                 "%s needs proved evidence" % claim_id)
    if grade == "CHECKED":
        _require(any(artifacts[item]["grade"] in {"PROVED", "CHECKED"}
                     for item in evidence), "%s needs checked evidence" % claim_id)
    if grade == "CONDITIONAL":
        _require(any(artifacts[item]["grade"] in
                     {"PROVED", "CHECKED", "CONDITIONAL"}
                     for item in evidence), "%s needs typed conditional evidence" % claim_id)
    if grade == "CITED":
        _require(any(artifacts[item]["grade"] == "CITED" for item in evidence),
                 "%s needs cited evidence" % claim_id)
    if grade == "RECONNAISSANCE":
        _require(any(artifacts[item]["grade"] == "RECONNAISSANCE"
                     for item in evidence),
                 "%s needs reconnaissance evidence" % claim_id)
    assumptions = _string_list(value.get("assumptions", []),
                               "%s assumptions" % claim_id)
    if grade == "CONDITIONAL":
        _require(assumptions, "%s conditional claim needs assumptions" % claim_id)
    return {
        "id": claim_id,
        "scope_id": _stable_id(value.get("scope_id"), "%s scope_id" % claim_id),
        "proposition": _string(value.get("proposition"),
                               "%s proposition" % claim_id),
        "grade": grade,
        "evidence_ids": evidence,
        "assumptions": assumptions,
        "consumers": _string_list(value.get("consumers", []),
                                  "%s consumers" % claim_id),
    }


def _normalize_price(value, leaf_id):
    _require(isinstance(value, dict), "%s price must be an object" % leaf_id)
    status = value.get("status")
    cost = value.get("cost_class")
    _require(status in PRICE_STATUSES, "%s price status is unknown" % leaf_id)
    _require(cost in COST_CLASSES, "%s cost class is unknown" % leaf_id)
    basis = _optional_string(value.get("basis"), "%s price basis" % leaf_id)
    detail = _optional_string(value.get("detail"), "%s price detail" % leaf_id)
    if status in {"PRICED", "PARTIAL"}:
        _require(basis and detail,
                 "%s priced/partial card needs basis and detail" % leaf_id)
    if status == "PRICED":
        _require(cost != "UNKNOWN", "%s priced card needs a cost class" % leaf_id)
    return {"status": status, "cost_class": cost,
            "basis": basis, "detail": detail}


def _normalize_leaf(value, artifacts):
    _require(isinstance(value, dict), "leaf price card must be an object")
    leaf_id = _stable_id(value.get("id"), "leaf id")
    state = value.get("state")
    _require(state in LEAF_STATES, "%s leaf state is unknown" % leaf_id)
    evidence = _string_list(value.get("evidence_ids", []),
                            "%s evidence_ids" % leaf_id)
    missing = sorted(set(evidence) - set(artifacts))
    _require(not missing, "%s names absent evidence: %s" %
             (leaf_id, ", ".join(missing)))
    unavailable = [item for item in evidence
                   if artifacts[item]["availability"] != "PRESENT"]
    _require(not unavailable, "%s names missing evidence: %s" %
             (leaf_id, ", ".join(unavailable)))
    retired = value.get("retired_representations", [])
    _require(isinstance(retired, list),
             "%s retired_representations must be a list" % leaf_id)
    normalized_retired = []
    for item in retired:
        _require(isinstance(item, dict), "%s retired item must be an object" % leaf_id)
        normalized_retired.append({
            "id": _stable_id(item.get("id"), "%s retired id" % leaf_id),
            "reason": _string(item.get("reason"), "%s retired reason" % leaf_id),
            "evidence_ids": _string_list(item.get("evidence_ids", []),
                                         "%s retired evidence" % leaf_id,
                                         allow_empty=False),
        })
    normalized_retired = _unique(normalized_retired,
                                 "%s retired representation" % leaf_id)
    for item in normalized_retired:
        absent = sorted(set(item["evidence_ids"]) - set(artifacts))
        _require(not absent, "%s retired representation %s names absent evidence" %
                 (leaf_id, item["id"]))
        unavailable = [evidence_id for evidence_id in item["evidence_ids"]
                       if artifacts[evidence_id]["availability"] != "PRESENT"]
        _require(not unavailable,
                 "%s retired representation %s names missing evidence" %
                 (leaf_id, item["id"]))
    next_object = _optional_string(value.get("next_accepted_object"),
                                   "%s next accepted object" % leaf_id)
    resume = _optional_string(value.get("resume_condition"),
                              "%s resume condition" % leaf_id)
    if state == "OPEN":
        _require(next_object, "%s open leaf needs a next accepted object" % leaf_id)
        _require(resume, "%s open leaf needs a resume condition" % leaf_id)
    return {
        "id": leaf_id,
        "state": state,
        "theorem_role": _string(value.get("theorem_role"),
                                "%s theorem role" % leaf_id),
        "exact_object": _string(value.get("exact_object"),
                                "%s exact object" % leaf_id),
        "next_accepted_object": next_object,
        "price": _normalize_price(value.get("price"), leaf_id),
        "retired_representations": normalized_retired,
        "resume_condition": resume,
        "evidence_ids": evidence,
    }


def _normalize_criterion(value, profile_id, claims, leaves, artifacts):
    _require(isinstance(value, dict), "%s criterion must be an object" % profile_id)
    criterion_id = _stable_id(value.get("id"), "%s criterion id" % profile_id)
    kind = value.get("kind")
    _require(kind in CRITERION_KINDS,
             "%s criterion kind is unknown" % criterion_id)
    result = {"id": criterion_id, "kind": kind,
              "description": _string(value.get("description"),
                                     "%s description" % criterion_id)}
    if kind == "SOURCE_FRESH":
        allowed = _string_list(value.get("allowed_statuses", ["CURRENT_CLEAN"]),
                               "%s allowed_statuses" % criterion_id,
                               allow_empty=False)
        _require(set(allowed) <= SOURCE_STATUSES,
                 "%s names an unknown source status" % criterion_id)
        result["allowed_statuses"] = allowed
        return result
    field, known = {
        "CLAIMS_PRESENT": ("claim_ids", claims),
        "LEAVES_PRICED": ("leaf_ids", leaves),
        "LEAVES_CLOSED": ("leaf_ids", leaves),
        "ARTIFACTS_PRESENT": ("artifact_ids", artifacts),
        "ARTIFACT_REPLAY_PASS": ("artifact_ids", artifacts),
    }[kind]
    ids = _string_list(value.get(field, []), "%s %s" % (criterion_id, field),
                       allow_empty=False)
    absent = sorted(set(ids) - set(known))
    _require(not absent, "%s names absent records: %s" %
             (criterion_id, ", ".join(absent)))
    result[field] = ids
    if kind == "CLAIMS_PRESENT":
        grades = _string_list(value.get("allowed_grades", sorted(CLAIM_GRADES)),
                              "%s allowed_grades" % criterion_id,
                              allow_empty=False)
        _require(set(grades) <= CLAIM_GRADES,
                 "%s names an unknown claim grade" % criterion_id)
        result["allowed_grades"] = grades
    return result


def _normalize_profile(value, claims, leaves, artifacts):
    _require(isinstance(value, dict), "closeout profile must be an object")
    profile_id = _stable_id(value.get("id"), "profile id")
    kind = value.get("kind")
    _require(kind in PROFILE_KINDS, "%s profile kind is unknown" % profile_id)
    criteria = [_normalize_criterion(item, profile_id, claims, leaves, artifacts)
                for item in value.get("criteria", [])]
    _require(criteria, "%s needs at least one criterion" % profile_id)
    return {
        "id": profile_id,
        "kind": kind,
        "title": _string(value.get("title"), "%s title" % profile_id),
        "criteria": _unique(criteria, "%s criterion" % profile_id),
    }


def _normalize(value):
    _require(isinstance(value, dict) and value.get("schema") == INPUT_SCHEMA,
             "unsupported campaign dossier input schema")
    _require(value.get("authority") == AUTHORITY and
             value.get("graph_effect") == GRAPH_EFFECT,
             "campaign dossier widened authority")
    source = _normalize_source(value.get("source"))
    artifacts_list = [_normalize_artifact(item)
                      for item in value.get("artifacts", [])]
    artifacts_list = _unique(artifacts_list, "artifact")
    path_digests = {}
    for item in source["canonical_sources"] + [
            artifact for artifact in artifacts_list
            if artifact["availability"] == "PRESENT"]:
        prior = path_digests.get(item["path"])
        _require(prior in {None, item["sha256"]},
                 "%s has conflicting expected digests" % item["path"])
        path_digests[item["path"]] = item["sha256"]
    artifacts = {item["id"]: item for item in artifacts_list}
    claims_list = [_normalize_claim(item, artifacts)
                   for item in value.get("claims", [])]
    claims_list = _unique(claims_list, "claim")
    claims = {item["id"]: item for item in claims_list}
    leaves_list = [_normalize_leaf(item, artifacts)
                   for item in value.get("leaves", [])]
    leaves_list = _unique(leaves_list, "leaf")
    leaves = {item["id"]: item for item in leaves_list}
    _require(claims_list, "dossier needs at least one portrait claim")
    _require(leaves_list, "dossier needs at least one leaf price card")
    profiles = [_normalize_profile(item, claims, leaves, artifacts)
                for item in value.get("profiles", [])]
    profiles = _unique(profiles, "profile")
    _require(profiles, "dossier needs at least one closeout profile")
    return {
        "campaign": {
            "id": _stable_id(value.get("campaign", {}).get("id"), "campaign id"),
            "title": _string(value.get("campaign", {}).get("title"),
                             "campaign title"),
            "summit_status": _string(value.get("campaign", {}).get("summit_status"),
                                     "campaign summit_status"),
        },
        "source": source,
        "artifacts": artifacts_list,
        "claims": claims_list,
        "leaves": leaves_list,
        "profiles": profiles,
    }


def _git(root, *args):
    try:
        result = subprocess.run(
            ["git", "-c", "safe.directory=%s" % root.as_posix(),
             "-C", str(root), *args], check=False,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, encoding="utf-8", errors="replace", timeout=15,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return None, str(exc)
    if result.returncode:
        return None, result.stderr.strip() or "git command failed"
    return result.stdout.strip(), None


def _git_bytes(root, *args):
    try:
        result = subprocess.run(
            ["git", "-c", "safe.directory=%s" % root.as_posix(),
             "-C", str(root), *args], check=False,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=15,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return None, str(exc)
    if result.returncode:
        return None, result.stderr.decode(
            "utf-8", errors="replace").strip() or "git command failed"
    return result.stdout, None


def _audit_source(source, artifacts, source_root, source_ref=None):
    if source_root is None:
        return {
            "status": "UNCHECKED",
            "expected_commit": source["expected_commit"],
            "observed_commit": None,
            "commit_matches": None,
            "dirty": None,
            "dirty_paths": [],
            "files": [],
            "problems": ["source checkout was not supplied"],
        }
    root = Path(source_root).resolve()
    if not root.is_dir():
        return {
            "status": "UNAVAILABLE",
            "expected_commit": source["expected_commit"],
            "observed_commit": None,
            "commit_matches": False,
            "dirty": None,
            "dirty_paths": [],
            "files": [],
            "problems": ["source checkout is absent: %s" % root],
        }
    pinned_head = None
    pinned_error = None
    if source_ref is not None:
        pinned_head, pinned_error = _git(
            root, "rev-parse", "--verify", str(source_ref) + "^{commit}")

    records = [("source", item) for item in source["canonical_sources"]]
    records.extend(("artifact", item) for item in artifacts
                   if item["availability"] == "PRESENT")
    file_results = []
    problems = []
    seen_paths = {}
    for record_kind, item in records:
        relative = item["path"]
        expected = item["sha256"].split(":", 1)[-1]
        path = (root / relative).resolve()
        try:
            path.relative_to(root)
        except ValueError:
            problems.append("%s path escapes source root" % item["id"])
            file_results.append({"id": item["id"], "kind": record_kind,
                                 "path": relative, "status": "ESCAPED"})
            continue
        if source_ref is not None:
            if pinned_head is None:
                present, observed = False, None
            else:
                payload, payload_error = _git_bytes(
                    root, "show", "%s:%s" %
                    (pinned_head, relative.replace("\\", "/")))
                present = payload_error is None
                observed = (hashlib.sha256(payload).hexdigest()
                            if present else None)
        else:
            present = path.is_file()
            observed = _digest(path) if present else None
        if not present:
            result = {"id": item["id"], "kind": record_kind,
                      "path": relative, "status": "MISSING",
                      "expected_sha256": "sha256:" + expected,
                      "observed_sha256": None}
            problems.append("%s is missing" % item["id"])
        else:
            status = "MATCH" if observed == expected else "DIGEST_MISMATCH"
            result = {"id": item["id"], "kind": record_kind,
                      "path": relative, "status": status,
                      "expected_sha256": "sha256:" + expected,
                      "observed_sha256": "sha256:" + observed}
            if status != "MATCH":
                problems.append("%s digest changed" % item["id"])
        duplicate = seen_paths.get(relative)
        if duplicate and duplicate != expected:
            problems.append("%s has conflicting expected digests" % relative)
        seen_paths[relative] = expected
        file_results.append(result)
    if source_ref is None:
        head, head_error = _git(root, "rev-parse", "HEAD")
        status_text, status_error = _git(root, "status", "--porcelain",
                                         "--untracked-files=all")
    else:
        head, head_error = pinned_head, pinned_error
        status_text, status_error = "", None
    if head_error:
        problems.append("cannot read source commit: %s" % head_error)
    if status_error:
        problems.append("cannot read source dirt: %s" % status_error)
    commit_matches = bool(head and head.startswith(source["expected_commit"]))
    if head and not commit_matches:
        problems.append("source commit changed")
    dirty_paths = sorted(line for line in (status_text or "").splitlines() if line)
    dirty = None if status_error else bool(dirty_paths)
    stale = any(item["status"] != "MATCH" for item in file_results)
    stale = stale or not commit_matches
    if head_error or status_error:
        audit_status = "UNAVAILABLE"
    elif stale:
        audit_status = "STALE"
    elif dirty:
        audit_status = "CURRENT_DIRTY"
    else:
        audit_status = "CURRENT_CLEAN"
    return {
        "status": audit_status,
        "root": str(root),
        "source_ref": source_ref,
        "expected_commit": source["expected_commit"],
        "observed_commit": head,
        "commit_matches": commit_matches,
        "dirty": dirty,
        "dirty_paths": dirty_paths,
        "files": sorted(file_results, key=lambda item: (item["path"], item["id"])),
        "problems": sorted(set(problems)),
    }


def _criterion_result(criterion, source_audit, claims, leaves, artifacts):
    kind = criterion["kind"]
    blockers = []
    if kind == "SOURCE_FRESH":
        if source_audit["status"] not in criterion["allowed_statuses"]:
            blockers.append("source is %s; accepted: %s" % (
                source_audit["status"], ", ".join(criterion["allowed_statuses"])))
    elif kind == "CLAIMS_PRESENT":
        for claim_id in criterion["claim_ids"]:
            if claims[claim_id]["grade"] not in criterion["allowed_grades"]:
                blockers.append("%s has grade %s" %
                                (claim_id, claims[claim_id]["grade"]))
    elif kind == "LEAVES_PRICED":
        for leaf_id in criterion["leaf_ids"]:
            if leaves[leaf_id]["price"]["status"] != "PRICED":
                blockers.append("%s price is %s" %
                                (leaf_id, leaves[leaf_id]["price"]["status"]))
    elif kind == "LEAVES_CLOSED":
        for leaf_id in criterion["leaf_ids"]:
            if leaves[leaf_id]["state"] != "CLOSED":
                blockers.append("%s remains %s" %
                                (leaf_id, leaves[leaf_id]["state"]))
    elif kind == "ARTIFACTS_PRESENT":
        for artifact_id in criterion["artifact_ids"]:
            if artifacts[artifact_id]["availability"] != "PRESENT":
                blockers.append("%s is missing" % artifact_id)
    elif kind == "ARTIFACT_REPLAY_PASS":
        for artifact_id in criterion["artifact_ids"]:
            status = artifacts[artifact_id]["replay"]["status"]
            if status != "PASS":
                blockers.append("%s replay is %s" % (artifact_id, status))
    # Keep the criterion's exact references in the evaluated read model.  A
    # downstream archival plan must be able to compute transitive evidence
    # coverage without reparsing (or silently disagreeing with) the input.
    return {
        **criterion,
        "passed": not blockers,
        "blockers": blockers,
    }


def _evaluate_profiles(profiles, source_audit, claims, leaves, artifacts):
    results = []
    for profile in profiles:
        criteria = [_criterion_result(item, source_audit, claims, leaves, artifacts)
                    for item in profile["criteria"]]
        results.append({
            "id": profile["id"],
            "kind": profile["kind"],
            "title": profile["title"],
            "status": "READY" if all(item["passed"] for item in criteria)
                      else "NOT_READY",
            "criteria": criteria,
            "counts": {
                "criteria": len(criteria),
                "passed": sum(item["passed"] for item in criteria),
                "blocked": sum(not item["passed"] for item in criteria),
                "blockers": sum(len(item["blockers"]) for item in criteria),
            },
        })
    return results


def build(value, source_root=None, source_ref=None):
    """Compile one normalized dossier and evaluate its closeout profiles."""
    normalized = _normalize(value)
    artifacts = {item["id"]: item for item in normalized["artifacts"]}
    claims = {item["id"]: item for item in normalized["claims"]}
    leaves = {item["id"]: item for item in normalized["leaves"]}
    audit = _audit_source(
        normalized["source"], normalized["artifacts"], source_root,
        source_ref=source_ref)
    profiles = _evaluate_profiles(normalized["profiles"], audit,
                                  claims, leaves, artifacts)
    body = {
        "schema": OUTPUT_SCHEMA,
        "authority": AUTHORITY,
        "graph_effect": GRAPH_EFFECT,
        "campaign": normalized["campaign"],
        "source": {**normalized["source"], "audit": audit},
        "claims": normalized["claims"],
        "leaves": normalized["leaves"],
        "artifacts": normalized["artifacts"],
        "profiles": profiles,
        "counts": {
            "claims": len(normalized["claims"]),
            "open_leaves": sum(item["state"] == "OPEN"
                               for item in normalized["leaves"]),
            "closed_leaves": sum(item["state"] == "CLOSED"
                                 for item in normalized["leaves"]),
            "priced_open_leaves": sum(
                item["state"] == "OPEN" and item["price"]["status"] == "PRICED"
                for item in normalized["leaves"]),
            "artifacts_present": sum(item["availability"] == "PRESENT"
                                     for item in normalized["artifacts"]),
            "artifacts_missing": sum(item["availability"] == "MISSING"
                                     for item in normalized["artifacts"]),
            "profiles_ready": sum(item["status"] == "READY" for item in profiles),
        },
    }
    body["history"] = {
        "immutable_inputs": True,
        "input_fingerprint": _fingerprint(normalized),
        "observation_fingerprint": _fingerprint({
            "input": normalized, "source_audit": audit, "profiles": profiles,
        }),
    }
    return body


def build_path(path, source_root=None, source_ref=None):
    try:
        value = json.loads(Path(path).read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise DossierError("campaign dossier is not JSON: %s" % exc)
    return build(value, source_root=source_root, source_ref=source_ref)


def render(dossier):
    _require(isinstance(dossier, dict) and dossier.get("schema") == OUTPUT_SCHEMA,
             "renderer needs a campaign-dossier/v0")
    campaign = dossier["campaign"]
    audit = dossier["source"]["audit"]
    lines = [
        "# %s" % campaign["title"],
        "",
        "Dossier: `%s`" % dossier["history"]["observation_fingerprint"],
        "Authority: `DERIVED_READ_MODEL_ONLY`; graph effect: `NONE`.",
        "Summit: %s" % campaign["summit_status"],
        "",
        "## Source freshness",
        "",
        "Status: `%s`; expected `%s`; observed `%s`." % (
            audit["status"], audit["expected_commit"],
            audit["observed_commit"] or "not checked"),
    ]
    if audit["dirty"]:
        lines.append("Dirty paths: %d." % len(audit["dirty_paths"]))
    for problem in audit["problems"]:
        lines.append("- %s" % problem)
    lines.extend(["", "## Closeout profiles", ""])
    for profile in dossier["profiles"]:
        lines.append("### %s — `%s`" % (profile["title"], profile["status"]))
        lines.append("")
        for criterion in profile["criteria"]:
            mark = "PASS" if criterion["passed"] else "BLOCKED"
            lines.append("- `%s` %s: %s" %
                         (mark, criterion["id"], criterion["description"]))
            for blocker in criterion["blockers"]:
                lines.append("  - %s" % blocker)
        lines.append("")
    lines.extend(["## Current portrait", ""])
    for claim in dossier["claims"]:
        lines.append("- `%s` **%s** — %s" %
                     (claim["grade"], claim["id"], claim["proposition"]))
    lines.extend(["", "## Residual price ledger", ""])
    for leaf in dossier["leaves"]:
        lines.append("### %s — `%s / %s`" %
                     (leaf["id"], leaf["state"], leaf["price"]["status"]))
        lines.append("")
        lines.append(leaf["exact_object"])
        if leaf["state"] == "OPEN":
            lines.append("")
            lines.append("Next accepted object: %s" % leaf["next_accepted_object"])
            lines.append("Resume only when: %s" % leaf["resume_condition"])
        if leaf["retired_representations"]:
            lines.append("Retired: %s." % ", ".join(
                item["id"] for item in leaf["retired_representations"]))
        lines.append("")
    lines.extend(["## Release artifacts", ""])
    for artifact in dossier["artifacts"]:
        lines.append("- `%s / %s / %s` **%s** — %s" % (
            artifact["availability"], artifact["grade"], artifact["role"],
            artifact["id"], artifact["description"]))
    return "\n".join(lines) + "\n"


def canonical_json(value, pretty=True):
    return json.dumps(value, sort_keys=True, indent=2 if pretty else None,
                      separators=None if pretty else (",", ":"),
                      ensure_ascii=True) + "\n"
