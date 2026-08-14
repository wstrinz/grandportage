"""Publication-facing tables compiled from campaign closeout records.

The projection makes dependencies, qualifications, residual work, and replay
status legible to authors and reviewers.  It is presentation, not authority.
"""

from __future__ import annotations

import hashlib
import json


OUTPUT_SCHEMA = "campaign-publication/v0"
AUTHORITY = "DERIVED_READ_MODEL_ONLY"
GRAPH_EFFECT = "NONE"
DOCUMENTS = {"PORTRAIT_AUDIT", "MANUSCRIPT_TABLES", "FULL_REPORT"}


class PublicationError(ValueError):
    """Publication input is incomplete or a requested document is unknown."""


def _require(condition, message):
    if not condition:
        raise PublicationError(message)


def _canonical_bytes(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=True).encode("ascii")


def _fingerprint(value):
    return "sha256:" + hashlib.sha256(_canonical_bytes(value)).hexdigest()


def _table(value):
    return str(value).replace("|", "\\|").replace("\r", " ").replace("\n", " ")


def _joined(values, empty="—"):
    return ", ".join("`%s`" % value for value in values) if values else empty


def build(dossier, *, package, profile, coverage, inventory, replay_lanes,
          blockers, generated_artifact_ids):
    """Compile stable author/reviewer tables from an evaluated release plan."""
    _require(dossier.get("schema") == "campaign-dossier/v0",
             "publication projection needs a campaign-dossier/v0")
    artifacts = {item["id"]: item for item in dossier["artifacts"]}
    selected = {item["id"]: item for item in inventory}
    lanes_by_artifact = {}
    for lane in replay_lanes:
        for artifact_id in lane["artifact_ids"]:
            lanes_by_artifact.setdefault(artifact_id, []).append(lane["id"])

    claims = []
    for claim in dossier["claims"]:
        evidence = []
        for artifact_id in claim["evidence_ids"]:
            artifact = artifacts[artifact_id]
            release_item = selected.get(artifact_id)
            evidence.append({
                "id": artifact_id,
                "role": artifact["role"],
                "grade": artifact["grade"],
                "availability": artifact["availability"],
                "replay_status": artifact["replay"]["status"],
                "replay_command": artifact["replay"]["command"],
                "public_disposition": artifact["public_disposition"],
                "selected": release_item is not None,
                "release_path": (release_item or {}).get("release_path"),
                "license_status": (release_item or {}).get("license_status"),
                "replay_lane_ids": sorted(lanes_by_artifact.get(artifact_id, [])),
            })
        claims.append({
            "id": claim["id"],
            "scope_id": claim["scope_id"],
            "proposition": claim["proposition"],
            "grade": claim["grade"],
            "assumptions": claim["assumptions"],
            "consumers": claim["consumers"],
            "evidence": evidence,
            "release_covered": all(item["selected"] for item in evidence),
        })

    leaves = []
    for leaf in dossier["leaves"]:
        leaves.append({
            "id": leaf["id"],
            "state": leaf["state"],
            "theorem_role": leaf["theorem_role"],
            "exact_object": leaf["exact_object"],
            "next_accepted_object": leaf["next_accepted_object"],
            "price": leaf["price"],
            "resume_condition": leaf["resume_condition"],
            "evidence_ids": leaf["evidence_ids"],
            "retired_representations": leaf["retired_representations"],
        })

    replay = []
    for artifact in dossier["artifacts"]:
        release_item = selected.get(artifact["id"])
        replay.append({
            "id": artifact["id"],
            "role": artifact["role"],
            "grade": artifact["grade"],
            "availability": artifact["availability"],
            "replay_status": artifact["replay"]["status"],
            "replay_command": artifact["replay"]["command"],
            "replay_receipt": artifact["replay"]["receipt"],
            "selected": release_item is not None,
            "release_path": (release_item or {}).get("release_path"),
            "payload_class": (release_item or {}).get("payload_class"),
            "license_status": (release_item or {}).get("license_status"),
            "replay_lane_ids": sorted(lanes_by_artifact.get(artifact["id"], [])),
        })

    body = {
        "schema": OUTPUT_SCHEMA,
        "authority": AUTHORITY,
        "graph_effect": GRAPH_EFFECT,
        "campaign": dossier["campaign"],
        "package": package,
        "profile": profile,
        "coverage": coverage,
        "claims": claims,
        "leaves": leaves,
        "replay": replay,
        "blockers": blockers,
        "generated_artifact_ids": sorted(generated_artifact_ids),
        "counts": {
            "claims": len(claims),
            "proved_claims": sum(item["grade"] == "PROVED" for item in claims),
            "conditional_claims": sum(item["grade"] == "CONDITIONAL"
                                      for item in claims),
            "claims_release_covered": sum(item["release_covered"]
                                          for item in claims),
            "open_leaves": sum(item["state"] == "OPEN" for item in leaves),
            "priced_open_leaves": sum(
                item["state"] == "OPEN" and item["price"]["status"] == "PRICED"
                for item in leaves),
            "replay_rows": len(replay),
            "blockers": len(blockers),
        },
    }
    body["history"] = {
        "dossier_input_fingerprint": dossier["history"]["input_fingerprint"],
        "publication_fingerprint": _fingerprint(body),
    }
    return body


def render_portrait_audit(publication):
    _require(publication.get("schema") == OUTPUT_SCHEMA,
             "portrait audit needs a campaign-publication/v0")
    campaign = publication["campaign"]
    lines = [
        "# %s — portrait dependency audit" % campaign["title"], "",
        "Publication projection: `%s`." %
        publication["history"]["publication_fingerprint"],
        "Authority: `DERIVED_READ_MODEL_ONLY`; graph effect: `NONE`.",
        "Summit status: %s" % campaign["summit_status"], "",
        "This audit records declared scopes, grades, assumptions, consumers, and "
        "evidence dependencies. It does not upgrade any claim.", "",
        "## Claim index", "",
        "| claim | grade | scope | evidence | assumptions | release covered |",
        "|---|---|---|---|---|---|",
    ]
    for claim in publication["claims"]:
        lines.append("| `%s` | `%s` | `%s` | %s | %s | %s |" % (
            claim["id"], claim["grade"], claim["scope_id"],
            _joined([item["id"] for item in claim["evidence"]]),
            _joined(claim["assumptions"]),
            "YES" if claim["release_covered"] else "NO"))
    lines.extend(["", "## Dependency cards", ""])
    for claim in publication["claims"]:
        lines.extend([
            "### `%s` — `%s`" % (claim["id"], claim["grade"]), "",
            claim["proposition"], "",
            "- Scope: `%s`" % claim["scope_id"],
            "- Assumptions: %s" % _joined(claim["assumptions"]),
            "- Consumers: %s" % _joined(claim["consumers"]),
            "- Release coverage: `%s`" %
            ("COVERED" if claim["release_covered"] else "INCOMPLETE"), "",
            "| evidence | artifact grade / role | availability | replay | lane | release |",
            "|---|---|---|---|---|---|",
        ])
        for item in claim["evidence"]:
            release = ("`%s`" % item["release_path"]
                       if item["selected"] else "NOT SELECTED")
            lines.append("| `%s` | `%s / %s` | `%s` | `%s` | %s | %s |" % (
                item["id"], item["grade"], item["role"], item["availability"],
                item["replay_status"], _joined(item["replay_lane_ids"]), release))
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def render_manuscript_tables(publication):
    _require(publication.get("schema") == OUTPUT_SCHEMA,
             "manuscript tables need a campaign-publication/v0")
    lines = [
        "# %s — manuscript tables" % publication["campaign"]["title"], "",
        "These tables are generated editorial material, not a manuscript and "
        "not mathematical authority.", "",
        "## Current portrait", "",
        "| claim | grade | exact scope | proposition | qualifications |",
        "|---|---|---|---|---|",
    ]
    for claim in publication["claims"]:
        qualification = (_joined(claim["assumptions"])
                         if claim["assumptions"] else "none declared")
        lines.append("| `%s` | `%s` | `%s` | %s | %s |" % (
            claim["id"], claim["grade"], claim["scope_id"],
            _table(claim["proposition"]), _table(qualification)))
    lines.extend([
        "", "## Residual and price ledger", "",
        "| leaf | state / price | cost | theorem role | smallest faithful object | next accepted object | resume condition |",
        "|---|---|---|---|---|---|---|",
    ])
    for leaf in publication["leaves"]:
        lines.append("| `%s` | `%s / %s` | `%s` | %s | %s | %s | %s |" % (
            leaf["id"], leaf["state"], leaf["price"]["status"],
            leaf["price"]["cost_class"], _table(leaf["theorem_role"]),
            _table(leaf["exact_object"]),
            _table(leaf["next_accepted_object"] or "closed"),
            _table(leaf["resume_condition"] or "closed")))
    lines.extend([
        "", "## Retired representations", "",
        "| leaf | representation | exact retirement reason | evidence |",
        "|---|---|---|---|",
    ])
    retired_count = 0
    for leaf in publication["leaves"]:
        for retired in leaf["retired_representations"]:
            retired_count += 1
            lines.append("| `%s` | `%s` | %s | %s |" % (
                leaf["id"], retired["id"], _table(retired["reason"]),
                _joined(retired["evidence_ids"])))
    if not retired_count:
        lines.append("| — | — | No retired representations declared. | — |")
    lines.extend([
        "", "## Replay and archival matrix", "",
        "| artifact | grade / role | replay | lane | selected payload |",
        "|---|---|---|---|---|",
    ])
    for row in publication["replay"]:
        payload = ("`%s`" % row["release_path"] if row["selected"]
                   else "not selected")
        lines.append("| `%s` | `%s / %s` | `%s` | %s | %s |" % (
            row["id"], row["grade"], row["role"], row["replay_status"],
            _joined(row["replay_lane_ids"]), payload))
    lines.extend([
        "", "## Publication blockers", "",
        "| class | record | blocker |",
        "|---|---|---|",
    ])
    if publication["blockers"]:
        for blocker in publication["blockers"]:
            lines.append("| `%s` | %s | %s |" % (
                blocker["code"],
                ("`%s`" % blocker["record_id"]
                 if blocker.get("record_id") else "—"),
                _table(blocker["detail"])))
    else:
        lines.append("| `NONE` | — | The selected publication profile is ready. |")
    return "\n".join(lines).rstrip() + "\n"


def render(publication, document="FULL_REPORT"):
    _require(document in DOCUMENTS, "unknown publication document: %s" % document)
    if document == "PORTRAIT_AUDIT":
        return render_portrait_audit(publication)
    if document == "MANUSCRIPT_TABLES":
        return render_manuscript_tables(publication)
    return (render_portrait_audit(publication).rstrip() + "\n\n---\n\n" +
            render_manuscript_tables(publication))


def canonical_json(value, pretty=True):
    return json.dumps(value, sort_keys=True, indent=2 if pretty else None,
                      separators=None if pretty else (",", ":"),
                      ensure_ascii=True) + "\n"
