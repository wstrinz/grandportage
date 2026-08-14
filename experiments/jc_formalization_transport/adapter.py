#!/usr/bin/env python3
"""Compile and audit the JC formalization transport ledger v0.

This is a deliberately derived integration assay.  It binds exact source
files and Lean declarations, records semantic endpoints and theorem premises,
and asks the existing Grand Portage kernel about transports which genuinely
fit its exact-affine relation vocabulary.  Edges outside that vocabulary fail
closed.  Nothing emitted here is a graph event or mathematical authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

from grandportage import kernel as K


ROOT = Path(__file__).resolve().parents[2]
NATIVE_ROOT = ROOT.parent / "math-stuff"
DEFAULT_FIXTURE = (
    ROOT / "fixtures" / "jc_formalization_transport" / "v0.json")

SCHEMA = "formalization-transport-ledger/v0"
INPUT_SCHEMA = "formalization-transport-ledger-input/v0"
AUTHORITY = "DERIVED_READ_MODEL_ONLY"
GRAPH_EFFECT = "NONE"
OUT_OF_KERNEL = "OUT_OF_KERNEL"
DEFINITIONAL = "DEFINITIONAL"
INEXPRESSIBLE = "INEXPRESSIBLE"
LICENSED = "LICENSED"
REFUSED = "REFUSED"

_ID = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._:-]*$")
_SHA256 = re.compile(r"^[0-9a-f]{64}$")
_OBJECT_STATUSES = {"LANDED", "OPEN", "PLANNED", "RETIRED", "DEFINITIONAL"}
_EDGE_STATUSES = {"LANDED", "OPEN", "PLANNED", "RETIRED", "DEFINITIONAL"}
_REPRESENTATIONS = {
    "AFFINE_MODEL", "FINITE_JET", "FORMAL_POWER_SERIES", "LEAN_TYPE",
    "LEAN_PREDICATE", "NATIVE_ARTIFACT", "RELATIONAL_SCOPE",
}
_AUTHORITY_KINDS = {"LEAN_DEFINITION", "LEAN_THEOREM"}
_REPLAY_STATUSES = {"PASS", "PACKET_REPORTED_PASS", "NOT_RUN"}
_CUSTOM_CLAIMS = {"DIMENSION_LOWER_CREDIT"}
_TRANSPORT_ATTRIBUTE_FIELDS = {
    "certificate", "map_kind", "zariski_closed", "identity_origin",
    "integral", "ring_iso", "coefficients_in_base", "zariski_dense",
    "existential", "image_complete", "exact_contraction",
    "geometric_closure", "point_surjective", "target_expressible",
}


class FormalizationLedgerError(ValueError):
    """The ledger input, formal binding, or expected refusal drifted."""


def _require(condition, check_id, message):
    if not condition:
        raise FormalizationLedgerError("%s: %s" % (check_id, message))


def _stable_id(value, where):
    _require(isinstance(value, str) and _ID.match(value), "ID1",
             "%s is not a stable semantic id" % where)
    return value


def _string(value, where):
    _require(isinstance(value, str) and value.strip(), "S1",
             "%s must be a nonempty string" % where)
    return value


def _string_list(value, where, identifiers=False):
    _require(isinstance(value, list), "L1", "%s must be a list" % where)
    result = []
    for index, item in enumerate(value):
        item = (_stable_id(item, "%s[%d]" % (where, index))
                if identifiers else _string(item, "%s[%d]" % (where, index)))
        result.append(item)
    _require(len(result) == len(set(result)), "L2",
             "%s repeats an entry" % where)
    return result


def _exact_fields(value, expected, where):
    _require(isinstance(value, dict) and set(value) == set(expected), "F1",
             "%s has unknown or missing fields" % where)


def _sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def canonical_json(value, pretty=True):
    separators = None if pretty else (",", ":")
    return json.dumps(value, indent=2 if pretty else None, sort_keys=True,
                      separators=separators, ensure_ascii=True) + "\n"


def fingerprint(value):
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":"),
                         ensure_ascii=True).encode("utf-8")
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def _indexed(records, kind):
    result = {}
    for record in records:
        item_id = _stable_id(record.get("id"), "%s.id" % kind)
        _require(item_id not in result, "ID2",
                 "%s repeats id %s" % (kind, item_id))
        result[item_id] = record
    return result


def _normalize_source(value):
    fields = {"id", "kind", "path", "sha256"}
    _exact_fields(value, fields, "source")
    result = dict(value)
    _stable_id(result["id"], "source.id")
    _string(result["kind"], "%s kind" % result["id"])
    path = _string(result["path"], "%s path" % result["id"])
    _require(not Path(path).is_absolute() and ".." not in Path(path).parts,
             "SRC1", "%s path is not a safe relative path" % result["id"])
    _require(isinstance(result["sha256"], str) and
             _SHA256.match(result["sha256"]), "SRC2",
             "%s sha256 is malformed" % result["id"])
    return result


def _normalize_object(value, source_ids):
    fields = {
        "id", "label", "representation", "status", "scope_id",
        "coefficient_domain", "source_ids", "notes",
    }
    _exact_fields(value, fields, "object")
    result = dict(value)
    object_id = _stable_id(result["id"], "object.id")
    _string(result["label"], "%s label" % object_id)
    _require(result["representation"] in _REPRESENTATIONS, "OBJ1",
             "%s has unknown representation" % object_id)
    _require(result["status"] in _OBJECT_STATUSES, "OBJ2",
             "%s has unknown status" % object_id)
    _stable_id(result["scope_id"], "%s scope_id" % object_id)
    _string(result["coefficient_domain"],
            "%s coefficient_domain" % object_id)
    result["source_ids"] = _string_list(
        result["source_ids"], "%s source_ids" % object_id, identifiers=True)
    _require(set(result["source_ids"]) <= source_ids, "OBJ3",
             "%s names an unknown source" % object_id)
    _string(result["notes"], "%s notes" % object_id)
    return result


def _normalize_premise(value, authority_ids):
    fields = {"id", "statement", "status", "scope_id", "authority_id"}
    _exact_fields(value, fields, "premise")
    result = dict(value)
    premise_id = _stable_id(result["id"], "premise.id")
    _string(result["statement"], "%s statement" % premise_id)
    _require(result["status"] in {"OPEN", "DISCHARGED", "ASSUMED"}, "PRE1",
             "%s has unknown status" % premise_id)
    _stable_id(result["scope_id"], "%s scope_id" % premise_id)
    if result["authority_id"] is not None:
        _stable_id(result["authority_id"], "%s authority_id" % premise_id)
        _require(result["authority_id"] in authority_ids, "PRE2",
                 "%s names an unknown authority" % premise_id)
    return result


def _normalize_authority(value, source_ids, object_ids):
    fields = {
        "id", "kind", "source_id", "declaration", "source_contains",
        "source_object_id", "target_object_id", "scope_id",
        "coefficient_domain", "premise_ids", "replay",
    }
    _exact_fields(value, fields, "authority")
    result = dict(value)
    authority_id = _stable_id(result["id"], "authority.id")
    _require(result["kind"] in _AUTHORITY_KINDS, "AUT1",
             "%s has unknown authority kind" % authority_id)
    _require(result["source_id"] in source_ids, "AUT2",
             "%s names an unknown source" % authority_id)
    _string(result["declaration"], "%s declaration" % authority_id)
    _string(result["source_contains"], "%s source_contains" % authority_id)
    for field in ("source_object_id", "target_object_id"):
        _require(result[field] in object_ids, "AUT3",
                 "%s names an unknown %s" % (authority_id, field))
    _stable_id(result["scope_id"], "%s scope_id" % authority_id)
    _string(result["coefficient_domain"],
            "%s coefficient_domain" % authority_id)
    result["premise_ids"] = _string_list(
        result["premise_ids"], "%s premise_ids" % authority_id,
        identifiers=True)
    replay = result["replay"]
    _exact_fields(replay, {"command", "status"}, "%s replay" % authority_id)
    _string(replay["command"], "%s replay.command" % authority_id)
    _require(replay["status"] in _REPLAY_STATUSES, "AUT4",
             "%s has unknown replay status" % authority_id)
    return result


def _normalize_edge(value, object_ids, authority_by_id, premise_ids):
    fields = {
        "id", "source", "target", "status", "relation", "authority_id",
        "losses", "premise_ids", "consumers", "rationale",
    }
    _exact_fields(value, fields, "edge")
    result = dict(value)
    edge_id = _stable_id(result["id"], "edge.id")
    for field in ("source", "target"):
        _require(result[field] in object_ids, "EDG1",
                 "%s names an unknown %s object" % (edge_id, field))
    _require(result["source"] != result["target"], "EDG2",
             "%s is a self-edge" % edge_id)
    _require(result["status"] in _EDGE_STATUSES, "EDG3",
             "%s has unknown status" % edge_id)
    _require(result["relation"] in set(K.DECLARABLE_TYPES) |
             {OUT_OF_KERNEL, DEFINITIONAL}, "EDG4",
             "%s has unknown relation" % edge_id)
    authority_id = result["authority_id"]
    if authority_id is not None:
        _require(authority_id in authority_by_id, "EDG5",
                 "%s names an unknown authority" % edge_id)
        authority = authority_by_id[authority_id]
        _require(authority["source_object_id"] == result["source"] and
                 authority["target_object_id"] == result["target"], "EDG6",
                 "%s authority endpoint binding does not match" % edge_id)
        _require(authority["premise_ids"] == result["premise_ids"], "EDG7",
                 "%s omitted or invented a formal premise" % edge_id)
    result["losses"] = _string_list(
        result["losses"], "%s losses" % edge_id)
    if result["relation"] in K.LOSSY_TYPES:
        _require(result["losses"], "EDG9",
                 "%s is lossy but names no information loss" % edge_id)
    result["premise_ids"] = _string_list(
        result["premise_ids"], "%s premise_ids" % edge_id,
        identifiers=True)
    _require(set(result["premise_ids"]) <= premise_ids, "EDG8",
             "%s names an unknown premise" % edge_id)
    result["consumers"] = _string_list(
        result["consumers"], "%s consumers" % edge_id, identifiers=True)
    _string(result["rationale"], "%s rationale" % edge_id)
    return result


def _run_assay(value, edge_by_id):
    fields = {
        "id", "case", "edge_id", "claim_kind", "direction", "scope",
        "transport_attributes", "expected_verdict",
    }
    _exact_fields(value, fields, "assay")
    assay = dict(value)
    assay_id = _stable_id(assay["id"], "assay.id")
    _require(assay["case"] in tuple("ABCDEFGH"), "ASY1",
             "%s has unknown adversarial case" % assay_id)
    _require(assay["edge_id"] in edge_by_id, "ASY2",
             "%s names an unknown edge" % assay_id)
    claim_kind = assay["claim_kind"]
    _require(claim_kind in set(K.CLAIM_KINDS) | _CUSTOM_CLAIMS, "ASY3",
             "%s has unknown claim kind" % assay_id)
    _require(assay["direction"] in K.DIRECTIONS, "ASY4",
             "%s has unknown direction" % assay_id)
    _require(assay["scope"] is None or isinstance(assay["scope"], str),
             "ASY5", "%s scope is malformed" % assay_id)
    attributes = assay["transport_attributes"]
    _require(isinstance(attributes, dict) and
             set(attributes) <= _TRANSPORT_ATTRIBUTE_FIELDS, "ASY6",
             "%s has unknown transport attributes" % assay_id)
    _require(assay["expected_verdict"] in
             {LICENSED, REFUSED, INEXPRESSIBLE}, "ASY7",
             "%s has unknown expected verdict" % assay_id)

    edge = edge_by_id[assay["edge_id"]]
    if claim_kind in _CUSTOM_CLAIMS:
        verdict = INEXPRESSIBLE
        reason = "current GP has no dimension/rank-credit claim kind"
    elif edge["relation"] in {OUT_OF_KERNEL, K.UNTYPED}:
        verdict = REFUSED
        reason = "%s edge fails closed" % edge["relation"]
    elif edge["relation"] == DEFINITIONAL:
        verdict = LICENSED
        reason = "the source and target are definitionally the same object"
    else:
        kwargs = dict(attributes)
        if assay["scope"] is not None:
            kwargs["scope"] = assay["scope"]
        ruling = K.transport(edge["relation"], assay["direction"],
                             claim_kind, **kwargs)
        verdict = LICENSED if ruling.licensed else REFUSED
        reason = ruling.reason
    _require(verdict == assay["expected_verdict"], "ASY8",
             "%s expected %s but current semantics returned %s: %s" %
             (assay_id, assay["expected_verdict"], verdict, reason))
    assay["actual_verdict"] = verdict
    assay["reason"] = reason
    return assay


def compile_ledger(value):
    root_fields = {
        "schema", "campaign", "source_commit", "sources", "objects",
        "authorities", "premises", "edges", "assays", "non_goals",
        "stop_conditions",
    }
    _exact_fields(value, root_fields, "ledger input")
    _require(value["schema"] == INPUT_SCHEMA, "ROOT1",
             "unsupported ledger input schema")
    _string(value["campaign"], "campaign")
    _require(isinstance(value["source_commit"], str) and
             re.match(r"^[0-9a-f]{40}$", value["source_commit"]), "ROOT2",
             "source_commit is not a full git object id")

    sources = [_normalize_source(item) for item in value["sources"]]
    source_by_id = _indexed(sources, "source")
    objects = [_normalize_object(item, set(source_by_id))
               for item in value["objects"]]
    object_by_id = _indexed(objects, "object")

    # Authorities refer to endpoints but premises may refer back to authorities,
    # so normalize the authority identities first and validate premise links in
    # the second pass.
    raw_authority_ids = {
        _stable_id(item.get("id"), "authority.id")
        for item in value["authorities"]
    }
    _require(len(raw_authority_ids) == len(value["authorities"]), "ID2",
             "authority repeats an id")
    authorities = [
        _normalize_authority(item, set(source_by_id), set(object_by_id))
        for item in value["authorities"]
    ]
    authority_by_id = _indexed(authorities, "authority")
    premises = [_normalize_premise(item, raw_authority_ids)
                for item in value["premises"]]
    premise_by_id = _indexed(premises, "premise")
    for authority in authorities:
        _require(set(authority["premise_ids"]) <= set(premise_by_id), "AUT5",
                 "%s names an unknown premise" % authority["id"])

    edges = [_normalize_edge(item, set(object_by_id), authority_by_id,
                             set(premise_by_id))
             for item in value["edges"]]
    edge_by_id = _indexed(edges, "edge")
    assays = [_run_assay(item, edge_by_id) for item in value["assays"]]
    assay_by_id = _indexed(assays, "assay")
    _require({item["case"] for item in assays} == set("ABCDEFGH"), "ASY9",
             "the ledger must exercise every adversarial case A-H")

    non_goals = _string_list(value["non_goals"], "non_goals")
    stop_conditions = _string_list(value["stop_conditions"], "stop_conditions")
    for records in (sources, objects, authorities, premises, edges, assays):
        records.sort(key=lambda item: item["id"])

    unbound = [edge["id"] for edge in edges
               if edge["status"] in {"LANDED", "DEFINITIONAL"}
               and edge["authority_id"] is None]
    out_of_kernel = [edge["id"] for edge in edges
                     if edge["relation"] == OUT_OF_KERNEL]
    return {
        "schema": SCHEMA,
        "authority": AUTHORITY,
        "graph_effect": GRAPH_EFFECT,
        "campaign": value["campaign"],
        "source_commit": value["source_commit"],
        "input_fingerprint": fingerprint(value),
        "sources": sources,
        "objects": objects,
        "authorities": authorities,
        "premises": premises,
        "edges": edges,
        "assays": assays,
        "summary": {
            "objects": len(object_by_id),
            "edges": len(edge_by_id),
            "formal_authorities": len(authority_by_id),
            "assays": len(assay_by_id),
            "licensed": sum(item["actual_verdict"] == LICENSED
                            for item in assays),
            "refused": sum(item["actual_verdict"] == REFUSED
                           for item in assays),
            "inexpressible": sum(item["actual_verdict"] == INEXPRESSIBLE
                                 for item in assays),
            "out_of_kernel_edges": out_of_kernel,
            "unbound_landed_edges": unbound,
        },
        "non_goals": non_goals,
        "stop_conditions": stop_conditions,
        "native_bindings_checked": [],
    }


def check_native_bindings(report, native_root=NATIVE_ROOT):
    native_root = Path(native_root)
    completed = subprocess.run(
        ["git", "-c", "safe.directory=%s" % native_root.as_posix(),
         "-C", str(native_root), "rev-parse", "HEAD"],
        capture_output=True, text=True, timeout=10, check=False)
    _require(completed.returncode == 0, "BND1",
             "cannot read the bound JC git commit")
    _require(completed.stdout.strip() == report["source_commit"], "BND2",
             "JC source commit changed")

    source_by_id = {item["id"]: item for item in report["sources"]}
    checked = []
    texts = {}
    for source in report["sources"]:
        path = native_root / source["path"]
        _require(path.is_file(), "BND3",
                 "bound source is absent: %s" % source["path"])
        _require(_sha256(path) == source["sha256"], "BND4",
                 "bound source digest changed: %s" % source["path"])
        texts[source["id"]] = path.read_text(encoding="utf-8")
        checked.append(source["id"])
    for authority in report["authorities"]:
        _require(authority["source_id"] in source_by_id, "BND5",
                 "formal authority source is not bound")
        _require(authority["source_contains"] in texts[authority["source_id"]],
                 "BND6", "Lean declaration is absent: %s" %
                 authority["declaration"])
    report["native_bindings_checked"] = sorted(checked)
    return report


def verify_fixture(path=DEFAULT_FIXTURE, check_bindings=False,
                   native_root=NATIVE_ROOT):
    value = json.loads(Path(path).read_text(encoding="utf-8"))
    report = compile_ledger(value)
    if check_bindings:
        check_native_bindings(report, native_root=native_root)
    return report


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", type=Path, default=DEFAULT_FIXTURE)
    parser.add_argument("--check-native-bindings", action="store_true")
    parser.add_argument("--compact", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = verify_fixture(
            args.fixture, check_bindings=args.check_native_bindings)
        print(canonical_json(report, pretty=not args.compact), end="")
        return 0
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        print(canonical_json({"status": "REFUSED", "error": str(exc)}),
              end="")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
