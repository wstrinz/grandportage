#!/usr/bin/env python3
"""Project the exact all-J c7_10 closeout into the GP frontier.

This adapter consumes one native, digest-bound source-face closeout.  It
supersedes only the finite exceptional-J remainder created by the earlier
generic-J handback; it intentionally creates no source witness, source
sufficiency, full-b=0, H3, or coefficient-value authority.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import tempfile
from pathlib import Path

from grandportage import evidence as EV
from grandportage import frontier as F


ROOT = Path(__file__).resolve().parents[2]
NATIVE_ROOT = ROOT.parent / "math-stuff" / "d2_plane_72_108"
FIXTURE = ROOT / "fixtures" / "jc_source_depth6" / "c710_all_j_closeout_handback_v1.json"
REVIEW_RECEIPT = ROOT / "review" / "jc-h3-c710-all-j-closeout-frontier-v1.json"
SCHEMA = "gp-jc-h3-c710-all-j-closeout-handback/v1"
SCOPE = "JC.H3.C22_C710.FULL_CHART"
EXCEPTIONAL = "JC.H3.C22_C710.EXCEPTIONAL_J_FIBERS"
ALL_J = "JC.H3.C22_C710.ALL_J_SOURCE_FACE_EXCLUSION"


class CloseoutHandbackError(ValueError):
    """The bounded all-J handback changed scope, evidence, or authority."""


def require(condition, check_id, message):
    if not condition:
        raise CloseoutHandbackError("%s: %s" % (check_id, message))


def normalized_sha256(path):
    return hashlib.sha256(
        Path(path).read_bytes().replace(b"\r\n", b"\n")
    ).hexdigest()


def load_fixture(path=FIXTURE):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def validate_handback_value(value):
    require(value.get("schema") == SCHEMA, "H1", "schema changed")
    require(value.get("binding_digest_algo") == "sha256-lf-normalized",
            "H2", "binding digest convention changed")
    closeout = value.get("closeout", {})
    require(closeout.get("verdict") == "C710_DIVISOR_FACE_IDEAL_UNIT_ALL_J",
            "C1", "all-J verdict changed")
    require(closeout.get("wall") == "b = 0, R = 0, Delta = 0 (S2 substituted)",
            "C2", "wall scope changed")
    require(closeout.get("cross_section") == "c = 1, a = J != 0" and
            closeout.get("pins") == "c2_1 = c2_2 = 0", "C3",
            "torus or pin scope changed")
    require(closeout.get("closed_leaf") == "c710_divisor_exceptional_J" and
            closeout.get("prior_leaf_status") == "OPEN, <= 37 algebraic J" and
            closeout.get("current_leaf_status") == "EXCLUDED, zero J", "C4",
            "finite-remainder closure changed")
    require(closeout.get("terminal_guard") == "det5 = 0" and
            closeout.get("field_scope") ==
            "every characteristic-zero field extension on the declared guarded divisor",
            "C5", "guard or field scope changed")
    require(closeout.get("checks") == 29 and closeout.get("mutation_refusals") == 8,
            "C6", "native replay count changed")
    require(closeout.get("all_j_licensed") is True, "C7",
            "all-J closeout missing")
    for key in ("source_witness_licensed", "source_sufficiency_licensed",
                "global_b0_licensed", "sigma_kappa_nonzero_licensed"):
        require(closeout.get(key) is False, "C8", key + " was promoted")
    require("not source sufficiency" in value.get("authority_boundary", "") and
            "does not decide sigma_kappa_nonzero" in
            value.get("authority_boundary", ""), "C9",
            "authority boundary lost explicit nonclaims")
    return value


def check_native_bindings(value, native_root=NATIVE_ROOT):
    for name, expected in value.get("source_bindings", {}).items():
        path = Path(native_root) / name
        require(path.exists(), "B1", "native binding missing: " + name)
        require(normalized_sha256(path) == expected, "B2",
                "native binding drifted: " + name)


def _item(identifier, proposition, status, *, replacements=(),
          frontier_state=None, evidence=(), next_artifact=None):
    value = {
        "id": identifier,
        "proposition": proposition,
        "status": status,
        "scope": {
            "id": SCOPE,
            "description": "the declared guarded c7_10 divisor with c2_1=c2_2=0",
        },
        "exports_to_scopes": [],
        "premises": [],
        "blocked_downstream": [],
        "superseding_evidence": list(evidence),
        "smallest_next_artifact": next_artifact,
        "estimated_cost": None,
        "potential_impact": [],
    }
    if frontier_state is not None:
        value["frontier_state"] = frontier_state
    if replacements:
        value["replacement_ids"] = list(replacements)
    return value


def frontier_input(value):
    validate_handback_value(value)
    closeout = value["closeout"]
    items = [
        _item(
            ALL_J,
            "The source-face necessary ideal is the unit ideal at every legal invariant-J fibre of the declared c7_10 divisor.",
            "CLOSED",
            evidence=("8928f7a exact 29-check unit-pivot closeout",)),
        _item(
            EXCEPTIONAL,
            "The former finite exceptional-J remainder of the generic-J source exclusion is discharged by the exact all-J closeout.",
            "RESOLVED_BY_ALL_J_CLOSEOUT",
            replacements=(ALL_J,),
            evidence=("8928f7a: %s" % closeout["current_leaf_status"],)),
    ]
    require(items[1]["replacement_ids"] == [ALL_J], "F1",
            "finite remainder must resolve only to all-J closeout")
    return {
        "schema": "frontier-input/v1",
        "items": items,
        "discharges": [],
        "sources": [{
            "commit": value["jc_commit"],
            "path": "d2_plane_72_108/f2_h3_c710_exceptional_j_closeout_certificate.json",
            "sha256": value["source_bindings"][
                "f2_h3_c710_exceptional_j_closeout_certificate.json"],
            "verdict": closeout["verdict"],
        }],
        "bound_source_names": sorted(value["source_bindings"]),
    }


def build_report(value):
    document = frontier_input(copy.deepcopy(value))
    report = F.build(document["items"], document["discharges"],
                     document["sources"])
    report["consumer"] = "jc-h3-c710-all-j-closeout-handback"
    report["source_authority_ceiling"] = (
        "ON_WALL_S2_C710_DIVISOR_SOURCE_FACE_EXCLUSION_ONLY")
    closeout = value["closeout"]
    report["evidence_envelope"] = EV.EvidenceEnvelope(
        schema=SCHEMA,
        context=EV.AffineContext(
            characteristic=0,
            coefficient_domain="characteristic-zero K[J] guarded c7_10 divisor",
            point_universe=None,
            ring_vars=(),
        ),
        source_bindings=tuple(
            EV.SourceBinding(name, "sha256:" + digest)
            for name, digest in sorted(value["source_bindings"].items())
        ),
        checked_proposition=(
            "the finite generic-J remainder on the declared c7_10 divisor is "
            "empty because every candidate common root is the illegal det5 guard"),
        licenses=(
            "C710_divisor_source_face_exclusion_all_invariant_J",
            "finite_exceptional_J_remainder_discharged",
        ),
        outstanding_premises=(
            "source-derived target-pair coefficient values",
            "R7 scalarity",
            "sigma_kappa_nonzero",
            "joint c2_1/c2_2/c7_10 stratum",
            "full b=0 source branch",
        ),
        graph_effect=EV.GRAPH_EFFECT_NONE,
        authority_boundary=value["authority_boundary"],
        certificate_payload={
            "verdict": closeout["verdict"],
            "closed_leaf": closeout["closed_leaf"],
            "terminal_guard": closeout["terminal_guard"],
            "field_scope": closeout["field_scope"],
            "source_sufficiency_licensed": closeout["source_sufficiency_licensed"],
        },
    ).as_dict()
    return report


def review_receipt(report):
    return {
        "schema": "gp-jc-h3-c710-all-j-closeout-frontier-review/v1",
        "projection_schema": report["schema"],
        "authority": report["authority"],
        "graph_effect": report["graph_effect"],
        "consumer": report["consumer"],
        "history": report["history"],
        "source_authority_ceiling": report["source_authority_ceiling"],
        "open_items": report["open_items"],
        "item_observations": F.item_observations(report),
        "evidence_envelope": report["evidence_envelope"],
    }


def emit_review_receipt(receipt, path=REVIEW_RECEIPT):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = F.canonical_json(receipt).encode("utf-8")
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


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", type=Path, default=FIXTURE)
    parser.add_argument("--native-root", type=Path, default=NATIVE_ROOT)
    parser.add_argument("--check-native-bindings", action="store_true")
    parser.add_argument("--emit", action="store_true")
    args = parser.parse_args(argv)
    try:
        value = validate_handback_value(load_fixture(args.fixture))
        if args.check_native_bindings:
            check_native_bindings(value, args.native_root)
        report = build_report(value)
        if args.emit:
            digest = emit_review_receipt(review_receipt(report))
            print(json.dumps({"path": str(REVIEW_RECEIPT),
                              "sha256_lf_normalized": digest},
                             indent=2, sort_keys=True))
        else:
            print(F.canonical_json(report), end="")
        return 0
    except (CloseoutHandbackError, F.FrontierError, OSError,
            json.JSONDecodeError) as exc:
        print(json.dumps({"schema": SCHEMA, "verdict": "REFUSED",
                          "error": str(exc)}, sort_keys=True))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
