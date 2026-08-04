#!/usr/bin/env python3
"""Consume the bounded JC support-seam and generic-J handback.

This is a read-only frontier projection.  It deliberately keeps the
coefficient-value seam and the exceptional J-fibres open.  It uses the
existing EvidenceEnvelope and frontier/v1 primitives and creates no graph
event or general-purpose evidence vocabulary.
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
FIXTURE = ROOT / "fixtures" / "jc_source_depth6" / "support_seam_handback_v1.json"
REVIEW_RECEIPT = ROOT / "review" / "jc-h3-support-seam-frontier-v1.json"
SCHEMA = "gp-jc-h3-support-seam-handback/v1"
SCOPE_D6 = "JC.H3.D6.CONDITIONAL_NORMALIZED_ROOT"
SCOPE_PARENT = "JC.H3.SOURCE.TARGET_PAIR.SEAM"
SCOPE_GENERIC_J = "JC.H3.C22_C710.GENERIC_J_OFF_EXCEPTIONAL"
SCOPE_FULL_J = "JC.H3.C22_C710.FULL_CHART"
R7 = "JC.H3.D6.R7.75_125_IDENTIFICATION"
R7P = "JC.H3.D6.R7_PRIME.SIGMA_BUDGET"
R6 = "JC.H3.D6.R6.NONMONOMIAL_FRAME"
PARENT = "JC.H3.SOURCE.TARGET_PAIR_TO_NORMALIZED_LAURENT_ROOT"
EXCEPTIONAL = "JC.H3.C22_C710.EXCEPTIONAL_J_FIBERS"
GENERIC = "JC.H3.C22_C710.NONNORMALIZED_TRANSPORT.GENERIC_J"
FULL = "JC.H3.C22_C710.NONNORMALIZED_TRANSPORT"


class SupportHandbackError(ValueError):
    """The bounded handback changed its semantics or bindings."""


def require(condition, check_id, message):
    if not condition:
        raise SupportHandbackError("%s: %s" % (check_id, message))


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
    seam = value.get("support_seam", {})
    require(seam.get("support_status") == "MATERIALIZED_EXACT", "S1",
            "support-level result changed")
    require(seam.get("value_status") == "UNMATERIALIZED" and
            seam.get("parent_status") == "UNMATERIALIZED_OPEN", "S2",
            "coefficient-value seam was promoted")
    require(seam.get("r6_status") ==
            "DISCHARGED_PREMISE_FREE_AS_CONSUMED" and
            seam.get("r6_premises") == [], "S3",
            "R6 regained a ladder premise")
    require(seam.get("r7_prime_status") ==
            "PROVED_NATIVE_UNCONDITIONAL" and
            seam.get("r7_prime") ==
            "deg_sigma(lambda_k) <= 15 - 3*k at every carried slot", "S4",
            "R7 prime lost its unconditional native proof")
    require(seam.get("r7_status") ==
            "PREMISE_OPEN_NATIVE_ROUTE_NAMED", "S4b",
            "R7 scalarity was promoted or hidden")
    require(seam.get("five_normalized_rows_bound") is True, "S5",
            "five-row weld is absent")
    require(seam.get("authority_ceiling") ==
            "CONDITIONAL_NORMALIZED_ROOT_TO_DEPTH6_BOUNDARY_ONLY", "S6",
            "source authority ceiling changed")

    generic = value.get("generic_j", {})
    require(generic.get("verdict") ==
            "C710_DIVISOR_FACE_IDEAL_UNIT_GENERIC_IN_J", "J1",
            "generic-J verdict changed")
    require(generic.get("route_y_exceptional_degree") == 37 and
            generic.get("route_z_exceptional_degree") == 37, "J2",
            "finite exceptional degree changed")
    require(generic.get("exceptional_fiber_semantics") ==
            "UNDECIDED_FIBER_NOT_SOURCE_WITNESS", "J3",
            "an exceptional zero was promoted to a witness")
    require(generic.get("full_chart_status") ==
            "RESOLVED_TO_GENERIC_AND_FINITE_REMAINDER", "J4",
            "generic exclusion was promoted to all fibres")
    require(generic.get("source_witness_licensed") is False, "J5",
            "source-witness authority was invented")
    require(generic.get("all_fibers_licensed") is False, "J6",
            "all-fibre authority was invented")
    return value


def check_native_bindings(value, native_root=NATIVE_ROOT):
    for name, expected in value.get("source_bindings", {}).items():
        path = Path(native_root) / name
        require(path.exists(), "B1", "native binding missing: " + name)
        require(normalized_sha256(path) == expected, "B2",
                "native binding drifted: " + name)


def _item(identifier, proposition, status, scope_id, scope_description,
          premises=(), target=None, frontier_state=None, exports=(),
          evidence=(), next_artifact=None, replacements=()):
    result = {
        "id": identifier,
        "proposition": proposition,
        "status": status,
        "scope": {"id": scope_id, "description": scope_description},
        "exports_to_scopes": list(exports),
        "premises": [
            {"id": premise, "status": "OPEN"} for premise in premises
        ],
        "blocked_downstream": [],
        "superseding_evidence": list(evidence),
        "smallest_next_artifact": next_artifact,
        "estimated_cost": None,
        "potential_impact": [],
    }
    if target is not None:
        result["status_when_premises_discharged"] = target
    if frontier_state is not None:
        result["frontier_state"] = frontier_state
    if replacements:
        result["replacement_ids"] = list(replacements)
    return result


def frontier_input(value):
    validate_handback_value(value)
    source_names = sorted(value["source_bindings"])
    d6_desc = "the exact conditional normalized-root depth-six seam"
    items = [
        _item(
            R7,
            "The source construction supplies the landed (75,125) ladder identification.",
            "INFERRED_UNBOUND_75_125_IDENTIFICATION", SCOPE_D6, d6_desc,
            frontier_state="OPEN",
            next_artifact={"description": "derive or bind the source-owned ladder coefficient values"}),
        _item(
            R7P,
            "Every carried ladder scalar satisfies deg_sigma(lambda_k) <= 15-3k.",
            value["support_seam"]["r7_prime_status"], SCOPE_D6, d6_desc,
            exports=(SCOPE_D6,),
            evidence=("0b55e76 native sigma-budget induction",)),
        _item(
            R6,
            "The residual F starts below the eight-row normalized-root window.",
            value["support_seam"]["r6_status"], SCOPE_D6, d6_desc,
            evidence=("687ebd0 sigma/omega residual-window proof",
                      "0b55e76 premise-free native R7-prime induction"),
            replacements=(R7P,)),
        _item(
            PARENT,
            "The source-derived target-pair coefficient values map to the normalized Laurent-root coefficient data.",
            "UNMATERIALIZED_OPEN", SCOPE_PARENT,
            "the source-derived target-pair value seam",
            frontier_state="OPEN",
            next_artifact={"description": value["support_seam"]["first_missing_native_object"]}),
        _item(
            GENERIC,
            "The source-face ideal is the unit ideal on the invariant J-family off the explicit exceptional polynomials.",
            "CLOSED", SCOPE_GENERIC_J,
            value["generic_j"]["generic_scope"],
            evidence=("4e509af specialization-stable K[J][u] Bezout identities",)),
        _item(
            EXCEPTIONAL,
            "Decide the fibres where both generic-J elimination routes have exceptional right-hand side.",
            "OPEN_FINITE_REMAINDER", SCOPE_FULL_J,
            "the explicit exceptional J fibres on the inherited guarded stratum",
            frontier_state="OPEN",
            next_artifact={"description": "exact legality or exclusion certificate on the finite exceptional J fibres"}),
        _item(
            FULL,
            "The former nonnormalized-transport request is resolved into a proved generic-J exclusion and an explicit finite exceptional-fibre remainder.",
            value["generic_j"]["full_chart_status"], SCOPE_FULL_J,
            "the full legal residual-modulus chart",
            replacements=(GENERIC, EXCEPTIONAL)),
    ]
    # The generic item must never feed the full-chart item as a premise or via
    # an export.  The only open premise of the full result is the named finite
    # exceptional fibre set.
    require(items[4]["exports_to_scopes"] == [], "J7",
            "generic-J result exports to a wider scope")
    require(items[6].get("replacement_ids") == [GENERIC, EXCEPTIONAL],
            "J8", "transport request lost its generic/exceptional split")
    sources = [{
        "commit": value["jc_commits"]["support_seam"],
        "path": "d2_plane_72_108/f2_h3_source_target_pair_to_normalized_root_manifest.json",
        "sha256": value["source_bindings"]["f2_h3_source_target_pair_to_normalized_root_manifest.json"],
        "verdict": "PARTIAL_MAP_EXACT_AT_SUPPORT_LEVEL_UNMATERIALIZED_AT_VALUE_LEVEL",
    }, {
        "commit": value["jc_commits"]["r7prime_induction"],
        "path": "d2_plane_72_108/f2_r7prime_induction_manifest.json",
        "sha256": value["source_bindings"]["f2_r7prime_induction_manifest.json"],
        "verdict": "R7_PRIME_PROVED_NATIVE_UNCONDITIONAL__R6_PREMISE_FREE__R7_OPEN",
    }, {
        "commit": value["jc_commits"]["generic_j"],
        "path": "d2_plane_72_108/f2_h3_c710_generic_j_certificate.json",
        "sha256": value["source_bindings"]["f2_h3_c710_generic_j_certificate.json"],
        "verdict": value["generic_j"]["verdict"],
    }]
    return {"schema": "frontier-input/v1", "items": items,
            "discharges": [], "sources": sources,
            "bound_source_names": source_names}


def build_report(value, discharges=()):
    document = frontier_input(copy.deepcopy(value))
    report = F.build(document["items"], discharges, document["sources"])
    report["consumer"] = "jc-h3-support-seam-handback"
    report["source_authority_ceiling"] = value["support_seam"]["authority_ceiling"]
    report["evidence_envelope"] = EV.EvidenceEnvelope(
        schema=SCHEMA,
        context=EV.AffineContext(
            characteristic=0,
            coefficient_domain="conditional characteristic-zero source seam and K[J] guarded family",
            point_universe=None,
            ring_vars=(),
        ),
        source_bindings=tuple(
            EV.SourceBinding(name, "sha256:" + digest)
            for name, digest in sorted(value["source_bindings"].items())
        ),
        checked_proposition=(
            "R7 prime and the depth-six residual window are premise-free, "
            "R7 scalarity remains open, and the generic-J unit identities leave a named "
            "finite unresolved fibre set"),
        licenses=(
            "exact_root_support_windows_depths_2_through_23",
            "R7_prime_proved_native_unconditional",
            "R6_discharged_premise_free_as_consumed",
            "generic_J_source_exclusion_off_explicit_exceptional_set",
        ),
        outstanding_premises=(
            "R7 scalarity",
            "source-derived target-pair coefficient values",
            "exceptional J fibres",
        ),
        graph_effect=EV.GRAPH_EFFECT_NONE,
        authority_boundary=value["authority_boundary"],
        certificate_payload={
            "support_status": value["support_seam"]["support_status"],
            "value_status": value["support_seam"]["value_status"],
            "r6_status": value["support_seam"]["r6_status"],
            "generic_j_verdict": value["generic_j"]["verdict"],
            "exceptional_fiber_semantics": value["generic_j"]["exceptional_fiber_semantics"],
        },
    ).as_dict()
    return report


def review_receipt(report):
    return {
        "schema": "gp-jc-h3-support-seam-frontier-review/v1",
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
    parser.add_argument("--emit", action="store_true",
                        help="atomically write the derived review receipt")
    args = parser.parse_args(argv)
    try:
        value = validate_handback_value(load_fixture(args.fixture))
        if args.check_native_bindings:
            check_native_bindings(value, args.native_root)
        report = build_report(value)
        if args.emit:
            receipt = review_receipt(report)
            digest = emit_review_receipt(receipt)
            print(json.dumps({"path": str(REVIEW_RECEIPT),
                              "sha256_lf_normalized": digest},
                             indent=2, sort_keys=True))
        else:
            print(F.canonical_json(report), end="")
        return 0
    except (SupportHandbackError, F.FrontierError, OSError,
            json.JSONDecodeError) as exc:
        print(json.dumps({"schema": SCHEMA, "verdict": "REFUSED",
                          "error": str(exc)}, sort_keys=True))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
