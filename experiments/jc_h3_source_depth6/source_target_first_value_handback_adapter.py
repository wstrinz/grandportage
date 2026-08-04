#!/usr/bin/env python3
"""Project the gauge-aware first source-target value seam into frontier/v1.

The receipt does not close the old coefficient-map request outright.  It
splits it into a closed, exact sigma-top partial map and a smaller open
remainder.  All concrete symbolic identities stay native and digest-bound.
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
FIXTURE = ROOT / "fixtures" / "jc_source_depth6" / "source_target_first_value_handback_v1.json"
REVIEW_RECEIPT = ROOT / "review" / "jc-h3-source-target-first-value-frontier-v1.json"
SCHEMA = "gp-jc-h3-source-target-first-value-handback/v1"
SCOPE = "JC.H3.SOURCE.TARGET_PAIR.SEAM"
PARENT = "JC.H3.SOURCE.TARGET_PAIR_TO_NORMALIZED_LAURENT_ROOT"
PARTIAL = "JC.H3.SOURCE.SIGMA_TOP_FACE_VALUES"
REMAINDER = "JC.H3.SOURCE.REMAINING_COEFFICIENT_MAP"


class FirstValueHandbackError(ValueError):
    """The native seam or its authority boundary drifted."""


def require(condition, check_id, message):
    if not condition:
        raise FirstValueHandbackError("%s: %s" % (check_id, message))


def normalized_sha256(path):
    return hashlib.sha256(Path(path).read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def load_fixture(path=FIXTURE):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def validate_handback_value(value):
    require(value.get("schema") == SCHEMA, "H1", "schema changed")
    require(value.get("binding_digest_algo") == "sha256-lf-normalized",
            "H2", "binding convention changed")
    seam = value.get("seam", {})
    require(seam.get("prior_parent_status") == "UNMATERIALIZED_OPEN", "S1",
            "old parent status changed")
    require(seam.get("partial_status") == "SIGMA_TOP_FACE_PARTIALLY_MATERIALIZED" and
            seam.get("remaining_status") == "OPEN_REMAINING_COEFFICIENT_MAP", "S2",
            "partial/remainder split changed")
    require(seam.get("direction") == "forward necessary consequence only", "S3",
            "implication direction widened")
    require(seam.get("checks") == 41 and seam.get("mutation_refusals") == 8,
            "S4", "native replay count changed")
    require(seam.get("ratios") == {"Q_(8,1)/p": "5/3",
                                   "Q_(1,2)/p^2": "5/9",
                                   "c_B/p^3": "5/3"}, "S5", "ratio data changed")
    require(seam.get("p_nonzero") is True and
            seam.get("gauge_free_value") == {"coordinate": "covered P_(3,0)",
                                              "value": 0},
            "S6", "first necessary values changed")
    require(seam.get("row6_cross_check") == "c_B/27 = 5*p^3/81", "S7",
            "row-6 cross-check changed")
    for key in ("reverse_lift_licensed", "source_sufficiency_licensed",
                "pair_existence_licensed", "r5_licensed", "r7_licensed",
                "h3_licensed"):
        require(seam.get(key) is False, "S8", key + " was promoted")
    boundary = value.get("authority_boundary", "")
    require("does not construct a pair" in boundary and
            "does not" in boundary and "source sufficiency" in boundary,
            "S9", "authority boundary lost nonclaims")
    return value


def check_native_bindings(value, native_root=NATIVE_ROOT):
    for name, expected in value["source_bindings"].items():
        path = Path(native_root) / name
        require(path.exists(), "B1", "native binding missing: " + name)
        require(normalized_sha256(path) == expected, "B2",
                "native binding drifted: " + name)


def _item(identifier, proposition, status, *, state, evidence=(), replacement_ids=(),
          next_artifact=None):
    result = {
        "id": identifier,
        "proposition": proposition,
        "status": status,
        "frontier_state": state,
        "scope": {"id": SCOPE,
                  "description": "the source-derived target-pair coefficient seam in the covered psi2 frame"},
        "exports_to_scopes": [], "premises": [], "blocked_downstream": [],
        "superseding_evidence": list(evidence),
        "smallest_next_artifact": next_artifact,
        "estimated_cost": None, "potential_impact": [],
    }
    if replacement_ids:
        result["replacement_ids"] = list(replacement_ids)
    return result


def frontier_input(value):
    validate_handback_value(value)
    seam = value["seam"]
    items = [
        _item(PARENT,
              "The old unmaterialized coefficient-map request is resolved into an exact gauge-aware sigma-top map and a named remaining coefficient-map obligation.",
              "RESOLVED_TO_PARTIAL_VALUE_AND_REMAINDER", state="CLOSED",
              evidence=("678675e native first-value certificate",),
              replacement_ids=(PARTIAL, REMAINDER)),
        _item(PARTIAL,
              "The covered psi2 sigma-top faces have ratios Q_(8,1)/p=5/3, Q_(1,2)/p^2=5/9, c_B/p^3=5/3; p is nonzero and covered P_(3,0)=0.",
              seam["partial_status"], state="CLOSED",
              evidence=("678675e 41-check forward necessary certificate",)),
        _item(REMAINDER,
              "Materialize the remaining source-derived coefficient map from the covered target pair to normalized Laurent-root data beyond the sigma-top partial map.",
              seam["remaining_status"], state="OPEN",
              next_artifact={"description": "complete the finite sigma descent or emit the next source-to-root coefficient transport with torus-character bookkeeping"}),
    ]
    require(items[0]["replacement_ids"] == [PARTIAL, REMAINDER], "F1",
            "parent split changed")
    return {"schema": "frontier-input/v1", "items": items, "discharges": [],
            "sources": [{"commit": value["jc_commit"],
                         "path": "d2_plane_72_108/f2_h3_source_target_pair_first_value_manifest.json",
                         "sha256": value["source_bindings"]["f2_h3_source_target_pair_first_value_manifest.json"],
                         "verdict": "FIRST_VALUE_MATERIALIZED_AS_TORUS_INVARIANT_RATIOS"}],
            "bound_source_names": sorted(value["source_bindings"])}


def build_report(value):
    document = frontier_input(copy.deepcopy(value))
    report = F.build(document["items"], document["discharges"], document["sources"])
    report["consumer"] = "jc-h3-source-target-first-value-handback"
    report["source_authority_ceiling"] = "FORWARD_GAUGE_AWARE_COEFFICIENT_SEAM_ONLY"
    seam = value["seam"]
    report["evidence_envelope"] = EV.EvidenceEnvelope(
        schema=SCHEMA,
        context=EV.AffineContext(characteristic=0,
            coefficient_domain="covered psi2 source-target coefficient seam",
            point_universe=None, ring_vars=()),
        source_bindings=tuple(EV.SourceBinding(name, "sha256:" + digest)
                              for name, digest in sorted(value["source_bindings"].items())),
        checked_proposition=("the covered sigma-top coefficient ratios and the gauge-free necessary zero P_(3,0)=0 are exact forward consequences"),
        licenses=("gauge_aware_sigma_top_coefficient_ratios", "P_3_0_zero_necessary_condition", "row6_fringe_value_cross_check"),
        outstanding_premises=("remaining coefficient map", "R5", "R7 scalarity", "reverse lifting", "source sufficiency"),
        graph_effect=EV.GRAPH_EFFECT_NONE,
        authority_boundary=value["authority_boundary"],
        certificate_payload={"partial_status": seam["partial_status"],
                             "remaining_status": seam["remaining_status"],
                             "gauge_free_value": seam["gauge_free_value"],
                             "source_sufficiency_licensed": seam["source_sufficiency_licensed"]},
    ).as_dict()
    return report


def review_receipt(report):
    return {"schema": "gp-jc-h3-source-target-first-value-frontier-review/v1",
            "projection_schema": report["schema"], "authority": report["authority"],
            "graph_effect": report["graph_effect"], "consumer": report["consumer"],
            "history": report["history"], "source_authority_ceiling": report["source_authority_ceiling"],
            "open_items": report["open_items"], "item_observations": F.item_observations(report),
            "evidence_envelope": report["evidence_envelope"]}


def emit_review_receipt(receipt, path=REVIEW_RECEIPT):
    path = Path(path); path.parent.mkdir(parents=True, exist_ok=True)
    payload = F.canonical_json(receipt).encode("utf-8")
    handle, temporary = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=str(path.parent))
    try:
        with os.fdopen(handle, "wb") as stream:
            stream.write(payload); stream.flush(); os.fsync(stream.fileno())
        os.replace(temporary, path)
    except BaseException:
        try: os.unlink(temporary)
        except FileNotFoundError: pass
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
        if args.check_native_bindings: check_native_bindings(value, args.native_root)
        report = build_report(value)
        if args.emit:
            print(json.dumps({"path": str(REVIEW_RECEIPT),
                              "sha256_lf_normalized": emit_review_receipt(review_receipt(report))},
                             indent=2, sort_keys=True))
        else: print(F.canonical_json(report), end="")
        return 0
    except (FirstValueHandbackError, F.FrontierError, OSError, json.JSONDecodeError) as exc:
        print(json.dumps({"schema": SCHEMA, "verdict": "REFUSED", "error": str(exc)}, sort_keys=True))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
