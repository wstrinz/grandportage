#!/usr/bin/env python3
"""Compile the JC low-jet pin-ablation handback into ``frontier/v1``.

The native certificates remain authoritative for their algebra.  This adapter
binds their exact bytes, checks the scope-bearing fields, and exposes only a
derived research frontier with graph effect NONE.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from grandportage import frontier as FRONT


ROOT = Path(__file__).resolve().parents[2]
NATIVE_ROOT = ROOT.parent / "math-stuff"
LANE = Path("d2_plane_72_108")
SOURCES = (
    {
        "commit": "6e692d2ec0dc4485489cf690f756c70d88aa5e91",
        "path": (LANE / "f2_h3_joint_low_jet_stratification_certificate.json").as_posix(),
        "sha256": "e2a0078e77b96bb9d09db3fe869e58d70ee0e8e783b723b755af1d978fddf7d8",
        "verdict": "JOINT_ESCAPE_LOCUS_IS_ONE_HYPERPLANE",
    },
    {
        "commit": "8cdb4f1232c5387465300c0f5d6f257c14fb8d0a",
        "path": (LANE / "f2_h3_c22_exceptional_control_certificate.json").as_posix(),
        "sha256": "0cf394a76ed6497fd6910dbeb8acfb9a2c7f0cb53559bb6e2edca2ab16473039",
        "verdict": "C22_FACE_IDEAL_UNIT_UNIFORM",
    },
    {
        "commit": "e0377d86bf1fbe5bf49505ca60102d890b63416b",
        "path": (LANE / "f2_h3_c710_torus_normalization_audit_certificate.json").as_posix(),
        "sha256": "38213bfee4533d4e174a8543eb986d26d1298d7f3aa8930203a1b65ec40de571",
        "verdict": "AC_NORMALIZATION_REFUSED",
    },
    {
        "commit": "25e62b05f7dbb02a64f22a6bdd18be2d91f4d144",
        "path": (LANE / "GP_PIN_ABLATION_HANDBACK_2026_08_03.md").as_posix(),
        "sha256": "19627c9233eabf8a6f64bbd4cae259812fa97abd74ddf7a5499e001480f92492",
        "verdict": "PROMOTION_SPECIFICATION_GRAPH_EFFECT_NONE",
    },
)


class PinAblationError(ValueError):
    """The native handback or a scope-bearing certificate field drifted."""


def _require(condition, message):
    if not condition:
        raise PinAblationError(message)


def _sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def _source(root, name):
    return _load(root / LANE / name)


def verify_native(native_root=NATIVE_ROOT):
    native_root = Path(native_root)
    for source in SOURCES:
        path = native_root / Path(source["path"])
        _require(path.is_file(), "native source is absent: %s" % path)
        _require(_sha256(path) == source["sha256"],
                 "native source digest changed: %s" % source["path"])

    joint = _source(
        native_root, "f2_h3_joint_low_jet_stratification_certificate.json")
    verdicts = joint.get("verdicts", {})
    _require(verdicts.get("JOINT_ESCAPE_LOCUS_IS_ONE_HYPERPLANE") == "PROVED",
             "joint confinement verdict changed")
    _require(verdicts.get("GENERIC_JOINT_LINE_FACE_IDEAL_UNIT") == "PROVED",
             "generic joint-line exclusion verdict changed")
    _require(str(verdicts.get("JOINT_LINE_FULLY_DISCHARGED", "")).startswith(
        "NOT PROVED -- at most 130 exceptional values"),
        "finite joint-line remainder was hidden")
    _require(joint.get("line", {}).get("cofactor_resultant_degree") == 130,
             "joint cofactor resultant degree changed")
    _require(joint.get("checks") == {"passed": 22, "total": 22, "labels": joint["checks"]["labels"]},
             "joint producer checks are not 22/22")

    c22 = _source(
        native_root, "f2_h3_c22_exceptional_control_certificate.json")
    _require(c22.get("verdict") == "C22_FACE_IDEAL_UNIT_UNIFORM",
             "uniform c2_2 verdict changed")
    _require(c22.get("bezout", {}).get("normalised_identity") ==
             "a**5*c**2 = -36*t*a**2*c*D1 + (24/5)*E",
             "uniform c2_2 Bezout identity changed")
    _require(c22.get("n_checks") == 39 and
             all(check.get("ok") is True for check in c22.get("checks", [])),
             "uniform c2_2 producer checks are not 39/39")
    handback = (native_root / LANE /
                "GP_PIN_ABLATION_HANDBACK_2026_08_03.md").read_text(
                    encoding="utf-8")
    _require("(c2_1,c2_2)=(-(15/2)*t,(15/2)*t^2)" in handback,
             "explicit c2_1/c2_2 failure point changed")

    torus = _source(
        native_root, "f2_h3_c710_torus_normalization_audit_certificate.json")
    _require(torus.get("verdicts", {}).get("AC_NORMALIZATION_REFUSED") ==
             "REFUSED", "a=c=1 normalization refusal changed")
    _require(torus.get("character", {}).get("invariant") ==
             "J = a*c**(-3), w(J) = 0", "residual torus invariant changed")
    _require(torus.get("character", {}).get("orbit_of_normalisation") ==
             "{ a = c**3, c != 0 }", "normalization orbit changed")
    _require(torus.get("checks_passed") == torus.get("checks_total") == 34,
             "torus audit checks are not 34/34")
    return [source["path"] for source in SOURCES]


def _item(item_id, proposition, status, scope_id, scope, *, open_=False,
          blocked=(), evidence=(), next_artifact=None, impact=(),
          replacement_ids=None):
    item = {
        "id": item_id,
        "proposition": proposition,
        "status": status,
        "frontier_state": "OPEN" if open_ else "CLOSED",
        "scope": {"id": scope_id, "description": scope},
        "premises": [],
        "blocked_downstream": list(blocked),
        "superseding_evidence": list(evidence),
        "smallest_next_artifact": next_artifact,
        "estimated_cost": None,
        "potential_impact": list(impact),
    }
    if replacement_ids is not None:
        item["replacement_ids"] = list(replacement_ids)
    return item


def build(native_root=NATIVE_ROOT):
    checked = verify_native(native_root)
    shared_scope = (
        "b=0, R=c8_12-a*c^2=0, Delta=c4_5-a^2/4=0, "
        "15*t^3+1=0, inherited legal-chart guards; c7_9 remains free")
    evidence = [source["path"] for source in SOURCES[:3]]
    items = [
        _item(
            "JC.H3.C79.SOURCE.FACE81.PIN_ABLATION",
            "The ranked low-jet pin-ablation request returned exact scoped results and explicit refusal boundaries.",
            "RESOLVED_TO_SCOPED_RESULTS", "JC.H3.C79.PIN_ABLATION",
            shared_scope + "; ranked c2_2, joint c2_2/c7_10, c2_1, b, and R outcomes",
            evidence=evidence,
            impact=["replace the open artifact request with bounded result items"],
            replacement_ids=[
                "JC.H3.B.RELAXATION",
                "JC.H3.B0.SOURCE.EXCLUSION",
                "JC.H3.C21.RELAXATION",
                "JC.H3.C22.UNIFORM_SOURCE_EXCLUSION",
                "JC.H3.C22_C710.JOINT_CONFINEMENT",
                "JC.H3.C22_C710.NONNORMALIZED_TRANSPORT",
                "JC.H3.C22_C710.NORMALIZED_LINE.GENERIC_EXCLUSION",
                "JC.H3.C22_C710.NORMALIZED_LINE.RESULTANT_ROOTS",
                "JC.H3.DELTA.RELAXATION",
                "JC.H3.R.RELAXATION",
            ]),
        _item(
            "JC.H3.C22.UNIFORM_SOURCE_EXCLUSION",
            "Two shallow window faces generate the unit ideal uniformly in c2_2.",
            "CLOSED", "JC.H3.C22.UNIFORM",
            shared_scope + "; c2_1=c7_10=0 and a,c are legal chart units",
            evidence=[SOURCES[1]["path"]],
            impact=["enlarge exact source exclusion from c2_2=0 to every c2_2"]),
        _item(
            "JC.H3.C22_C710.JOINT_CONFINEMENT",
            "At c2_1=0 the only possible joint escape locus is c2_2=(15/2)*a*t^2*(2*c7_10+a^2*c), with no c2_2*c7_10 cross term.",
            "VERIFIED_CONFINEMENT", "JC.H3.C22_C710.JOINT",
            shared_scope + "; c2_1=0 with c2_2,c7_10,a,c free",
            evidence=[SOURCES[0]["path"]],
            impact=["confine joint low-jet source incidence to one exact hyperplane"]),
        _item(
            "JC.H3.C22_C710.NORMALIZED_LINE.GENERIC_EXCLUSION",
            "At a=c=1 both intercepts and the generic point of the joint line are source-excluded.",
            "VERIFIED_GENERIC_WITH_FINITE_REMAINDER",
            "JC.H3.C22_C710.NORMALIZED_LINE",
            shared_scope + "; a=c=1 on the exact joint confinement line",
            evidence=[SOURCES[0]["path"]],
            impact=["reduce the normalized joint line to a finite unresolved remainder"]),
        _item(
            "JC.H3.C22_C710.NORMALIZED_LINE.RESULTANT_ROOTS",
            "The at-most-130 roots of the exact degree-130 cofactor resultant remain unresolved.",
            "OPEN_FINITE_REMAINDER", "JC.H3.C22_C710.NORMALIZED.LINE.ROOTS",
            shared_scope + "; a=c=1 and c7_10 is a root of the recorded cofactor resultant",
            open_=True,
            blocked=["whole normalized joint-line source exclusion"],
            evidence=[SOURCES[0]["path"]],
            next_artifact={"description": "decide legality and source incidence at each exact resultant root without promoting generic-point evidence"},
            impact=["close the normalized joint line if every legal root is excluded"]),
        _item(
            "JC.H3.C22_C710.NONNORMALIZED_TRANSPORT",
            "The a=c=1 result does not automatically transport across the full (a,c) chart; the residual invariant is J=a*c^(-3).",
            "OPEN_TRANSPORT", "JC.H3.C22_C710.FULL_CHART",
            shared_scope + "; full legal (a,c) chart",
            open_=True,
            blocked=["full-chart joint-line source exclusion"],
            evidence=[SOURCES[2]["path"]],
            next_artifact={"description": "run a function-field argument over K(a,c), retaining the residual torus invariant"},
            impact=["transport only evidence proved equivariant beyond a=c^3"]),
        _item(
            "JC.H3.C21.RELAXATION",
            "The current two-generator certificate fails after relaxing c2_1; the explicit simultaneous zero is confinement, not a source witness.",
            "OPEN_EXPLICIT_CERTIFICATE_FAILURE", "JC.H3.C21_C22.JOINT",
            shared_scope + "; c7_10=0 and (c2_1,c2_2)=(-(15/2)*t,(15/2)*t^2)",
            open_=True,
            blocked=["source exclusion after c2_1 relaxation"],
            evidence=[SOURCES[1]["path"]],
            next_artifact={"description": "supply a different exact source-exclusion certificate or a genuine source-incidence witness at the explicit pair"},
            impact=["decide whether c2_1 is load-bearing beyond this failed pair"]),
        _item(
            "JC.H3.B0.SOURCE.EXCLUSION",
            "Actual-source incidence on the full b=0 branch remains undecided.",
            "OPEN", "JC.H3.B0.FULL", "the full b=0 branch",
            open_=True, blocked=["source-side H3 promotion on b=0"],
            next_artifact={"description": "a component-covering source exclusion not confined to the low-jet pinned wall"}),
        _item(
            "JC.H3.B.RELAXATION", "No conclusion was exported after relaxing b.",
            "OPEN", "JC.H3.B.OFF_WALL", "b is not fixed to zero",
            open_=True, next_artifact={"description": "an exact off-b=0 source packet"}),
        _item(
            "JC.H3.R.RELAXATION", "No conclusion was exported after relaxing R=c8_12-a*c^2.",
            "OPEN", "JC.H3.R.OFF_WALL", "R is not fixed to zero",
            open_=True, next_artifact={"description": "an exact off-R source packet"}),
        _item(
            "JC.H3.DELTA.RELAXATION", "No conclusion was exported after relaxing Delta=c4_5-a^2/4.",
            "OPEN", "JC.H3.DELTA.OFF_WALL", "Delta is not fixed to zero",
            open_=True, next_artifact={"description": "an exact off-Delta source packet"}),
    ]
    report = FRONT.build(items, sources=SOURCES)
    report["consumer"] = "jc-h3-low-jet-pin-ablation"
    report["native_bindings_checked"] = checked
    report["authority_ceiling"] = (
        "SCOPED_SOURCE_EXCLUSION_AND_CONFINEMENT_ONLY; NO SOURCE_SUFFICIENCY, "
        "COMPONENT_COVER, H3, OR (75,125)")
    report["live_replay_note"] = (
        "c2_2 checker passed 14/14; joint checker passed K0-K21 and refused "
        "K22 because a clean tracked Python source has CRLF checkout bytes; "
        "LF normalization matches its certificate binding")
    return report


def review_receipt(report):
    receipt = {
        key: report[key] for key in (
            "schema", "authority", "graph_effect", "consumer", "counts",
            "history", "sources", "open_items", "authority_ceiling",
            "live_replay_note")
    }
    receipt["item_observations"] = FRONT.item_observations(report)
    return receipt


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-root", type=Path, default=NATIVE_ROOT)
    parser.add_argument("--review", action="store_true")
    parser.add_argument("--compact", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = build(args.native_root)
        if args.review:
            report = review_receipt(report)
        print(FRONT.canonical_json(report, pretty=not args.compact), end="")
        return 0
    except (OSError, json.JSONDecodeError, ValueError) as exc:
        print(json.dumps({"status": "REFUSED", "error": str(exc)},
                         indent=2, sort_keys=True))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
