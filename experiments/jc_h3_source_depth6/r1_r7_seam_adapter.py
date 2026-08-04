#!/usr/bin/env python3
"""Freeze the corrected JC R1--R7 source-seam authority frontier.

This adapter translation-validates three landed native manifests and projects
their exact authority boundary into a compact GP report. It creates no graph,
does not close the parent source obligation, and does not run native checkers
unless ``--native-replay`` is explicitly requested.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path

from grandportage import evidence as EV


ROOT = Path(__file__).resolve().parents[2]
NATIVE_ROOT = ROOT.parent / "math-stuff" / "d2_plane_72_108"
DEFAULT_FIXTURE = (
    ROOT / "fixtures" / "jc_source_depth6" / "r1_r7_seam_v1.json")
SCHEMA = "gp-jc-r1-r7-source-seam/v1"
PARENT_OBLIGATION = "target_pair_to_normalized_laurent_root"
PARENT_STATUS = "UNMATERIALIZED_OPEN"
GRAPH_EFFECT = EV.GRAPH_EFFECT_NONE
EXPECTED_FIXTURE_SHA256 = (
    "e8b849d772b0a06c1afea60870576930bcc70aef261420e086c8ac5768dde982")

NATIVE_BINDINGS = {
    "f2_original_pair_root_normalization_manifest.json":
        "4d930a9465f1e54d57bf4b5095c1ab0242e78a132e856c6f4e9fbfdffb79db09",
    "f2_original_pair_root_normalization.py":
        "117e0befbf0a195b85e2d11368f4085ffa0bfd650e410bbafb89fdd6e6adb89a",
    "f2_residual_y_bound_frame_manifest.json":
        "c62748d41f9cfe120990d2739eb963dba4306ebe4a4f03e21e157b380ec9e793",
    "f2_residual_y_bound_frame.py":
        "0953c6f42fd4d54e861b6a213fbdac168be4d49b0bfb1337633ad1ec31b34428",
    "f2_r6_shear_forcing_manifest.json":
        "d9c3926f74054c5febb47256626a772fe965d69d0391e55336abe854ddce35eb",
    "f2_r6_shear_forcing.py":
        "9002b3759c1341aa76e3b5ef5f7edfbc9e490d30ba6539fdad91f71a2a425e76",
    "f2_reduction_certificate.py":
        "5ff3faf543ba01e3e6e06f7e79d1120c667fac2836ed27de1a5c41dae07d9da0",
}

NATIVE_MANIFESTS = {
    "normalization": "f2_original_pair_root_normalization_manifest.json",
    "frame": "f2_residual_y_bound_frame_manifest.json",
    "shear": "f2_r6_shear_forcing_manifest.json",
}

EXPECTED_SUBSTAGES = [
    ("R1_root_existence_normalization", "PROVED"),
    ("R2_depression_unit", "PROVED"),
    ("R3_monic_normalization", "CHECKED"),
    ("R4_grading_alignment", "PROVED"),
    ("R5_root_support_table", "CHECKED_PREMISE_BOUND"),
    ("R6_residual_window", "OPEN"),
    ("R7_ladder_coefficients_in_K", "INFERRED"),
]

R6_TYPED = {
    "branch_A": "REFUTED_EVERY_GAUGE_PREMISE_BOUND",
    "pair_positive_j": "FORCED",
    "Q_positive_j": "OPEN",
    "covered_point_1_2": "ACTUAL_NONZERO_LANDED_NORMALIZATION_ONLY",
    "missing_datum": "exact non-monomial eqq1 -> psi2 conversion",
    "premises": ["actual_pair", "source_polynomiality", "gap5"],
    "J": None,
}

OPEN_FRONTIER = [
    {
        "id": "R5",
        "status": "CHECKED_PREMISE_BOUND",
        "why_open": "selected monic depressed cubic face is an inherited premise",
    },
    {
        "id": "R6",
        "status": "OPEN_NONMONOMIAL_FRAME_CONVERSION",
        "why_open": R6_TYPED["missing_datum"],
    },
    {
        "id": "R7",
        "status": "INFERRED_UNBOUND_75_125_IDENTIFICATION",
        "why_open": "the cited source does not print the (75,125) identification",
    },
]


class R1R7SeamError(ValueError):
    """The frozen seam or its claimed authority has drifted."""


def require(condition, check_id, message):
    if not condition:
        raise R1R7SeamError("%s: %s" % (check_id, message))


def normalized_bytes(path):
    return Path(path).read_bytes().replace(b"\r\n", b"\n")


def normalized_sha256(path):
    return hashlib.sha256(normalized_bytes(path)).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True,
                       ensure_ascii=True) + "\n").encode("utf-8")


def _load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def _native_payloads(native_root=NATIVE_ROOT):
    return {
        key: _load(Path(native_root) / name)
        for key, name in NATIVE_MANIFESTS.items()
    }


def _validate_native_payloads(payloads):
    require(set(payloads) == set(NATIVE_MANIFESTS), "N1",
            "native manifest set changed")
    normalization = payloads["normalization"]
    frame = payloads["frame"]
    shear = payloads["shear"]
    require(normalization.get("schema") ==
            "jc-f2-original-pair-root-normalization/v1", "N2",
            "normalization schema changed")
    require(frame.get("schema") == "jc-f2-residual-y-bound-frame/v1", "N3",
            "frame schema changed")
    require(shear.get("schema") == "jc-f2-r6-shear-forcing/v1", "N4",
            "corrected shear schema changed")

    substages = [(item.get("id"), item.get("verdict"))
                 for item in normalization.get("substages", [])]
    require(substages == EXPECTED_SUBSTAGES, "N5",
            "R1--R7 native frontier changed")
    require(normalization.get("authority", {}).get(
        "strict_original_source_supported") is False, "N6",
        "normalization manifest promoted original-source support")
    require(frame.get("status") ==
            "R6_OPEN_LINEAR_TRANSPORT_REFUTED_NO_DERIVABLE_UNIVERSAL_J",
            "N7", "frame diagnosis changed")
    require(frame.get("dichotomy", {}).get("branch_B", {}).get("actual_J") ==
            "UNDETERMINED (NOT asserted infinite)", "N8",
            "frame manifest changed the actual residual's J status")

    expected_shear_status = (
        "BRANCH_A_REFUTED_PREMISE_BOUND__PAIR_POSITIVE_J_FORCED__"
        "Q_(1,2)_LANDED_NORMALIZATION_ONLY__RELOCATION_OPEN")
    require(shear.get("status") == expected_shear_status, "N9",
            "corrected shear status changed")
    bracket = shear.get("bracket_forcing", {})
    gauge = shear.get("gauge_enumeration", {})
    landed = shear.get("landed_normalization", {})
    require("J_P + J_Q >= 3" in bracket.get("forcing", ""), "N10",
            "pair-level positive-j forcing changed")
    require("PAIR-level" in bracket.get("claim", ""), "N11",
            "pair-level forcing scope was dropped")
    require(gauge.get("Q_side_relocation", "").startswith("OPEN"), "N12",
            "Q-side relocation was promoted")
    require(landed.get("scope") == "the landed normalization ONLY", "N13",
            "covered point (1,2) scope changed")
    require("ACTUAL nonzero" in landed.get("claim", ""), "N14",
            "landed (1,2) coefficient status changed")
    premise_text = " ".join(
        shear.get("authority", {}).get("PREMISE_CITED", []))
    require(all(token in premise_text for token in (
        "actual-pair", "source-polynomiality", "GAP-5")), "N15",
        "corrected shear premises changed")
    require(shear.get("branch_A_refutation", {}).get("J_supplied") is None,
            "N16", "corrected shear manifest supplied J")


def _projection():
    return {
        "parent_obligation": PARENT_OBLIGATION,
        "parent_status": PARENT_STATUS,
        "closed_substages": ["R1", "R2", "R3", "R4"],
        "open_frontier": copy.deepcopy(OPEN_FRONTIER),
        "R6": copy.deepcopy(R6_TYPED),
        "authority_ceiling": "conditional normalized-root data only",
        "graph_effect": GRAPH_EFFECT,
        "outstanding_premises": [
            "R5 selected monic depressed cubic face",
            "R6 exact non-monomial eqq1 -> psi2 conversion",
            "R6 Q-side relocation remains open",
            "R7 (75,125) identification is not printed",
            "GAP-5 source equivalence",
            PARENT_OBLIGATION,
        ],
        "refusals": [
            "original polynomial-pair membership",
            "source-image sufficiency",
            "reverse lift",
            "chart or branch coverage",
            "I4=I1=Im1=0",
            "H3 promotion",
            "(75,125) verdict change",
        ],
    }


def build_fixture(native_root=NATIVE_ROOT):
    payloads = _native_payloads(native_root)
    _validate_native_payloads(payloads)
    bindings = {
        name: normalized_sha256(Path(native_root) / name)
        for name in sorted(NATIVE_BINDINGS)
    }
    require(bindings == dict(sorted(NATIVE_BINDINGS.items())), "B1",
            "native source binding changed before freeze")
    return {
        "schema": SCHEMA,
        "binding_digest_algo": "sha256-lf-normalized",
        "correction_commits": ["fb18749", "d0257f9"],
        "source_bindings": bindings,
        "native_manifests": payloads,
        "projection": _projection(),
        "authority_boundary": (
            "R1--R4 are closed only inside the conditional normalized-root "
            "seam. R5 remains premise-bound, R6 lacks the exact non-monomial "
            "frame conversion, and R7 remains inferred. No graph, source, "
            "coverage, H3, or verdict authority is created."),
    }


def _validate_projection(projection):
    require(projection.get("parent_obligation") == PARENT_OBLIGATION and
            projection.get("parent_status") == PARENT_STATUS, "M9",
            "parent source obligation was promoted")
    require(projection.get("closed_substages") == ["R1", "R2", "R3", "R4"],
            "M1", "closed substage set changed")
    frontier = {item.get("id"): item for item in
                projection.get("open_frontier", [])}
    require(frontier.get("R6", {}).get("status") ==
            "OPEN_NONMONOMIAL_FRAME_CONVERSION" and
            projection.get("R6", {}).get("J") is None, "M1",
            "R6 was closed or reduced to supplying J")
    require(projection.get("R6", {}).get("Q_positive_j") == "OPEN", "M2",
            "Q-side positive-j support was promoted")
    require(projection.get("R6", {}).get("covered_point_1_2") ==
            "ACTUAL_NONZERO_LANDED_NORMALIZATION_ONLY", "M3",
            "covered point (1,2) escaped its landed normalization")
    require(projection.get("R6", {}).get("branch_A") ==
            "REFUTED_EVERY_GAUGE_PREMISE_BOUND" and
            projection.get("R6", {}).get("premises") ==
            ["actual_pair", "source_polynomiality", "gap5"], "M4",
            "branch-A refutation lost its premises")
    require(frontier.get("R7", {}).get("status") ==
            "INFERRED_UNBOUND_75_125_IDENTIFICATION", "M5",
            "R7 or the (75,125) identification was promoted")
    require(frontier.get("R5", {}).get("status") ==
            "CHECKED_PREMISE_BOUND", "M6", "R5 lost PREMISE_BOUND scope")
    require(projection.get("graph_effect") == GRAPH_EFFECT, "M7",
            "standalone seam report attempted graph authority")
    require("GAP-5 source equivalence" in
            projection.get("outstanding_premises", []), "M10",
            "GAP-5 source equivalence was omitted")
    require(projection.get("R6", {}).get("pair_positive_j") == "FORCED", "M2b",
            "pair-level positive-j forcing was dropped")
    require(projection.get("R6", {}).get("missing_datum") ==
            "exact non-monomial eqq1 -> psi2 conversion", "M1b",
            "R6 missing datum changed")


def validate_fixture_value(fixture):
    require(set(fixture) == {
        "schema", "binding_digest_algo", "correction_commits",
        "source_bindings", "native_manifests", "projection",
        "authority_boundary",
    }, "F1", "fixture shape changed")
    require(fixture["schema"] == SCHEMA, "F2", "fixture schema changed")
    require(fixture["binding_digest_algo"] == "sha256-lf-normalized", "F3",
            "binding digest algorithm changed")
    require(fixture["correction_commits"] == ["fb18749", "d0257f9"], "F4",
            "correction commit anchors changed")
    _validate_projection(fixture["projection"])
    require(fixture["source_bindings"] ==
            dict(sorted(NATIVE_BINDINGS.items())), "M8",
            "a frozen native binding digest drifted")
    _validate_native_payloads(fixture["native_manifests"])
    return fixture


def check_native_bindings(fixture, native_root=NATIVE_ROOT):
    root = Path(native_root)
    require(root.exists(), "B2", "sibling JC checkout is absent")
    for name, expected in fixture["source_bindings"].items():
        path = root / name
        require(path.exists(), "B3", "native binding is absent: " + name)
        require(normalized_sha256(path) == expected, "M8",
                "native binding changed: " + name)


def verify_fixture(path=DEFAULT_FIXTURE, check_bindings=False,
                   native_root=NATIVE_ROOT):
    path = Path(path)
    raw = path.read_bytes()
    if EXPECTED_FIXTURE_SHA256 is not None:
        require(hashlib.sha256(raw).hexdigest() == EXPECTED_FIXTURE_SHA256,
                "F5", "frozen R1--R7 fixture digest changed")
    fixture = validate_fixture_value(json.loads(raw.decode("utf-8")))
    if check_bindings:
        check_native_bindings(fixture, native_root)
    projection = copy.deepcopy(fixture["projection"])
    envelope = EV.EvidenceEnvelope(
        schema=SCHEMA,
        context=EV.AffineContext(
            characteristic=0,
            coefficient_domain="conditional characteristic-zero source seam",
            point_universe=None,
            ring_vars=(),
        ),
        source_bindings=tuple(
            EV.SourceBinding(name, "sha256:" + digest)
            for name, digest in sorted(fixture["source_bindings"].items())),
        checked_proposition=(
            "the corrected R1--R7 decomposition and R6 pair/Q/landed-point "
            "scopes match the three frozen native manifests"),
        licenses=(
            "R1_R4_closed_inside_conditional_normalized_root_seam",
            "R6_branch_A_refuted_every_gauge_premise_bound",
            "R6_pair_positive_j_forced_premise_bound",
            "R6_landed_point_1_2_actual_nonzero_only_in_landed_normalization",
        ),
        outstanding_premises=tuple(projection["outstanding_premises"]),
        graph_effect=GRAPH_EFFECT,
        authority_boundary=fixture["authority_boundary"],
        certificate_payload={
            "parent_obligation": PARENT_OBLIGATION,
            "closed_substages": projection["closed_substages"],
            "open_frontier": projection["open_frontier"],
            "R6": projection["R6"],
            "binding_digest_algo": fixture["binding_digest_algo"],
        },
    ).as_dict()
    projection.update({
        "schema": SCHEMA,
        "verdict": "VERIFIED_R1_R7_OPEN_FRONTIER",
        "binding_digest_algo": fixture["binding_digest_algo"],
        "source_bindings": fixture["source_bindings"],
        "evidence_envelope": envelope,
    })
    return projection


def native_replay(native_root=NATIVE_ROOT):
    root = Path(native_root)
    commands = [
        ("normalization", ["f2_original_pair_root_normalization.py", "--quiet"],
         "35/35 checks passed"),
        ("frame", ["f2_residual_y_bound_frame.py", "--quiet",
                   "--self-test-mutations"], "11 mutations refused"),
        ("shear", ["f2_r6_shear_forcing.py", "--quiet",
                   "--self-test-mutations", "--emit-certificate"],
         "21 mutations refused"),
    ]
    results = []
    for stage_id, argv, expected in commands:
        started = time.time()
        completed = subprocess.run(
            [sys.executable] + [str(root / argv[0])] + argv[1:],
            cwd=str(root), capture_output=True, text=True, timeout=300,
            check=False)
        require(completed.returncode == 0, "R1",
                "%s native replay failed: %s" %
                (stage_id, completed.stderr.strip()))
        require(expected in completed.stdout, "R2",
                "%s native replay summary changed" % stage_id)
        if stage_id == "shear":
            start = completed.stdout.find("{")
            require(start >= 0, "R3", "shear certificate JSON is absent")
            certificate = json.loads(completed.stdout[start:])
            require(certificate.get("status") ==
                    _native_payloads(root)["shear"].get("status"), "R4",
                    "emitted shear certificate status changed")
        results.append({
            "id": stage_id,
            "status": "VERIFIED",
            "seconds": round(time.time() - started, 3),
        })
    return {
        "verdict": "VERIFIED_NATIVE_R1_R7_REPLAY",
        "graph_effect": GRAPH_EFFECT,
        "stages": results,
    }


def write_fixture(path=DEFAULT_FIXTURE, native_root=NATIVE_ROOT, force=False):
    path = Path(path)
    if path.exists() and not force:
        raise R1R7SeamError("fixture exists; pass --force to replace it: %s" % path)
    value = build_fixture(native_root)
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = encoded(value)
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
    return hashlib.sha256(payload).hexdigest()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", type=Path, default=DEFAULT_FIXTURE)
    parser.add_argument("--native-root", type=Path, default=NATIVE_ROOT)
    parser.add_argument("--check-native-bindings", action="store_true")
    parser.add_argument("--native-replay", action="store_true")
    parser.add_argument("--write-fixture", action="store_true")
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args(argv)
    if args.force and not args.write_fixture:
        parser.error("--force requires --write-fixture")
    try:
        if args.write_fixture:
            digest = write_fixture(
                args.fixture, args.native_root, force=args.force)
            print(json.dumps({"fixture": str(args.fixture),
                              "sha256": digest}, indent=2, sort_keys=True))
            return 0
        report = verify_fixture(
            args.fixture, args.check_native_bindings, args.native_root)
        if args.native_replay:
            report["native_replay"] = native_replay(args.native_root)
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0
    except (R1R7SeamError, OSError, subprocess.SubprocessError,
            json.JSONDecodeError) as exc:
        print(json.dumps({"schema": SCHEMA, "verdict": "REFUSED",
                          "error": str(exc)}, indent=2, sort_keys=True),
              file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
