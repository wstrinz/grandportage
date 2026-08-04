#!/usr/bin/env python3
"""Verify the scoped JC depth-eight first-order fiber obstruction.

The frozen native composition receipt shows that c7_4 is solved on the
nine-relation locus and that the rotated scalar Omega_comb is nonzero at one
exact L-valued base witness.  Because the scalar is independent of the free
c8_5 coordinate, this excludes the entire c8_5 fiber at the first-order
depth-eight compatibility layer.

The verifier deliberately grants no claim about another base point, the whole
12-dimensional survivor, nonlinear lifting, actual-source membership, or H3.
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
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
NATIVE_ROOT = ROOT.parent / "math-stuff" / "d2_plane_72_108"
DEFAULT_FIXTURE = ROOT / "fixtures" / "jc_depth8_fiber" / "v1.json"
SCHEMA = "first_order_fiber_obstruction_v1"
EXPECTED_FIXTURE_SHA256 = (
    "070de7693f7d0b8044f3a91e3a00147407f474ff333d69a8cfa18b1028b6477c")

NATIVE_BINDINGS = {
    "f2_h3_straggler_zero_block_composition_certificate.json":
        "edd4e47668901c608f0f6a4f822c47bf5b01a9910c1ba46bdc9d45bf70103ebe",
    "f2_h3_straggler_zero_block_composition.py":
        "774e45c0783ffe3ceab9d838c42163aab78cf8d32509126475c81f897dafc744",
}

CONSUMED_BINDINGS = {
    "f2_h3_adjoint_recurrence_certificate.json":
        "9a3f3854b19d5efe988c660f51babbb7b71eca00cf99b2fd88c8b6168ccb7ba4",
    "f2_h3_depth8_cokernel_scaffold_certificate.json":
        "4bc4a9c65e7b97a462156f591b3aef28d59ac5fd1afcf7afd96fee15d3f5656a",
    "f2_h3_p_c6_1_depth7_composition_certificate.json":
        "3f40c20451c8dad364202e2b644f78403dc06761a5a2716fee2d8ae083f0a79e",
    "f2_h3_p_c6_1_receipt.json":
        "d971325110dcab38b25089c542c4cc5fd79ddb04342124ebf11c5d673ce4ee25",
    "f2_h3_p_c6_1_zero_block_certificate.json":
        "107a0b08b93eaf67ae50f2d57e43f97d4cf1ad0cc26696ab7a35272515c048ea",
    "f2_h3_s2_depth8_omega_certificate.json":
        "5c161962e201a1e76beea77229ce53c5610b60c4ee91e5da6a5585110b750bb2",
}

EXPECTED_OBJECT_DIGESTS = {
    "B74": "ae09002481231f4bf4ea9f6fd3c724ca7d36681696c85397dcd388edfa3e3aa5",
    "omega_comb": "a43adc79a9af1a6b184c2351628760f00c1d1cb6f8f410bd160b1a99ab8643a5",
    "verdict": "651adb4ef5ed386f4738826779e1b02afc5f23b169d7d2e4f8af7bd2cf389cbd",
    "combined_cokernel":
        "9cca515b9f7dad298e30faf8c765114f6751995c1b7e5e590a21a02f9d85edeb",
}


class FiberEvidenceError(ValueError):
    """The frozen receipt, first-order scope, or authority boundary drifted."""


def require(condition, check_id, message):
    if not condition:
        raise FiberEvidenceError("%s: %s" % (check_id, message))


def normalized_sha256(path):
    return hashlib.sha256(
        Path(path).read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def object_digest(value):
    canonical = json.dumps(value, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True,
                       ensure_ascii=True) + "\n").encode("utf-8")


def _element_nonzero(value, where):
    require(isinstance(value, list) and len(value) == 2, "E1",
            where + " is not an L = K + K*y element")
    coefficients = []
    for k_part in value:
        require(isinstance(k_part, list) and len(k_part) == 3 and
                all(isinstance(item, str) for item in k_part), "E2",
                where + " is not a cubic K-coordinate triple")
        try:
            parsed = [Fraction(item) for item in k_part]
        except (ValueError, ZeroDivisionError) as exc:
            raise FiberEvidenceError("E3: invalid exact coefficient in " +
                                     where) from exc
        require([str(item) for item in parsed] == k_part, "E4",
                where + " has a noncanonical rational coefficient")
        coefficients.extend(parsed)
    return any(coefficients)


def _validate_native(certificate):
    require(certificate.get("id") ==
            "f2_h3_straggler_zero_block_composition" and
            certificate.get("schema_version") == 1, "N1",
            "native certificate identity or schema changed")
    require(certificate.get("bindings") == CONSUMED_BINDINGS, "N2",
            "composition dependency binding changed")
    require(certificate.get("layer") == (
        "actual-source derivative recurrence x zero-block composition, "
        "conditional on P1..P5, S2, the pin and H8; value_c6_1 affinity "
        "in the heavies is exact; depth-8 row dependence on (c7_4, c8_5) "
        "is first-order (the adjoint lane's layer)"), "N3",
        "native layer or conditionality changed")
    pin = certificate.get("pin_semantics", {})
    require(pin == {
        "field": "K = QQ[t]/(15*t**3 + 1); L = K[y]/(y**2 - d), the "
                 "composition certificate's explicit quadratic extension",
        "modulus": "15*t**3 + 1",
    }, "N4", "coefficient field or point universe changed")

    operator = certificate.get("combined_operator", {})
    require(operator.get("columns") ==
            ["c9_6", "c7_3", "c8_5", "c7_4"] and
            operator.get("rank_at_witness") == 4 and
            operator.get("B85") == (
                "15*c5_7*t**2 (single monomial; unit on the scaffold guard "
                "c5_7 != 0)"), "N5", "combined operator or unit guard changed")
    require("SOLVED on the nine-relation locus" in
            operator.get("c7_4_status", "") and
            "NOT a legal rescue direction" in
            operator.get("c7_4_status", ""), "N6",
            "c7_4 was widened back into a free rescue direction")
    cokernel = certificate.get("combined_cokernel", {})
    components = cokernel.get("components", {})
    require(set(components) == {"nu1p", "nu2p", "nu3p", "nu5p"} and
            all("c8_5" not in record.get("sparse", {}).get("symbols", [])
                for record in components.values()), "N6A",
            "rotated obstruction gained forbidden fiber-coordinate dependence")

    verdict = certificate.get("verdict", {})
    require(verdict == {
        "c7_4_rescue_survives": False,
        "cokernel_rotated": True,
        "depth8_compatibility_reinstated": True,
        "depth9_additive_pair_authorized": False,
        "fiber_statement": "the pointwise Omega_8 non-extension extends to "
            "the ENTIRE free c8_5 fiber of the landed L-witness, at first "
            "order in the depth-8 rows",
        "omega_comb_nonzero_at_witness": True,
        "open": "Omega_comb on the rest of the 12-dimensional nine-relation "
            "locus; the Galois conjugate without replay; component-level "
            "claims; source sufficiency; H3",
    }, "N7", "native scoped verdict changed")

    values = certificate.get("witness_values", {})
    require(_element_nonzero(values.get("omega_comb"), "Omega_comb"), "N8",
            "Omega_comb is zero at the landed witness")
    require(_element_nonzero(values.get("B74"), "B74") and
            _element_nonzero(values.get("B85"), "B85") and
            _element_nonzero(values.get("det4_extended"), "det4"), "N9",
            "a required witness pivot or rank determinant vanished")

    actual_digests = {
        "B74": object_digest(operator.get("B74_sparse")),
        "omega_comb": object_digest(values.get("omega_comb")),
        "verdict": object_digest(verdict),
        "combined_cokernel": object_digest(cokernel),
    }
    require(actual_digests == EXPECTED_OBJECT_DIGESTS, "N10",
            "load-bearing sparse object or scope statement changed")
    return {
        "omega_comb_nonzero": True,
        "combined_rank": 4,
        "free_fiber_coordinate": "c8_5",
        "solved_coordinate": "c7_4",
        "point_universe": "L",
    }


def _projection():
    return {
        "instance_id": "jc_h3_depth8_landed_L_witness_c8_5_fiber",
        "coefficient_domain": "K = QQ[t]/(15*t^3+1)",
        "point_universe": "L = K[y]/(y^2-d)",
        "semantic_layer": "FIRST_ORDER_DEPTH8_COMPATIBILITY",
        "base_scope": {
            "parent": "12-dimensional nine-relation survivor locus",
            "selected": "one exact landed L-valued base witness",
            "other_base_points": "OPEN",
            "galois_conjugate": "NOT_REPLAYED",
        },
        "fiber_scope": {
            "coordinate": "c8_5",
            "quantifier": "ALL_VALUES_IN_L",
            "dependent_coordinate": "c7_4",
            "dependent_status": "SOLVED_AFFINELY_FROM_ZERO_BLOCK",
            "compatible_first_order_fiber": "EMPTY",
        },
        "checked_premises": [
            "combined operator has rank 4 at the landed witness",
            "c7_4 is solved and is not an independent rescue direction",
            "Omega_comb is independent of c8_5 on the named fiber",
            "Omega_comb is exactly nonzero in L at the landed witness",
        ],
        "outstanding_premises": [
            "P1..P5", "S2", "15*t^3+1=0", "c5_7 != 0", "H8",
        ],
        "lean_backing": {
            "first_order": "fiberEmpty_of_base_obstruction",
            "nonlinear_bridge_not_instantiated":
                "nonlinearFiberEmpty_of_sound_linearization",
        },
        "licenses": [
            "no compatible first-order depth-8 point exists anywhere along "
            "the free c8_5 fiber over the one landed L-valued base witness",
            "the c7_4 rescue is unavailable on that exact fiber",
        ],
        "does_not_license": [
            "nonlinear nonextension without a separately checked sound "
            "linearization bridge",
            "the Galois-conjugate witness",
            "any other base direction or the full nine-relation locus",
            "component emptiness", "actual-source membership or exclusion",
            "source sufficiency", "H3", "a (75,125) verdict change",
            "depth-9 additive-pair authority", "graph claim authority",
        ],
        "graph_effect": "NONE",
    }


def build_fixture(native_root=NATIVE_ROOT):
    root = Path(native_root)
    bindings = {name: normalized_sha256(root / name)
                for name in sorted(NATIVE_BINDINGS)}
    require(bindings == dict(sorted(NATIVE_BINDINGS.items())), "B1",
            "native inputs drifted before freeze")
    certificate = json.loads((root /
        "f2_h3_straggler_zero_block_composition_certificate.json").read_text(
            encoding="utf-8"))
    _validate_native(certificate)
    return {
        "schema": SCHEMA,
        "binding_digest_algo": "sha256-lf-normalized",
        "source_bindings": bindings,
        "native_certificate": certificate,
        "projection": _projection(),
        "authority_boundary": (
            "The native exact checks plus the Lean fiber theorem establish "
            "first-order incompatibility along one entire c8_5 fiber. They "
            "do not establish nonlinear, other-base, component, source, H3, "
            "graph, or verdict authority."),
    }


def validate_fixture_value(fixture):
    require(set(fixture) == {"schema", "binding_digest_algo",
            "source_bindings", "native_certificate", "projection",
            "authority_boundary"}, "F1", "fixture shape changed")
    require(fixture["schema"] == SCHEMA and
            fixture["binding_digest_algo"] == "sha256-lf-normalized", "F2",
            "fixture schema or digest algorithm changed")
    require(fixture["source_bindings"] ==
            dict(sorted(NATIVE_BINDINGS.items())), "F3",
            "frozen native binding changed")
    require(fixture["projection"] == _projection(), "M1",
            "fiber scope, semantic layer, premise, or authority changed")
    checked = _validate_native(fixture["native_certificate"])
    return fixture, checked


def check_native_bindings(fixture, native_root=NATIVE_ROOT):
    root = Path(native_root)
    require(root.exists(), "B2", "sibling JC checkout is absent")
    for name, expected in fixture["source_bindings"].items():
        require((root / name).exists(), "B3", "native binding absent: " + name)
        require(normalized_sha256(root / name) == expected, "B4",
                "native binding changed: " + name)


def verify_fixture(path=DEFAULT_FIXTURE, check_bindings=False,
                   native_root=NATIVE_ROOT):
    raw = Path(path).read_bytes()
    if EXPECTED_FIXTURE_SHA256 is not None:
        require(hashlib.sha256(raw).hexdigest() == EXPECTED_FIXTURE_SHA256,
                "F4", "frozen fiber fixture digest changed")
    fixture, checked = validate_fixture_value(json.loads(raw.decode("utf-8")))
    if check_bindings:
        check_native_bindings(fixture, native_root)
    report = copy.deepcopy(fixture["projection"])
    report.update({
        "schema": SCHEMA,
        "verdict": "VERIFIED_CONDITIONAL_FIRST_ORDER_EMPTY_EXACT_BASE_FIBER",
        "checked_instance_premises": checked,
        "source_bindings": fixture["source_bindings"],
        "evidence_envelope": {
            "schema": SCHEMA,
            "checked_proposition": (
                "the first-order depth-8 compatibility model is empty along "
                "the entire c8_5 fiber over one exact landed L witness"),
            "licenses": fixture["projection"]["licenses"],
            "outstanding_premises": fixture["projection"][
                "outstanding_premises"],
            "graph_effect": "NONE",
            "authority_boundary": fixture["authority_boundary"],
        },
    })
    return report


def native_replay(native_root=NATIVE_ROOT):
    script = (Path(native_root) /
              "f2_h3_straggler_zero_block_composition.py")
    completed = subprocess.run(
        [sys.executable, str(script), "--quiet"], cwd=str(native_root),
        capture_output=True, text=True, timeout=120, check=False)
    require(completed.returncode == 0, "N11",
            "native composition replay failed: " + completed.stderr.strip())
    require("CHECKS: 24/24 pass" in completed.stdout and
            "Omega_comb != 0" in completed.stdout, "N12",
            "native replay summary changed")
    return {"verdict": "VERIFIED_NATIVE_24_OF_24", "graph_effect": "NONE"}


def _atomic_write(path, value, force=False):
    path = Path(path)
    if path.exists() and not force:
        raise FiberEvidenceError(
            "output exists; pass --force to replace it: %s" % path)
    payload = encoded(value)
    path.parent.mkdir(parents=True, exist_ok=True)
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
    parser.add_argument("--output", type=Path)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args(argv)
    if args.force and not (args.write_fixture or args.output):
        parser.error("--force requires --write-fixture or --output")
    try:
        if args.write_fixture:
            digest = _atomic_write(
                args.fixture, build_fixture(args.native_root), args.force)
            print(json.dumps({"fixture": str(args.fixture), "sha256": digest},
                             indent=2, sort_keys=True))
            return 0
        report = verify_fixture(
            args.fixture, args.check_native_bindings, args.native_root)
        if args.native_replay:
            report["native_replay"] = native_replay(args.native_root)
        if args.output:
            _atomic_write(args.output, report, args.force)
        else:
            print(json.dumps(report, indent=2, sort_keys=True))
        return 0
    except (FiberEvidenceError, OSError, ValueError, json.JSONDecodeError) as exc:
        print("REFUSED: %s" % exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
