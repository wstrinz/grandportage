#!/usr/bin/env python3
"""Freeze and verify the conditional JC original-pair to E-system seam.

The native artifact is intentionally honest: it independently replays the
normalized Laurent-root to five reduced-row construction, while refusing to
claim the still-unmaterialized original-pair to normalized-root map. This
adapter binds that boundary to GP's existing exact five-row fixture.

It mints no graph authority. In particular it supplies no actual-source
membership, reverse lift, chart coverage, H3, or final verdict promotion.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from grandportage import evidence as EV


ROOT = Path(__file__).resolve().parents[2]
NATIVE_ROOT = ROOT.parent / "math-stuff" / "d2_plane_72_108"
NATIVE_MANIFEST = NATIVE_ROOT / "f2_original_pair_to_esystem_manifest.json"
NATIVE_VERIFIER = NATIVE_ROOT / "f2_original_pair_to_esystem_verify.py"
FACE_FIXTURE = (ROOT / "fixtures" / "jc_source_depth6" /
                "graded_face_extraction_v1.json")
DEFAULT_FIXTURE = (ROOT / "fixtures" / "jc_source_depth6" /
                   "original_pair_to_esystem_v1.json")

SCHEMA = "gp-jc-original-pair-to-esystem-seam/v1"
NATIVE_SCHEMA = "jc-f2-original-pair-to-esystem-manifest/v1"
EXPECTED_NATIVE_COMMIT = "d4a18b476b8bb8366e6c4505f03294f098dfb589"
EXPECTED_NATIVE_MANIFEST_SHA256 = (
    "44e96e9423a8e0187910774d6db9057f660445d8d7078af5516d787c181489dd"
)
EXPECTED_NATIVE_VERIFIER_SHA256 = (
    "080e0c398bec1b5d60ade3ed1fedfe02537c8720e94c3e4d7c5432c8adb8e08f"
)
EXPECTED_FACE_FIXTURE_SHA256 = (
    "6c8887034321884b6bb0aa7cd8cf04d90e472a36f4a6ba4035a53e7eda1aa8a1"
)
EXPECTED_FIXTURE_SHA256 = "970515c9548833ee253a64302b8aa5950849ad8cd54fa0bc375d22770156934a"

EXPECTED_ROWS = [
    {"row": 1, "terms": 39,
     "sha256": "2c10ee773d3f951460edebb2233ef6f1a95d8686f416e45395b112d64cb13d95"},
    {"row": 2, "terms": 38,
     "sha256": "705fc43f2dabfbd5bbde70ed7a6614ac8e740893f86beebc792fd5e3633a9e5c"},
    {"row": 3, "terms": 49,
     "sha256": "a2edcf00b3f3e6d93a8616dbd5fcb451a310ec86f00e9d239de6b831dc042c9b"},
    {"row": 4, "terms": 66,
     "sha256": "c6a4358296522f05950be2b0ccd3deca2f3fd029222a558888694de8d991d216"},
    {"row": 5, "terms": 81,
     "sha256": "bdd15bb06fdf12e06dd3365541f593d240712e94526be47b28d297f03e818ce8"},
]
EXPECTED_STAGES = {
    "source_to_target_hulls",
    "target_pair_to_normalized_laurent_root",
    "aligned_ladder_and_gauge",
    "finite_root_support",
    "normalized_root_to_five_rows",
}
REQUIRED_REFUSALS = {
    "complete original-pair to reduced-E-system edge",
    "actual polynomial-pair membership",
    "source-image sufficiency",
    "reverse lift",
    "chart coverage",
    "I4=I1=Im1=0",
    "H3 promotion",
    "(75,125) verdict change",
}


class SeamAdapterError(ValueError):
    """A frozen seam binding or authority boundary changed."""


def require(condition, message):
    if not condition:
        raise SeamAdapterError(message)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lf_normalized_sha256(path):
    return hashlib.sha256(
        path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def canonical(value):
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def sparse_digest(value):
    body = {
        "symbols": list(value["symbols"]),
        "terms": [[list(map(list, monomial)), coefficient]
                  for monomial, coefficient in value["terms"]],
    }
    return hashlib.sha256(
        json.dumps(body, separators=(",", ":")).encode("utf-8")).hexdigest()


def _load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def _stages(manifest):
    stages = manifest.get("stages")
    require(isinstance(stages, list), "native stages are absent")
    indexed = {stage.get("id"): stage for stage in stages}
    require(len(indexed) == len(stages), "native stage id is missing or duplicated")
    require(set(indexed) == EXPECTED_STAGES, "native stage inventory changed")
    return indexed


def _validate_manifest(manifest, face):
    require(manifest.get("schema") == NATIVE_SCHEMA,
            "native manifest schema changed")
    require(manifest.get("status") == "CONDITIONAL_EXACT_WITH_OPEN_UPSTREAM",
            "native conditional status changed")

    source = manifest.get("source_problem", {})
    require(source.get("coefficient_domain") ==
            "characteristic-zero field K", "source domain changed")
    require(source.get("ambient_ring") == "K[x,y]", "source ring changed")
    require(source.get("exact_pair_serialized") is False,
            "unmaterialized source pair was promoted")
    require(source.get("coefficient_variable_order") is None,
            "source coefficient order changed without an exact pair")

    stages = _stages(manifest)
    missing = stages["target_pair_to_normalized_laurent_root"]
    require(missing.get("status") == "UNMATERIALIZED_OPEN",
            "missing source map was promoted")
    require(missing.get("implementation") is None,
            "missing source map acquired an unbound implementation")
    require(missing.get("strict_replay_effect") == "FAIL",
            "strict source replay no longer fails closed")

    rows = stages["normalized_root_to_five_rows"]
    require(rows.get("relation") ==
            "exact_ambient_polynomial_equality_and_one_way_polynomiality_consequence",
            "reduced-row relation changed")
    require(rows.get("status") == "REPLAYABLE_CONDITIONAL_EXACT",
            "reduced-row replay status changed")
    require(rows.get("localization") == "none",
            "undeclared localization entered row derivation")

    contract = manifest.get("normalized_root_contract", {})
    require((contract.get("delta"), contract.get("m"), contract.get("n")) ==
            (3, 3, 5), "normalized-root delta/m/n changed")
    require((contract.get("source_window_rows"),
             contract.get("p_side_rows"),
             contract.get("output_rows")) == (8, 14, 5),
            "normalized-root row counts changed")
    require(contract.get("solved_variables") ==
            ["z%d" % exponent for exponent in range(10, 24)],
            "P-side solved-variable order changed")
    require(contract.get("invariant_substitution_downstream") == {
        "a4": "I4",
        "a1": "I1+4/5*a2*I4",
        "am1": "Im1+1/5*a2^2",
    }, "downstream invariant substitution changed")
    require(contract.get("pin_semantics") == {
        "relation": "15*t^3+1=0",
        "stage": "downstream weighted-face/source specialization",
        "part_of_reduced_row_derivation": False,
    }, "downstream pin semantics changed")

    require(manifest.get("root_supports") == face.get("root_supports"),
            "native and GP root-support tables differ")
    require(manifest.get("reduced_rows") == EXPECTED_ROWS,
            "native reduced-row commitments changed")

    face_rows = []
    for record in face.get("source_rows", []):
        require(len(record["sparse"]["terms"]) == record["terms"],
                "GP source-row term count changed")
        require(sparse_digest(record["sparse"]) == record["sha256"],
                "GP source-row sparse digest changed")
        face_rows.append({
            key: record[key] for key in ("row", "terms", "sha256")
        })
    require(face_rows == EXPECTED_ROWS,
            "native reduced rows do not weld to GP source rows")

    downstream = manifest.get("existing_downstream_bindings", {})
    require(downstream.get("gp_graded_face_fixture_sha256") ==
            EXPECTED_FACE_FIXTURE_SHA256,
            "native GP face-fixture binding changed")
    require(downstream.get("depth6_chain_canonical_sha256") ==
            face.get("chain_canonical_sha256"),
            "native depth-chain binding changed")

    authority = manifest.get("authority", {})
    require(authority.get("strict_original_source_supported") is False,
            "strict original-source authority was promoted")
    require(REQUIRED_REFUSALS <= set(authority.get("refusals", [])),
            "required authority refusal was dropped")
    require(manifest.get("replay", {}).get("expected_strict_exit") == 2,
            "strict replay no longer has refusal exit")


def _check_native_files(manifest):
    require(NATIVE_MANIFEST.is_file(), "native seam manifest is absent")
    require(NATIVE_VERIFIER.is_file(), "native seam verifier is absent")
    require(sha256(NATIVE_MANIFEST) == EXPECTED_NATIVE_MANIFEST_SHA256,
            "native seam manifest digest changed")
    require(sha256(NATIVE_VERIFIER) == EXPECTED_NATIVE_VERIFIER_SHA256,
            "native seam verifier digest changed")
    require(_load(NATIVE_MANIFEST) == manifest,
            "native manifest differs from frozen projection")
    for relative, expected in manifest.get(
            "bindings_sha256_lf_normalized", {}).items():
        path = NATIVE_ROOT / relative
        require(path.is_file(), "native bound input is absent: " + relative)
        require(lf_normalized_sha256(path) == expected,
                "native bound input digest changed: " + relative)


def build_fixture():
    require(sha256(NATIVE_MANIFEST) == EXPECTED_NATIVE_MANIFEST_SHA256,
            "native seam manifest digest changed before freeze")
    require(sha256(NATIVE_VERIFIER) == EXPECTED_NATIVE_VERIFIER_SHA256,
            "native seam verifier digest changed before freeze")
    manifest = _load(NATIVE_MANIFEST)
    face = _load(FACE_FIXTURE)
    require(sha256(FACE_FIXTURE) == EXPECTED_FACE_FIXTURE_SHA256,
            "GP face fixture changed before freeze")
    _validate_manifest(manifest, face)
    return {
        "schema": SCHEMA,
        "native_commit": EXPECTED_NATIVE_COMMIT,
        "native_manifest_sha256": EXPECTED_NATIVE_MANIFEST_SHA256,
        "native_verifier_sha256": EXPECTED_NATIVE_VERIFIER_SHA256,
        "gp_face_fixture_sha256": EXPECTED_FACE_FIXTURE_SHA256,
        "manifest": manifest,
        "authority_boundary": (
            "Conditional normalized-root to reduced-row replay only. "
            "The original-pair to normalized-root coefficient map remains open; "
            "no graph, membership, reverse-lift, coverage, H3, or verdict authority."
        ),
    }


def verify_fixture(path=DEFAULT_FIXTURE, check_native_bindings=False):
    path = Path(path)
    require(sha256(path) == EXPECTED_FIXTURE_SHA256,
            "frozen seam fixture digest changed")
    fixture = _load(path)
    require(set(fixture) == {
        "schema", "native_commit", "native_manifest_sha256",
        "native_verifier_sha256", "gp_face_fixture_sha256", "manifest",
        "authority_boundary",
    }, "frozen seam fixture fields changed")
    require(fixture["schema"] == SCHEMA, "frozen seam schema changed")
    require(fixture["native_commit"] == EXPECTED_NATIVE_COMMIT,
            "native seam commit binding changed")
    require(fixture["native_manifest_sha256"] ==
            EXPECTED_NATIVE_MANIFEST_SHA256,
            "native manifest binding changed")
    require(fixture["native_verifier_sha256"] ==
            EXPECTED_NATIVE_VERIFIER_SHA256,
            "native verifier binding changed")
    require(fixture["gp_face_fixture_sha256"] ==
            EXPECTED_FACE_FIXTURE_SHA256,
            "GP face-fixture binding changed")
    require(sha256(FACE_FIXTURE) == EXPECTED_FACE_FIXTURE_SHA256,
            "current GP face fixture changed")

    face = _load(FACE_FIXTURE)
    manifest = fixture["manifest"]
    _validate_manifest(manifest, face)
    if check_native_bindings:
        _check_native_files(manifest)

    envelope = EV.EvidenceEnvelope(
        schema=NATIVE_SCHEMA,
        context=EV.AffineContext(
            characteristic=0,
            coefficient_domain="characteristic-zero field K",
            point_universe=None,
            ring_vars=tuple(
                manifest["normalized_root_contract"]["output_variable_order"]),

        ),
        source_bindings=(
            EV.SourceBinding(
                "JC original-pair seam manifest",
                "sha256:" + EXPECTED_NATIVE_MANIFEST_SHA256),
            EV.SourceBinding(
                "JC original-pair seam verifier",
                "sha256:" + EXPECTED_NATIVE_VERIFIER_SHA256),
            EV.SourceBinding(
                "GP graded face fixture",
                "sha256:" + EXPECTED_FACE_FIXTURE_SHA256),
        ),
        checked_proposition=(
            "conditional normalized Laurent-root data imply the five exact "
            "reduced polynomiality rows"),
        licenses=(
            "five_reduced_rows_replayed_from_conditional_normalized_root_data",
            "native_row_commitments_welded_to_gp_exact_source_rows",
            "strict_original_source_promotion_refused",
        ),
        outstanding_premises=(
            "serialize or universally bind the exact original source pair",
            "materialize the coefficient-level target-pair to normalized-root map",
            "prove any source-image sufficiency or reverse lift separately",
        ),
        graph_effect=EV.GRAPH_EFFECT_NONE,
        authority_boundary=fixture["authority_boundary"],
        certificate_payload={
            "native_commit": EXPECTED_NATIVE_COMMIT,
            "rows": EXPECTED_ROWS,
            "missing_stage": "target_pair_to_normalized_laurent_root",
            "strict_original_source_supported": False,
        },
    ).as_dict()
    return {
        "verdict": "VERIFIED_CONDITIONAL_ESYSTEM_SEAM",
        "native_commit": EXPECTED_NATIVE_COMMIT,
        "rows": len(EXPECTED_ROWS),
        "strict_original_source_supported": False,
        "missing_stage": "target_pair_to_normalized_laurent_root",
        "evidence_envelope": envelope,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", type=Path, default=DEFAULT_FIXTURE)
    parser.add_argument("--check-native-bindings", action="store_true")
    parser.add_argument("--refresh-fixture", action="store_true")
    args = parser.parse_args(argv)

    if args.refresh_fixture:
        value = build_fixture()
        args.fixture.parent.mkdir(parents=True, exist_ok=True)
        args.fixture.write_bytes((
            json.dumps(value, indent=2, sort_keys=True,
                       ensure_ascii=True) + "\n").encode("utf-8"))
        print(args.fixture)
        return 0

    report = verify_fixture(
        args.fixture, check_native_bindings=args.check_native_bindings)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
