#!/usr/bin/env python3
"""Freeze and verify the JC S4 ``C2 = 0`` / ``C2 != 0`` scope split.

This is a standalone constructible-scope projection, not a new graph relation.
It independently checks the exact K-point against the frozen 952-term fitting
condition, its 24-term leading coefficient, and the 12-term rank witness.  The
24 off-locus seeds remain bounded search provenance and license no emptiness or
confinement statement.
"""

from __future__ import annotations

import argparse
import contextlib
import copy
import hashlib
import io
import json
import os
import runpy
import subprocess
import sys
import tempfile
from fractions import Fraction
from pathlib import Path

from grandportage import evidence as EV
from grandportage import groebner as G


ROOT = Path(__file__).resolve().parents[2]
NATIVE_ROOT = ROOT.parent / "math-stuff" / "d2_plane_72_108"
DEFAULT_FIXTURE = ROOT / "fixtures" / "jc_s4" / "scope_v1.json"
SCHEMA = "gp-jc-s4-constructible-scope/v1"
EXPECTED_FIXTURE_SHA256 = (
    "fd501e3bda2a3854fc7038d1c13de1d2a916a0f56f6c5fbbb64584ee0773d29b")

NATIVE_BINDINGS = {
    "f2_h3_s4_downstairs_consistency.json":
        "bfc9a751dad32aca72efe14b2870a3125d478a47e6ae4a77b0d783eee3de5a08",
    "f2_h3_s4_fitting_kpoint.json":
        "0c8cfac5d31bc00c7a3edb49cc1706837883c75f74ce38f202f539b7d0e45342",
    "f2_h3_s4_fitting_kpoint.py":
        "2983b60c18ac3cf6328b926a51b8e0dfd99090956d603f59566da0e024b3fa0b",
    "f2_h3_s4_rank3_minors.json":
        "2358ff6f5e9f9e001e627757a2875825f533a8eb7d57eacdbf9ee1e37280348f",
    "f2_h3_s4_rank3_minors.py":
        "167309d3ea3596a023dc8903e7f4675fa69dec65686498f08e9b40371dbb9383",
}

POLYNOMIAL_SYMBOLS = (
    "c2_1", "c2_2", "c3_5", "c7_10", "c7_9",
    "c8_10", "c8_11", "c8_12", "p", "t",
)
MODEL_VARS = tuple(name for name in POLYNOMIAL_SYMBOLS if name != "t")
K_ZERO = (Fraction(0), Fraction(0), Fraction(0))
K_ONE = (Fraction(1), Fraction(0), Fraction(0))
K_T = (Fraction(0), Fraction(1), Fraction(0))


class S4ScopeError(ValueError):
    """The frozen S4 receipt, arithmetic, or authority scope drifted."""


def require(condition, check_id, message):
    if not condition:
        raise S4ScopeError("%s: %s" % (check_id, message))


def normalized_sha256(path):
    raw = Path(path).read_bytes().replace(b"\r\n", b"\n")
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True,
                       ensure_ascii=True) + "\n").encode("utf-8")


def sparse_digest(value):
    canonical = json.dumps({
        "symbols": list(value["symbols"]),
        "terms": [[list(map(list, monomial)), coefficient]
                  for monomial, coefficient in value["terms"]],
    }, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def _k_add(left, right):
    return tuple(a + b for a, b in zip(left, right))


def _k_mul(left, right):
    raw = [Fraction(0)] * 5
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            raw[i + j] += a * b
    for degree in range(4, 2, -1):
        raw[degree - 3] -= raw[degree] / 15
    return tuple(raw[:3])


def _k_pow(value, exponent):
    result = K_ONE
    base = value
    power = exponent
    while power:
        if power & 1:
            result = _k_mul(result, base)
        base = _k_mul(base, base)
        power //= 2
    return result


def _parse_k(expression):
    parsed = G.parse_polynomial(
        expression, ("t",), 0, G._ArithmeticBudget())
    result = [Fraction(0), Fraction(0), Fraction(0)]
    for monomial, coefficient in parsed.terms.items():
        exponent = monomial[0]
        require(exponent <= 2, "K1",
                "K element is not a canonical degree-at-most-two representative")
        result[exponent] += coefficient
    return tuple(result)


def _decode_sparse(value, where):
    require(isinstance(value, dict) and set(value) == {"symbols", "terms"},
            "P1", where + " has the wrong sparse shape")
    symbols = value["symbols"]
    require(symbols == sorted(set(symbols)), "P2",
            where + " symbols are not sorted and unique")
    require(set(symbols) <= set(POLYNOMIAL_SYMBOLS), "P3",
            where + " contains an unexpected coordinate")
    output = {}
    previous = None
    for position, term in enumerate(value["terms"]):
        require(isinstance(term, list) and len(term) == 2, "P4",
                "%s term %d is malformed" % (where, position))
        support, coefficient_text = term
        require(isinstance(support, list) and isinstance(coefficient_text, str),
                "P4", "%s term %d is malformed" % (where, position))
        monomial = []
        last = -1
        for factor in support:
            require(isinstance(factor, list) and len(factor) == 2, "P4",
                    where + " has malformed support")
            index, exponent = factor
            require(type(index) is int and last < index < len(symbols), "P5",
                    where + " support indices are not canonical")
            require(type(exponent) is int and 0 < exponent <= 64, "P6",
                    where + " exponent is outside the bounded checker")
            monomial.append((symbols[index], exponent))
            last = index
        monomial = tuple(monomial)
        require(previous is None or previous < monomial, "P7",
                where + " terms are not strictly canonical")
        coefficient = Fraction(coefficient_text)
        require(coefficient and str(coefficient) == coefficient_text, "P8",
                where + " has a zero or noncanonical coefficient")
        output[monomial] = coefficient
        previous = monomial
    return output


def _slice(polynomial, variable, exponent):
    output = {}
    for monomial, coefficient in polynomial.items():
        powers = dict(monomial)
        if powers.pop(variable, 0) == exponent:
            output[tuple(sorted(powers.items()))] = coefficient
    return output


def _degree(polynomial, variable):
    return max((dict(monomial).get(variable, 0) for monomial in polynomial),
               default=0)


def _evaluate(polynomial, assignment):
    total = K_ZERO
    for monomial, coefficient in polynomial.items():
        value = (coefficient, Fraction(0), Fraction(0))
        for name, exponent in monomial:
            factor = K_T if name == "t" else assignment[name]
            value = _k_mul(value, _k_pow(factor, exponent))
        total = _k_add(total, value)
    return total


def _native_payload(native_root=NATIVE_ROOT):
    return json.loads((Path(native_root) /
                       "f2_h3_s4_fitting_kpoint.json").read_text(
                           encoding="utf-8"))


def _extract_native_polynomials(native_root=NATIVE_ROOT):
    """Execute the producer only while building a frozen fixture."""
    root = Path(native_root)
    script = root / "f2_h3_s4_fitting_kpoint.py"
    old_argv = sys.argv[:]
    old_path = sys.path[:]
    try:
        sys.argv = [str(script), "--quiet"]
        sys.path.insert(0, str(root))
        with contextlib.redirect_stdout(io.StringIO()):
            namespace = runpy.run_path(str(script), run_name="gp_s4_fixture")
    finally:
        sys.argv = old_argv
        sys.path[:] = old_path
    canon = namespace["canon"]
    return {
        "C": canon(namespace["C"]),
        "C2": canon(namespace["C2"]),
        "rank_witness": canon(namespace["WITNESS"]),
    }


def _projection(receipt):
    search = receipt["suggested_route_envelope"]
    return {
        "coefficient_domain": "K = QQ[t]/(15*t^3 + 1)",
        "point_universe": "BASE",
        "parent": {
            "id": "S4_C_ZERO",
            "sort": "NECESSARY_BOUNDARY_MODEL",
            "equations": ["C"],
            "status": "NONEMPTY_WITNESSED_ON_C2_ZERO_PIECE",
        },
        "closed_piece": {
            "id": "S4_C_ZERO__C2_ZERO",
            "relation": "CLOSED_RESTRICTION",
            "equations": ["C", "C2"],
            "claim": "NONEMPTY",
            "status": "VERIFIED_EXACT_K_POINT",
        },
        "open_piece": {
            "id": "S4_C_ZERO__C2_NONZERO",
            "relation": "PRINCIPAL_OPEN_RESTRICTION",
            "equations": ["C"],
            "open_conditions": ["C2"],
            "claim": None,
            "status": "OPEN",
            "search_evidence": {
                "seeds": search["seeds"],
                "provably_non_square_discriminant":
                    search["provably_non_square_discriminant"],
                "squares_found": search["squares_found"],
                "inconclusive": search["inconclusive"],
                "authority": "BOUNDED_PROVENANCE_ONLY",
                "graph_effect": "NONE",
            },
        },
        "cover": {
            "kind": "ZERO_NONZERO_CONSTRUCTIBLE_COVER",
            "branches": ["S4_C_ZERO__C2_ZERO", "S4_C_ZERO__C2_NONZERO"],
            "status": "VERIFIED_STRUCTURAL_DICHOTOMY",
            "union_claim": None,
            "graph_effect": "NONE",
        },
        "guards": {
            "c3_5": "-3/2",
            "c3_5_nonzero": True,
            "no_coordinate_inverted": True,
        },
        "graph_effect": "NONE",
        "refusals": list(receipt["refusals"]) + [
            "off-locus emptiness",
            "all K-points lie on C2 = 0",
            "24-seed search promoted to a theorem",
            "claim about the union beyond its structural cover",
        ],
    }


def build_fixture(native_root=NATIVE_ROOT):
    root = Path(native_root)
    bindings = {name: normalized_sha256(root / name)
                for name in sorted(NATIVE_BINDINGS)}
    require(bindings == dict(sorted(NATIVE_BINDINGS.items())), "B1",
            "native S4 input drifted before freeze")
    receipt = _native_payload(root)
    polynomials = _extract_native_polynomials(root)
    return {
        "schema": SCHEMA,
        "binding_digest_algo": "sha256-lf-normalized",
        "source_bindings": bindings,
        "native_receipt": receipt,
        "polynomials": polynomials,
        "projection": _projection(receipt),
        "authority_boundary": (
            "The exact point verifies NONEMPTY only on C=C2=0 (and hence C=0). "
            "The principal-open C2!=0 piece remains OPEN. The 24 seeds are "
            "bounded search provenance, never emptiness or confinement."),
    }


def _validate_projection(projection):
    require(projection.get("coefficient_domain") ==
            "K = QQ[t]/(15*t^3 + 1)" and
            projection.get("point_universe") == "BASE", "M1",
            "coefficient domain or point universe widened")
    require(projection.get("graph_effect") == "NONE", "M2",
            "standalone S4 assay attempted graph authority")
    require(projection.get("parent") == {
        "id": "S4_C_ZERO",
        "sort": "NECESSARY_BOUNDARY_MODEL",
        "equations": ["C"],
        "status": "NONEMPTY_WITNESSED_ON_C2_ZERO_PIECE",
    }, "M3", "parent necessary-boundary scope changed")
    closed = projection.get("closed_piece", {})
    require(closed == {
        "id": "S4_C_ZERO__C2_ZERO",
        "relation": "CLOSED_RESTRICTION",
        "equations": ["C", "C2"],
        "claim": "NONEMPTY",
        "status": "VERIFIED_EXACT_K_POINT",
    }, "M4",
            "closed-piece point authority changed")
    opened = projection.get("open_piece", {})
    require({key: opened.get(key) for key in (
        "id", "relation", "equations", "open_conditions", "claim", "status",
    )} == {
        "id": "S4_C_ZERO__C2_NONZERO",
        "relation": "PRINCIPAL_OPEN_RESTRICTION",
        "equations": ["C"],
        "open_conditions": ["C2"],
        "claim": None,
        "status": "OPEN",
    }, "M5",
            "off-locus piece was promoted or mistyped")
    search = opened.get("search_evidence", {})
    require(search == {
        "seeds": 24,
        "provably_non_square_discriminant": 24,
        "squares_found": 0,
        "inconclusive": 0,
        "authority": "BOUNDED_PROVENANCE_ONLY",
        "graph_effect": "NONE",
    }, "M6", "bounded search was widened beyond its envelope")
    cover = projection.get("cover", {})
    require(cover.get("kind") == "ZERO_NONZERO_CONSTRUCTIBLE_COVER" and
        cover.get("branches") == [
        "S4_C_ZERO__C2_ZERO", "S4_C_ZERO__C2_NONZERO"] and
        cover.get("status") == "VERIFIED_STRUCTURAL_DICHOTOMY" and
        cover.get("union_claim") is None and
        cover.get("graph_effect") == "NONE", "M7",
        "constructible cover was promoted or lost a branch")
    require(projection.get("guards") == {
        "c3_5": "-3/2",
        "c3_5_nonzero": True,
        "no_coordinate_inverted": True,
    }, "M8", "point guard scope changed")
    refusals = set(projection.get("refusals", []))
    require({"off-locus emptiness", "all K-points lie on C2 = 0",
             "24-seed search promoted to a theorem",
             "source-image sufficiency", "actual-source membership",
             "H3 promotion"} <= refusals, "M9",
            "required off-locus refusal disappeared")


def validate_fixture_value(fixture):
    require(set(fixture) == {
        "schema", "binding_digest_algo", "source_bindings", "native_receipt",
        "polynomials", "projection", "authority_boundary",
    }, "F1", "fixture shape changed")
    require(fixture["schema"] == SCHEMA, "F2", "fixture schema changed")
    require(fixture["binding_digest_algo"] == "sha256-lf-normalized", "F3",
            "binding algorithm changed")
    require(fixture["source_bindings"] ==
            dict(sorted(NATIVE_BINDINGS.items())), "M10",
            "frozen native binding changed")
    receipt = fixture["native_receipt"]
    require(receipt.get("id") == "f2_h3_s4_fitting_kpoint" and
            receipt.get("kind") == "point_existence_certificate" and
            receipt.get("point_is_in_K") is True and
            receipt.get("all_four_vanish") is True, "N1",
            "native point receipt identity or local verdict changed")
    require(receipt.get("checks") == {"passed": 15, "total": 15} and
            receipt.get("mutations") == {"dead": 7, "total": 7}, "N2",
            "native point receipt check counts changed")
    require(receipt.get("suggested_route_envelope", {}).get("seeds") == 24 and
            receipt["suggested_route_envelope"].get("squares_found") == 0,
            "N3", "bounded search envelope changed")
    _validate_projection(fixture["projection"])

    records = fixture["polynomials"]
    require(set(records) == {"C", "C2", "rank_witness"}, "F4",
            "frozen polynomial set changed")
    C = _decode_sparse(records["C"], "C")
    C2 = _decode_sparse(records["C2"], "C2")
    witness = _decode_sparse(records["rank_witness"], "rank witness")
    require(sparse_digest(records["C"]) ==
            receipt["reconstructed"]["fitting_condition_sha256"], "P9",
            "C digest no longer matches the native receipt")
    require(len(C) == 952 and len(C2) == 24 and len(witness) == 12, "P10",
            "C, C2, or rank-witness term count changed")
    require(_degree(C, "p") == 2 and _slice(C, "p", 2) == C2, "P11",
            "C2 is not the exact leading p-coefficient of C")

    point = {name: _parse_k(value)
             for name, value in receipt["point"].items()
             if name in set(MODEL_VARS)}
    require(_evaluate(C, point) == K_ZERO and
            _evaluate(C2, point) == K_ZERO, "W1",
            "the exhibited K-point is not on C=C2=0")
    require(_evaluate(witness, point) != K_ZERO, "W2",
            "the rank witness vanishes at the exhibited point")
    require(point["c3_5"] != K_ZERO, "W3",
            "the exhibited point lost the c3_5 guard")
    require(_evaluate(_slice(C, "p", 1), point) != K_ZERO, "W4",
            "C is not linear with nonzero p-coefficient on the point")
    return fixture


def check_native_bindings(fixture, native_root=NATIVE_ROOT):
    root = Path(native_root)
    require(root.exists(), "B2", "sibling JC checkout is absent")
    for name, expected in fixture["source_bindings"].items():
        require((root / name).exists(), "B3", "native binding is absent: " + name)
        require(normalized_sha256(root / name) == expected, "M9",
                "native binding changed: " + name)


def verify_fixture(path=DEFAULT_FIXTURE, check_bindings=False,
                   native_root=NATIVE_ROOT):
    raw = Path(path).read_bytes()
    if EXPECTED_FIXTURE_SHA256 is not None:
        require(hashlib.sha256(raw).hexdigest() == EXPECTED_FIXTURE_SHA256,
                "F5", "frozen S4 fixture digest changed")
    fixture = validate_fixture_value(json.loads(raw.decode("utf-8")))
    if check_bindings:
        check_native_bindings(fixture, native_root)
    projection = copy.deepcopy(fixture["projection"])
    envelope = EV.EvidenceEnvelope(
        schema=SCHEMA,
        context=EV.AffineContext(
            characteristic=0,
            coefficient_domain=projection["coefficient_domain"],
            point_universe=projection["point_universe"],
            ring_vars=MODEL_VARS,
            generators=("C", "C2"),
        ),
        source_bindings=tuple(
            EV.SourceBinding(name, "sha256:" + digest)
            for name, digest in sorted(fixture["source_bindings"].items())),
        checked_proposition=(
            "one exact K-point lies on C=C2=0 with nonzero rank witness; "
            "the complementary C2!=0 piece remains open"),
        licenses=(
            "S4_C2_zero_piece_nonempty_over_K",
            "S4_C_zero_parent_nonempty_over_K_from_same_point",
            "C2_zero_or_nonzero_is_a_structural_constructible_cover",
        ),
        outstanding_premises=(
            "K-point existence or emptiness on C=0 and C2!=0",
            "source-image sufficiency and actual-source membership",
            "H3 and (75,125) verdict promotion",
        ),
        graph_effect=EV.GRAPH_EFFECT_NONE,
        authority_boundary=fixture["authority_boundary"],
        certificate_payload={
            "closed_piece": projection["closed_piece"],
            "open_piece": projection["open_piece"],
            "cover": projection["cover"],
        },
    ).as_dict()
    projection.update({
        "schema": SCHEMA,
        "verdict": "VERIFIED_ONE_PIECE_OPEN_OTHER_PIECE",
        "source_bindings": fixture["source_bindings"],
        "evidence_envelope": envelope,
    })
    return projection


def native_replay(native_root=NATIVE_ROOT):
    script = Path(native_root) / "f2_h3_s4_fitting_kpoint.py"
    completed = subprocess.run(
        [sys.executable, str(script), "--quiet"], cwd=str(native_root),
        capture_output=True, text=True, timeout=120, check=False)
    require(completed.returncode == 0, "R1",
            "native S4 replay failed: " + completed.stderr.strip())
    require("checks    15/15 passed" in completed.stdout and
            "mutations 7/7 dead" in completed.stdout, "R2",
            "native S4 replay summary changed")
    return {"verdict": "VERIFIED_NATIVE_S4_REPLAY", "graph_effect": "NONE"}


def write_fixture(path=DEFAULT_FIXTURE, native_root=NATIVE_ROOT, force=False):
    path = Path(path)
    if path.exists() and not force:
        raise S4ScopeError("fixture exists; pass --force to replace it: %s" % path)
    payload = encoded(build_fixture(native_root))
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


def write_report(path, report, force=False):
    """Atomically persist a reviewable projection without silent overwrite."""
    path = Path(path)
    if path.exists() and not force:
        raise S4ScopeError("output exists; pass --force to replace it: %s" % path)
    payload = encoded(report)
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


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", type=Path, default=DEFAULT_FIXTURE)
    parser.add_argument("--native-root", type=Path, default=NATIVE_ROOT)
    parser.add_argument("--check-native-bindings", action="store_true")
    parser.add_argument("--native-replay", action="store_true")
    parser.add_argument("--write-fixture", action="store_true")
    parser.add_argument("--output", type=Path,
                        help="atomically write the verified projection")
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args(argv)
    if args.force and not (args.write_fixture or args.output):
        parser.error("--force requires --write-fixture or --output")
    try:
        if args.write_fixture:
            digest = write_fixture(args.fixture, args.native_root, args.force)
            print(json.dumps({"fixture": str(args.fixture), "sha256": digest},
                             indent=2, sort_keys=True))
            return 0
        report = verify_fixture(
            args.fixture, args.check_native_bindings, args.native_root)
        if args.native_replay:
            report["native_replay"] = native_replay(args.native_root)
        if args.output:
            write_report(args.output, report, args.force)
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        print(json.dumps({"schema": SCHEMA, "verdict": "REFUSED",
                          "error": str(exc)}, indent=2, sort_keys=True),
              file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
