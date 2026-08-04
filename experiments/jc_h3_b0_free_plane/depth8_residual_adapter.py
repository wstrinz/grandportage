#!/usr/bin/env python3
"""Replay the explicit JC depth-eight residual scalar and constrained pullback.

This bounded adapter consumes two frozen native certificates.  It independently
recomputes Psi8 from r8_1 and r8_3, instantiates the prior affine-block
compatibility identity, reconstructs Omega8 through the landed depth-6/7 block
solve, and checks the exact degree-14 quotient witness.  The result excludes
only that frozen compatible witness and retains graph effect NONE.
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

from grandportage import evidence as EV


ROOT = Path(__file__).resolve().parents[2]
NATIVE_ROOT = ROOT.parent / "math-stuff" / "d2_plane_72_108"
DEFAULT_FIXTURE = ROOT / "fixtures" / "jc_b0_depth8_residual" / "v1.json"
DEFAULT_REVIEW = ROOT / "review" / "jc-h3-b0-depth8-psi8-omega8-v1.json"
PREVIOUS_FIXTURE = ROOT / "fixtures" / "jc_b0_depth8_free_plane" / "v1.json"
SCHEMA = EV.AFFINE_FIBER_BLOCK_SCHEMA
EXPECTED_FIXTURE_SHA256 = (
    "ce082feccd226db1bd8e0749b652ae806e896a79053a0ed7454c5a1288e686b6")
EXPECTED_PREVIOUS_FIXTURE_SHA256 = (
    "7c26a7fdcfd12321997beb259f73388db654b3aff1cfbb83f30ccfa11017b82c")

PSI_CERT = "f2_h3_b0_depth8_psi8_certificate.json"
PULLBACK_CERT = "f2_h3_b0_psi8_constrained_pullback_certificate.json"
MODULE_CERT = "f2_h3_b0_compatibility_module.json"
UNIFORM_CERT = "f2_h3_b0_uniform_lambda.json"

# Filled from LF-normalized native inputs.  Fixture construction refuses drift.
NATIVE_BINDINGS = {
    "f2_h3_b0_compatibility_module.json": "944f95d762e05d3dec4ffa6599b4f0d1d2674e4127e5d168712a62de50291840",
    "f2_h3_b0_depth8_free_plane_coefficients.json": "5cf9015b0065eb6fd5cd181be28f4c9e8004ca61786fafba1af463fddfc3024a",
    "f2_h3_b0_depth8_psi8.py": "f00cbf68a7d9d58985c16513b881b4230bf39c9a559575adbfe7fe2182705281",
    "f2_h3_b0_depth8_psi8_certificate.json": "58b6a583acd6f3011c0a7b845adf1afa4de3f80a5b2d902c5cf91c4774157736",
    "f2_h3_b0_depth8_psi8_producer.py": "acf941c81621c819fac71241261ee9b46fccb871e3a74d3f8b6c369b6a3b1da6",
    "f2_h3_b0_free_plane_receipt.json": "e6c731f984d9c06d84aac014db8bff234bb15962d1ee6fac2ee80df7795e00da",
    "f2_h3_b0_psi8_constrained_pullback.py": "b6717420970f3b728965232dbec891d188ad825d555329d54157854301778615",
    "f2_h3_b0_psi8_constrained_pullback_certificate.json": "54f44753b19f35dbcbf326de0a1076c51ad08569dc941a73cf1e3f7e6f0e5e6b",
    "f2_h3_b0_psi8_constrained_pullback_producer.py": "83abb0f4cf734bf6f9616fae39501a7a05e590a33ba25c56068507f9597d0a9f",
    "f2_h3_b0_source_incidence.json": "683f148fe737d80f4d24dcd33f082895435bf449a5b7608c03985cede1763ff7",
    "f2_h3_b0_uniform_lambda.json": "499a7c0975ac01883ecf4b7b9be14e9b00dd4284f7688810aaa175ca86ada3fd",
    "f2_h3_esystem_seam.py": "e21ecff0f9f389b620fa599820e95c93eb44343c44ff20e9d25879f330b39aca",
    "f2_h3_graded_eliminator_contract.py": "63da51c56475d39266f3fc74e6f5b0a2f70d05e0d7781d98791aa6bf12535965",
    "f2_h3_p_c6_1_receipt.json": "d971325110dcab38b25089c542c4cc5fd79ddb04342124ebf11c5d673ce4ee25",
    "f2_h3_source_depth6_chain_certificate.json.gz": "2280c88410667ce9c8ac5900c61b044f5cd7174540d859485c04bcca3a27eba0",
    "f2_h3_source_depth6_receipt.json": "3dde87dd53b07c851ce78c27227b63660a9177860791cc2dca5bff5152db9c0d",
    "f2_h3_source_depth7_receipt.json": "2b50fc44669222a335697119c6221588e056cc32dfc1e1590e96162a4d301b86",
    "f2_h3_wall_source_locus_polys.json.gz": "3cf98a426e1bce9d8eabbdb672403f0e6e97f08009e274a11865b8af15f48a19",
    "f2_target_root_support_data.py": "16eb77a98c9c02939cc48a9b7f0e9f1141234784013daf4a34ca375666a2f2d2",
}

FIBER = (
    "c8_9", "c7_7", "c8_8", "c7_6", "c8_7", "c8_6", "c7_5",
    "c7_4", "c8_5",
)
SOLVED = FIBER[:7]
BASE = (
    "c2_1", "c2_2", "c2_3", "c3_5", "c7_8", "c7_9", "c7_10",
    "c8_10", "c8_11", "p",
)
U1 = SOLVED[:5]


class Depth8ResidualEvidenceError(ValueError):
    """The residual, pullback, quotient witness, or scope drifted."""


def require(condition, check_id, message):
    if not condition:
        raise Depth8ResidualEvidenceError("%s: %s" % (check_id, message))


def normalized_sha256(path):
    return hashlib.sha256(
        Path(path).read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True,
                       ensure_ascii=True) + "\n").encode("utf-8")


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("utf-8")


def _fraction(value, check_id="P1"):
    try:
        result = Fraction(value)
    except (ValueError, ZeroDivisionError, TypeError) as exc:
        raise Depth8ResidualEvidenceError(
            "%s: invalid rational coefficient" % check_id) from exc
    require(str(result) == value, check_id, "noncanonical rational")
    return result


# Sparse polynomials are maps from sorted monomials to exact rationals.  Every
# multiplication reduces t^3 = -1/15, so this layer is over K, not QQ[t].
def from_sparse(value):
    require(set(value) == {"symbols", "terms"}, "P2",
            "sparse object shape changed")
    symbols = value["symbols"]
    require(isinstance(symbols, list) and symbols == sorted(set(symbols)) and
            all(isinstance(name, str) for name in symbols), "P3",
            "sparse symbol table is not canonical")
    out = {}
    for row in value["terms"]:
        require(isinstance(row, list) and len(row) == 2, "P4",
                "sparse term is malformed")
        powers, coefficient = row
        monomial = []
        prior = -1
        for pair in powers:
            require(isinstance(pair, list) and len(pair) == 2 and
                    type(pair[0]) is int and prior < pair[0] < len(symbols) and
                    type(pair[1]) is int and pair[1] > 0, "P5",
                    "sparse power is invalid or unordered")
            prior = pair[0]
            monomial.append((symbols[pair[0]], pair[1]))
        key = tuple(sorted(monomial))
        require(key not in out, "P6", "duplicate sparse monomial")
        rational = _fraction(coefficient, "P7")
        require(rational != 0, "P7", "zero sparse coefficient")
        out[key] = rational
    require(sparse_json(out) == value, "P8", "sparse object is noncanonical")
    return out


def unser(value):
    out = {}
    for monomial, coefficient in value:
        key = tuple((name, exponent) for name, exponent in monomial)
        require(key == tuple(sorted(key)) and key not in out, "P9",
                "module polynomial is noncanonical")
        out[key] = _fraction(coefficient, "P10")
    return out


def sparse_json(poly):
    names = sorted({name for monomial in poly for name, _ in monomial})
    indexes = {name: index for index, name in enumerate(names)}
    terms = sorted([[[[indexes[name], exponent]
                      for name, exponent in monomial], str(coefficient)]
                    for monomial, coefficient in poly.items()])
    return {"symbols": names, "terms": terms}


def ser(poly):
    return sorted((list(map(list, monomial)), str(coefficient))
                  for monomial, coefficient in poly.items())


def sparse_digest(poly):
    return hashlib.sha256(canonical(sparse_json(poly))).hexdigest()


def module_digest(poly):
    return hashlib.sha256(canonical(ser(poly))).hexdigest()


def padd(left, right):
    out = dict(left)
    for monomial, coefficient in right.items():
        value = out.get(monomial, Fraction(0)) + coefficient
        if value:
            out[monomial] = value
        else:
            out.pop(monomial, None)
    return out


def pscale(poly, scalar):
    scalar = Fraction(scalar)
    return {monomial: coefficient * scalar
            for monomial, coefficient in poly.items() if coefficient * scalar}


def pin(poly):
    out = {}
    for monomial, coefficient in poly.items():
        powers = dict(monomial)
        quotient, remainder = divmod(powers.pop("t", 0), 3)
        coefficient *= Fraction(-1, 15) ** quotient
        if remainder:
            powers["t"] = remainder
        key = tuple(sorted(powers.items()))
        value = out.get(key, Fraction(0)) + coefficient
        if value:
            out[key] = value
        else:
            out.pop(key, None)
    return out


def pmul(left, right):
    out = {}
    for lm, lc in left.items():
        for rm, rc in right.items():
            powers = dict(lm)
            for name, exponent in rm:
                powers[name] = powers.get(name, 0) + exponent
            key = tuple(sorted(powers.items()))
            out[key] = out.get(key, Fraction(0)) + lc * rc
    return pin({key: value for key, value in out.items() if value})


def product(*values):
    out = {(): Fraction(1)}
    for value in values:
        out = pmul(out, value)
    return out


def power(poly, exponent):
    out = {(): Fraction(1)}
    for _ in range(exponent):
        out = pmul(out, poly)
    return out


def variable(name):
    return {((name, 1),): Fraction(1)}


def degree(poly, name):
    return max((dict(monomial).get(name, 0) for monomial in poly), default=0)


def mindegree(poly, name):
    return min((dict(monomial).get(name, 0) for monomial in poly), default=0)


def support(poly):
    return {name for monomial in poly for name, _ in monomial}


def coeff_parts(poly, names):
    out = {}
    for monomial, coefficient in poly.items():
        powers = dict(monomial)
        key = tuple(sorted((name, powers.pop(name)) for name in list(powers)
                           if name in names))
        rest = tuple(sorted(powers.items()))
        out[key] = padd(out.get(key, {}), {rest: coefficient})
    return out


def specialize(poly, values):
    out = {}
    for monomial, coefficient in poly.items():
        powers = dict(monomial)
        for name in list(powers):
            if name in values:
                coefficient *= values[name] ** powers.pop(name)
        if coefficient:
            key = tuple(sorted(powers.items()))
            out[key] = out.get(key, Fraction(0)) + coefficient
    return {key: value for key, value in out.items() if value}


def strip_monomial(poly, powers):
    out = {}
    for monomial, coefficient in poly.items():
        rest = dict(monomial)
        for name, exponent in powers.items():
            if rest.get(name, 0) < exponent:
                return None
            rest[name] -= exponent
            if rest[name] == 0:
                rest.pop(name)
        out[tuple(sorted(rest.items()))] = coefficient
    return out


def determinant(matrix):
    size = len(matrix)
    require(all(len(row) == size for row in matrix), "P11",
            "polynomial matrix is not square")
    memo = {}

    def expand(row, columns):
        if row == size:
            return {(): Fraction(1)}
        key = (row, columns)
        if key in memo:
            return memo[key]
        result = {}
        remaining = [column for column in range(size)
                     if columns >> column & 1]
        for index, column in enumerate(remaining):
            entry = matrix[row][column]
            if entry:
                sub = expand(row + 1, columns & ~(1 << column))
                result = padd(result, pscale(pmul(entry, sub),
                                             -1 if index % 2 else 1))
        memo[key] = result
        return result

    return expand(0, (1 << size) - 1)


# K = QQ[t]/(15*t^3+1), followed by univariate arithmetic over K.
KZERO = (Fraction(0), Fraction(0), Fraction(0))
KONE = (Fraction(1), Fraction(0), Fraction(0))


def kadd(left, right):
    return tuple(a + b for a, b in zip(left, right))


def ksub(left, right):
    return tuple(a - b for a, b in zip(left, right))


def kmul(left, right):
    work = [Fraction(0)] * 5
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            work[i + j] += a * b
    for exponent in (4, 3):
        work[exponent - 3] -= work[exponent] / 15
    return tuple(work[:3])


def kscale(value, scalar):
    return tuple(entry * scalar for entry in value)


def kinverse(value):
    require(value != KZERO, "K1", "attempted to invert zero in K")
    matrix = [[Fraction(0)] * 4 for _ in range(3)]
    for column in range(3):
        basis = tuple(Fraction(1) if i == column else Fraction(0)
                      for i in range(3))
        image = kmul(value, basis)
        for row in range(3):
            matrix[row][column] = image[row]
    matrix[0][3] = Fraction(1)
    for column in range(3):
        pivot = next((row for row in range(column, 3)
                      if matrix[row][column]), None)
        require(pivot is not None, "K2", "nonunit coefficient in K")
        matrix[column], matrix[pivot] = matrix[pivot], matrix[column]
        scale = matrix[column][column]
        matrix[column] = [entry / scale for entry in matrix[column]]
        for row in range(3):
            if row != column and matrix[row][column]:
                scale = matrix[row][column]
                matrix[row] = [a - scale * b for a, b in
                               zip(matrix[row], matrix[column])]
    return tuple(matrix[row][3] for row in range(3))


def ktrim(poly):
    poly = list(poly)
    while len(poly) > 1 and poly[-1] == KZERO:
        poly.pop()
    return poly


def kpoly_add(left, right):
    size = max(len(left), len(right))
    return ktrim([kadd(left[i] if i < len(left) else KZERO,
                       right[i] if i < len(right) else KZERO)
                  for i in range(size)])


def kpoly_sub(left, right):
    size = max(len(left), len(right))
    return ktrim([ksub(left[i] if i < len(left) else KZERO,
                       right[i] if i < len(right) else KZERO)
                  for i in range(size)])


def kpoly_mul(left, right):
    out = [KZERO for _ in range(len(left) + len(right) - 1)]
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] = kadd(out[i + j], kmul(a, b))
    return ktrim(out)


def kpoly_divmod(dividend, divisor):
    dividend = ktrim(dividend)
    divisor = ktrim(divisor)
    require(not (len(divisor) == 1 and divisor[0] == KZERO), "K3",
            "zero polynomial divisor")
    degree_divisor = len(divisor) - 1
    inverse_lead = kinverse(divisor[-1])
    quotient = [KZERO for _ in
                range(max(1, len(dividend) - degree_divisor))]
    while not (len(dividend) == 1 and dividend[0] == KZERO) and \
            len(dividend) - 1 >= degree_divisor:
        offset = len(dividend) - 1 - degree_divisor
        factor = kmul(dividend[-1], inverse_lead)
        quotient[offset] = factor
        for index, coefficient in enumerate(divisor):
            dividend[offset + index] = ksub(
                dividend[offset + index], kmul(factor, coefficient))
        dividend = ktrim(dividend)
    return ktrim(quotient), ktrim(dividend)


def kpoly_gcd(left, right):
    left, right = ktrim(left), ktrim(right)
    while not (len(right) == 1 and right[0] == KZERO):
        left, right = right, kpoly_divmod(left, right)[1]
    inverse = kinverse(left[-1])
    return [kmul(value, inverse) for value in left]


def coeffs_in(poly, name):
    out = {}
    for monomial, coefficient in poly.items():
        powers = dict(monomial)
        exponent = powers.pop(name, 0)
        out[exponent] = padd(out.get(exponent, {}),
                             {tuple(sorted(powers.items())): coefficient})
    return out


def to_kpoly(poly, name):
    coefficients = coeffs_in(poly, name)
    degree_bound = max(coefficients, default=0)
    out = []
    for exponent in range(degree_bound + 1):
        value = [Fraction(0)] * 3
        for monomial, coefficient in coefficients.get(exponent, {}).items():
            require(all(var == "t" for var, _ in monomial), "K4",
                    "quotient coefficient contains a non-field variable")
            value[dict(monomial).get("t", 0)] += coefficient
        out.append(tuple(value))
    return ktrim(out)


def triples(values):
    require(len(values) % 3 == 0, "K5", "flattened K polynomial malformed")
    return [tuple(_fraction(values[index + offset], "K6")
                  for offset in range(3)) for index in range(0, len(values), 3)]


def _expected_projection():
    return {
        "instance_id": "jc_h3_b0_depth8_psi8_constrained_pullback",
        "semantic_layer": "NECESSARY_DEPTH8_CONDITION_ON_CONSTRAINED_FIBER",
        "coefficient_domain": "K = QQ[t]/(15*t^3+1)",
        "checked_results": {
            "Psi8": "709-term nonzero nonunit affine fiber scalar",
            "Omega8": "4123-term constrained base polynomial",
            "exceptional_content": "c2_3^26*c3_5^2 retained and audited",
            "frozen_witness": "Omega8 is a unit in K[Z]/(r_final), dimension 14",
        },
        "licenses": [
            "r8_1 and r8_3 independently recombine through the checked left syzygy to the exact Psi8",
            "Psi8 is the explicit necessary compatibility of the prior rank-two affine block",
            "the landed constrained depth-6/7 substitution clears to the exact Omega8 without a new inversion",
            "Omega8 excludes the entire frozen degree-14 compatible witness algebra",
            "Omega8 is not generated by the prior A, OB, Phi ideal because those vanish in that witness algebra",
        ],
        "consumed_frozen_semantics": [
            "the boundary triple is necessary for extension under P1-P5, S2, the pin, and declared guards",
            "the compatibility module's embedded matrices and residual digests describe the constrained depth-6/7 solve",
            "the uniform-Lambda finite algebra is a compatible witness for A=OB=Phi=0 with det5 invertible",
        ],
        "does_not_license": [
            "equivalence with the complete depth-eight or actual-source fiber",
            "emptiness of a component of Z(Phi) cap X_b or the off-slice zero locus of Omega8",
            "nonzerodivisor or K-rationality claims",
            "row 3, r8_2, depth nine, recursive stratification, or nonlinear lifting",
            "H8, H3, source membership, verdict promotion, or a (75,125) status change",
            "any graph claim or transport authority",
        ],
        "first_open_obligation": (
            "decide the off-slice locus Z(Omega8) cap Z(Phi) cap X_b or "
            "supply a separately bounded component model; do not infer it "
            "from the frozen degree-14 witness"),
        "graph_effect": "NONE",
    }


def build_fixture(native_root=NATIVE_ROOT):
    root = Path(native_root)
    bindings = {name: normalized_sha256(root / name)
                for name in sorted(NATIVE_BINDINGS)}
    require(bindings == dict(sorted(NATIVE_BINDINGS.items())), "B1",
            "native Psi8/Omega8 inputs drifted before freeze")
    return {
        "schema": SCHEMA,
        "binding_digest_algo": "sha256-lf-normalized",
        "source_bindings": bindings,
        "gp_prerequisite": {
            "fixture": "fixtures/jc_b0_depth8_free_plane/v1.json",
            "sha256": EXPECTED_PREVIOUS_FIXTURE_SHA256,
            "required_result": "rank two with left syzygy (c2_3,0,2)",
        },
        "psi8_certificate": json.loads((root / PSI_CERT).read_text(
            encoding="utf-8")),
        "pullback_certificate": json.loads((root / PULLBACK_CERT).read_text(
            encoding="utf-8")),
        "compatibility_module": json.loads((root / MODULE_CERT).read_text(
            encoding="utf-8")),
        "uniform_lambda": json.loads((root / UNIFORM_CERT).read_text(
            encoding="utf-8")),
        "projection": _expected_projection(),
        "authority_boundary": (
            "The adapter proves an exact necessary depth-eight scalar and "
            "excludes one frozen finite compatible witness. It does not "
            "model a component, complete source fiber, or graph authority."),
    }


def _check_prerequisite(value):
    require(value == {
        "fixture": "fixtures/jc_b0_depth8_free_plane/v1.json",
        "sha256": EXPECTED_PREVIOUS_FIXTURE_SHA256,
        "required_result": "rank two with left syzygy (c2_3,0,2)",
    }, "C1", "prior GP block prerequisite changed")
    require(hashlib.sha256(PREVIOUS_FIXTURE.read_bytes()).hexdigest() ==
            EXPECTED_PREVIOUS_FIXTURE_SHA256, "C2",
            "prior GP block fixture is not current")


def _validate_certificate_custody(fixture):
    psi = fixture["psi8_certificate"]
    pullback = fixture["pullback_certificate"]
    module = fixture["compatibility_module"]
    uniform = fixture["uniform_lambda"]
    require(psi.get("id") == "f2_h3_b0_depth8_psi8" and
            psi.get("schema_version") == 1 and
            psi.get("verdict") == "DEPTH8_SCALAR_NONZERO_NONUNIT", "N1",
            "Psi8 certificate identity or verdict changed")
    require(pullback.get("id") == "f2_h3_b0_psi8_constrained_pullback" and
            pullback.get("schema") == "constrained_pullback/1" and
            pullback.get("verdict") ==
            "OMEGA8_NOT_IN_PRIOR_IDEAL__UNIT_ON_FROZEN_WITNESS", "N2",
            "Omega8 certificate identity, schema, or verdict changed")
    require(module.get("verdict") == "COMPATIBILITY_PACKET_EXACT" and
            uniform.get("verdict") == "GENERIC_NONZERO_DIVISOR", "N3",
            "parent compatibility certificates changed grade")
    bindings = fixture["source_bindings"]
    require(all(bindings.get(name) == digest
                for name, digest in psi["bindings"].items()) and
            all(bindings.get(name) == digest
                for name, digest in psi["source_digests"].items()) and
            all(bindings.get(name) == digest
                for name, digest in pullback["bindings"].items()), "N4",
            "nested native custody digests disagree")
    require(pullback["bindings"][PSI_CERT] == bindings[PSI_CERT] and
            pullback["bindings"][MODULE_CERT] == bindings[MODULE_CERT] and
            pullback["bindings"][UNIFORM_CERT] == bindings[UNIFORM_CERT],
            "N5", "pullback is not welded to the frozen parents")
    require(psi["field"] == pullback["ring"]["coefficient_field"] ==
            module["ring"]["coefficient_field"] ==
            "K = QQ[t]/(15*t**3 + 1)", "N6",
            "coefficient field or pin changed")
    require(tuple(pullback["ring"]["fiber_coordinates"]) == FIBER and
            tuple(pullback["ring"]["base_coordinates"]) == BASE and
            pullback["ring"]["ring_variable_order"] ==
            psi["ring_variable_order"], "N7",
            "ring order or coordinate packs changed")
    require(pullback["source_representable"] is False and
            pullback["faces_cleared"] == 0 and
            "equivalent" in pullback["semantic_grade"]["is_not"] and
            any("component-wide" in item for item in pullback["refusals"]) and
            pullback["witness"]["slice"] == {
                "c2_1": "0", "c2_2": "0", "c2_3": "1", "c3_5": "1",
                "c7_10": "0", "c7_9": "0", "p": "1",
            },
            "N8", "native scope or refusal boundary widened")


def _validate_psi8(fixture):
    psi = fixture["psi8_certificate"]
    r1 = from_sparse(psi["r8_1"]["sparse"])
    r3 = from_sparse(psi["r8_3"]["sparse"])
    scalar = from_sparse(psi["Psi8"]["sparse"])
    require((len(r1), len(r3), len(scalar)) == (552, 704, 709) and
            sparse_digest(r1) == psi["r8_1"]["sha256"] and
            sparse_digest(r3) == psi["r8_3"]["sha256"] and
            sparse_digest(scalar) == psi["Psi8"]["sha256"], "A1",
            "residual sparse body or digest changed")
    a = variable("c2_3")
    recomputed = padd(pmul(a, r1), pscale(r3, 2))
    require(recomputed == scalar, "A2",
            "Psi8 is not c2_3*r8_1 + 2*r8_3")
    require(padd(pmul(a, r1), pscale(r3, -2)) != scalar and
            padd(r1, pscale(r3, 2)) != scalar and
            padd(pmul(a, r1), r3) != scalar, "A3",
            "syzygy scalars are not load-bearing")
    require(isinstance(psi["r8_2"], str) and
            psi["r8_2"].startswith("NOT BUILT") and
            "middle coordinate 0" in psi["r8_2"] and
            psi["independence_theorem"]["weights"]["row3_c9_6"] ==
            "NONZERO", "A4", "missing-middle-coordinate rationale changed")
    require(all(degree(poly, name) == 0 for poly in (r1, r3, scalar)
                for name in ("c7_4", "c8_5", "c5_7", "c8_12", "c4_5")) and
            all(degree(poly, "t") < 3 for poly in (r1, r3, scalar)), "A5",
            "restriction or field-pin normal form changed")
    fiber_degrees = {name: degree(scalar, name) for name in FIBER}
    require(fiber_degrees == psi["Psi8"]["fiber_degrees"] and
            all(fiber_degrees[name] == 1 for name in SOLVED) and
            fiber_degrees["c7_4"] == fiber_degrees["c8_5"] == 0 and
            scalar and psi["decision"]["nonzero_nonunit"] is True and
            psi["decision"]["unit_incompatible"] is False, "A6",
            "Psi8 nonzero/nonunit affine classification changed")

    # Instantiate the previous GP block's augmented determinant identity.
    zero = {}
    m8 = [
        [zero, pscale(product(a, variable("t")), -5), r1],
        [pscale(product(power(a, 4), variable("c3_5")), Fraction(-5, 8)),
         zero, variable("r8_2")],
        [zero, pscale(product(power(a, 2), variable("t")), Fraction(5, 2)),
         r3],
    ]
    audited = pscale(product(power(a, 5), variable("c3_5"),
                             variable("t")), Fraction(-25, 16))
    require(determinant(m8) == pmul(audited, scalar) and
            degree(determinant(m8), "r8_2") == 0, "A7",
            "residual-to-block compatibility identity failed")
    return r1, r3, scalar


def _validate_pullback(fixture, scalar):
    receipt = fixture["pullback_certificate"]
    module = fixture["compatibility_module"]
    block1, block2, block3 = module["blocks"]
    matrix = [[unser(value) for value in row] for row in block1["matrix"]]
    residuals = [from_sparse(value) for value in
                 receipt["replay_inputs"]["block1_residuals"]]
    closed_c86 = from_sparse(receipt["replay_inputs"][
        "block2_closed_form"])
    residual_e321 = from_sparse(receipt["replay_inputs"][
        "block3_residual_E321"])
    det5 = determinant(matrix)
    require(len(det5) == 6 and
            module_digest(det5) == block1["determinant_sha256"] and
            [module_digest(poly) for poly in residuals] ==
            block1["residual_sha256"] and
            module_digest(closed_c86) ==
            module["fiber_semantics"]["block2_closed_form_sha256"] and
            module_digest(residual_e321) ==
            block3["residual_sha256"][1], "D1",
            "landed block solve weld failed")
    require(unser(block2["matrix"][0][0]) ==
            pscale(product(variable("c2_3"), variable("t")), -5) and
            unser(block3["matrix"][1][0]) ==
            pscale(product(power(variable("c2_3"), 4),
                           variable("c3_5")), Fraction(-5, 8)), "D2",
            "block pivot changed")

    numerators = {}
    for column, name in enumerate(U1):
        replaced = [[pscale(residuals[row], -1)
                     if current == column else matrix[row][current]
                     for current in range(5)] for row in range(5)]
        numerators[name] = determinant(replaced)
    require(all(numerators.values()) and
            all(not (support(poly) & set(FIBER))
                for poly in numerators.values()), "D3",
            "Cramer numerator is zero or retains a fiber coordinate")

    parts = coeff_parts(scalar, set(SOLVED))
    require(all(len(key) <= 1 and (not key or key[0][1] == 1)
                for key in parts) and
            all(not (support(poly) & set(FIBER)) for poly in parts.values()) and
            {key[0][0] if key else "1": len(poly)
             for key, poly in parts.items()} ==
            receipt["psi8_fiber_affine_split"]["terms_by_coordinate"], "D4",
            "Psi8 fiber-affine split changed")

    a, c, t = variable("c2_3"), variable("c3_5"), variable("t")
    det5_sq = pmul(det5, det5)
    a4c, a3c = product(power(a, 4), c), product(power(a, 3), c)
    denominator = pscale(product(a4c, t, det5_sq), 5)

    def assemble(block3_sign):
        out = pmul(denominator, parts.get((), {}))
        for name in U1:
            coefficient = parts.get(((name, 1),))
            if coefficient:
                cofactor = pscale(product(a4c, t, det5), 5)
                out = padd(out, product(cofactor, coefficient,
                                         numerators[name]))
        coefficient = parts.get((("c8_6", 1),))
        if coefficient:
            out = padd(out, product(a3c, det5, coefficient, closed_c86))
        coefficient = parts.get((("c7_5", 1),))
        if coefficient:
            out = padd(out, product(pscale(t, block3_sign), coefficient,
                                     residual_e321))
        return pin(out)

    omega = from_sparse(receipt["Omega8"]["sparse"])
    recomputed = assemble(8)
    require(recomputed == omega and len(omega) == 4123 and
            sparse_digest(omega) == receipt["Omega8"]["sha256"] and
            module_digest(omega) ==
            receipt["Omega8"]["sha256_module_serialization"], "D5",
            "constrained substitution does not reproduce Omega8")
    require(assemble(-8) != omega and
            receipt["denominator"]["formula"] ==
            "5*c2_3**4*c3_5*t*det5**2" and
            receipt["denominator"]["new_inversions"] == [] and
            receipt["denominator"]["summand_cofactors"]["c7_5_part"] ==
            "8*t", "D6", "denominator ledger or block-3 sign changed")
    require(not (support(omega) & set(FIBER)) and
            sorted(support(omega)) == receipt["Omega8"]["support"] ==
            sorted(set(BASE) | {"t"}), "D7",
            "Omega8 does not descend exactly to the base")

    exceptional = receipt["exceptional_factors"]
    primitive = strip_monomial(omega, {"c2_3": 26, "c3_5": 2})
    require(primitive is not None and
            mindegree(omega, "c2_3") == exceptional["mindeg_c2_3"] == 26 and
            mindegree(omega, "c3_5") == exceptional["mindeg_c3_5"] == 2 and
            mindegree(primitive, "c2_3") ==
            mindegree(primitive, "c3_5") == 0 and
            sparse_digest(primitive) ==
            exceptional["primitive_part_sha256"] and
            module_digest(primitive) ==
            exceptional["primitive_part_sha256_module_serialization"] and
            product(power(a, 26), power(c, 2), primitive) == omega and
            exceptional["policy"] == "REPORTED, NOT CANCELLED", "D8",
            "exceptional-factor ledger or primitive part changed")
    return omega, denominator, det5


def _validate_witness(fixture, omega, denominator):
    receipt = fixture["pullback_certificate"]
    uniform = fixture["uniform_lambda"]
    witness = receipt["witness"]
    modulus = triples(witness["r_final"])
    xbar = triples(witness["Xbar"])
    ybar = triples(witness["Ybar"])
    sliced = {name: from_sparse(witness[name]) for name in
              ("sliced_A", "sliced_OB", "sliced_Phi", "sliced_det5")}
    expected_slice = {
        "c2_1": "0", "c2_2": "0", "c2_3": "1", "c3_5": "1",
        "c7_10": "0", "c7_9": "0", "p": "1",
    }
    require(witness["slice"] == expected_slice and
            witness["slice_codimension"] == 7, "W1",
            "frozen witness slice changed")
    fixed = {name: _fraction(value, "W2")
             for name, value in witness["slice"].items()}

    def reduce_k(poly):
        return kpoly_divmod(poly, modulus)[1]

    def multiply_k(left, right):
        return reduce_k(kpoly_mul(left, right))

    def eval_x(poly):
        coefficients = coeffs_in(poly, "c7_8")
        result, xpower = [KZERO], [KONE]
        for exponent in range(max(coefficients, default=0) + 1):
            if exponent:
                xpower = multiply_k(xpower, xbar)
            if exponent in coefficients:
                coefficient = to_kpoly(pin(coefficients[exponent]), "c8_11")
                result = reduce_k(kpoly_add(
                    result, multiply_k(coefficient, xpower)))
        return reduce_k(result)

    def eval_xy(poly):
        coefficients = coeffs_in(poly, "c8_10")
        result, ypower = [KZERO], [KONE]
        for exponent in range(max(coefficients, default=0) + 1):
            if exponent:
                ypower = multiply_k(ypower, ybar)
            if exponent in coefficients:
                result = reduce_k(kpoly_add(
                    result, multiply_k(eval_x(pin(coefficients[exponent])),
                                       ypower)))
        return reduce_k(result)

    derivative = [kscale(modulus[index], index)
                  for index in range(1, len(modulus))]
    squarefree_gcd = kpoly_gcd(modulus, derivative)
    require(len(modulus) - 1 == witness["dim_K"] ==
            uniform["chain"]["r_final_degree"] == 14 and
            len(squarefree_gcd) - 1 == 0 and
            eval_xy(sliced["sliced_A"]) == [KZERO] and
            eval_xy(sliced["sliced_OB"]) == [KZERO] and
            eval_xy(sliced["sliced_Phi"]) == [KZERO], "W3",
            "finite compatible witness equations or modulus failed")
    det5_image = to_kpoly(sliced["sliced_det5"], "c8_11")
    require(len(kpoly_gcd(det5_image, modulus)) - 1 == 0, "W4",
            "det5 is not a unit on the frozen witness")

    omega_image = eval_xy(specialize(omega, fixed))
    denominator_image = to_kpoly(specialize(denominator, fixed), "c8_11")
    omega_gcd = kpoly_gcd(omega_image, modulus)
    require(omega_image != [KZERO] and len(omega_image) - 1 ==
            witness["Omega8_in_R_degree"] == 13 and
            [str(entry) for coefficient in omega_image for entry in coefficient]
            == witness["Omega8_in_R"] and len(omega_gcd) - 1 ==
            witness["gcd_with_r_final_degree"] == 0 and
            witness["Omega8_is_a_unit_in_R"] is True and
            len(kpoly_gcd(denominator_image, modulus)) - 1 == 0, "W5",
            "Omega8 coprimality/unit witness failed")
    require(receipt["decision"]["prior_ideal_generated"] is False and
            receipt["decision"]["unit_on_frozen_witness_algebra"] is True and
            any("component" in item
                for item in receipt["decision"]["unresolved"]), "W6",
            "finite-witness conclusion widened")
    return {
        "dimension": 14,
        "slice_codimension": 7,
        "omega_image_degree": 13,
        "gcd_degree": 0,
        "omega_unit": True,
    }


def validate_fixture_value(fixture):
    require(set(fixture) == {
        "schema", "binding_digest_algo", "source_bindings",
        "gp_prerequisite", "psi8_certificate", "pullback_certificate",
        "compatibility_module", "uniform_lambda", "projection",
        "authority_boundary",
    }, "F1", "fixture shape changed")
    require(fixture["schema"] == SCHEMA and
            fixture["binding_digest_algo"] == "sha256-lf-normalized", "F2",
            "fixture schema or digest algorithm changed")
    require(fixture["source_bindings"] ==
            dict(sorted(NATIVE_BINDINGS.items())), "F3",
            "frozen native binding changed")
    require(fixture["projection"] == _expected_projection(), "M1",
            "authority projection or graph effect changed")
    _check_prerequisite(fixture["gp_prerequisite"])
    _validate_certificate_custody(fixture)
    r1, r3, scalar = _validate_psi8(fixture)
    omega, denominator, _ = _validate_pullback(fixture, scalar)
    witness = _validate_witness(fixture, omega, denominator)
    return {
        "r8_terms": [len(r1), len(r3)],
        "psi8_terms": len(scalar),
        "psi8_class": "NONZERO_NONUNIT_FIBER_AFFINE",
        "omega8_terms": len(omega),
        "exceptional_content": "c2_3^26*c3_5^2",
        "witness": witness,
    }


def check_native_bindings(fixture, native_root=NATIVE_ROOT):
    root = Path(native_root)
    require(root.exists(), "B2", "sibling JC checkout is absent")
    for name, expected in fixture["source_bindings"].items():
        require((root / name).exists(), "B3", "native binding absent: " + name)
        require(normalized_sha256(root / name) == expected, "B4",
                "native binding changed: " + name)


def report_from_checked_fixture(fixture, checked):
    report = copy.deepcopy(fixture["projection"])
    report.update({
        "schema": SCHEMA,
        "verdict": "VERIFIED_NECESSARY_PSI8__FROZEN_WITNESS_EXCLUDED",
        "checked_instance": checked,
        "source_bindings": fixture["source_bindings"],
        "gp_prerequisite": fixture["gp_prerequisite"],
        "evidence_envelope": {
            "schema": SCHEMA,
            "checked_proposition": (
                "the prior necessary affine block has explicit scalar Psi8; "
                "its exact constrained pullback Omega8 is a unit only on the "
                "named frozen degree-14 compatible witness"),
            "licenses": fixture["projection"]["licenses"],
            "consumed_frozen_semantics": fixture["projection"][
                "consumed_frozen_semantics"],
            "outstanding_premises": fixture["projection"][
                "does_not_license"],
            "first_open_obligation": fixture["projection"][
                "first_open_obligation"],
            "graph_effect": "NONE",
            "authority_boundary": fixture["authority_boundary"],
        },
    })
    return report


def verify_fixture(path=DEFAULT_FIXTURE, check_bindings=False,
                   native_root=NATIVE_ROOT):
    raw = Path(path).read_bytes()
    if EXPECTED_FIXTURE_SHA256 is not None:
        require(hashlib.sha256(raw).hexdigest() == EXPECTED_FIXTURE_SHA256,
                "F4", "frozen Psi8/Omega8 fixture digest changed")
    fixture = json.loads(raw.decode("utf-8"))
    checked = validate_fixture_value(fixture)
    if check_bindings:
        check_native_bindings(fixture, native_root)
    return report_from_checked_fixture(fixture, checked)


def native_replay(native_root=NATIVE_ROOT):
    results = {}
    for script, summary, timeout in (
        ("f2_h3_b0_depth8_psi8.py", "22/22 checks", 60),
        ("f2_h3_b0_psi8_constrained_pullback.py",
         "18/18 checks passed", 120),
    ):
        completed = subprocess.run(
            [sys.executable, str(Path(native_root) / script), "--quiet"],
            cwd=str(native_root), capture_output=True, text=True,
            timeout=timeout, check=False)
        require(completed.returncode == 0 and summary in completed.stdout,
                "N9", "native replay failed: " + script + " " +
                completed.stderr.strip())
        results[script] = summary
    return {"verdict": "VERIFIED_NATIVE_40_OF_40",
            "checks": results, "graph_effect": "NONE"}


def _atomic_write(path, value, force=False):
    path = Path(path)
    if path.exists() and not force:
        raise Depth8ResidualEvidenceError(
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
    except (Depth8ResidualEvidenceError, OSError, ValueError,
            json.JSONDecodeError) as exc:
        print("REFUSED: %s" % exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
