#!/usr/bin/env python3
"""Replay the JC b=0 compatibility class as bounded standalone evidence.

The native producer proves that the denominator-cleared compatibility class
``Phi_b0_compat`` is neither zero nor a unit on one exact localized,
materialized-depth model.  Fixture construction executes that producer and
freezes only the bounded affine block, Cramer data, and two quotient-algebra
witnesses.  Ordinary replay is independent exact arithmetic over

    K = QQ[t]/(15*t^3 + 1)

and never imports the JC producer.

This is intentionally not a graph claim.  The result concerns a ring element,
not emptiness/nonemptiness of the parent research problem, and has graph effect
NONE.
"""

from __future__ import annotations

import argparse
import contextlib
import copy
import hashlib
import importlib.util
import io
import json
import os
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
NATIVE_ROOT = ROOT.parent / "math-stuff" / "d2_plane_72_108"
DEFAULT_FIXTURE = ROOT / "fixtures" / "jc_b0_compatibility" / "class_v1.json"
DEFAULT_REVIEW = ROOT / "review" / "jc-h3-b0-compatibility-v1.json"
SCHEMA = "localized_ring_element_class_v1"
EXPECTED_FIXTURE_SHA256 = (
    "faeda936b84f5f4ba68f55eeb4cc00d34a6c5f7e6e60f7312e4e3f21f1ff0e95")

NATIVE_BINDINGS = {
    "F2_H3_B0_COMMON_ROOT.md":
        "ca5b6d537d945971cf315791feb5cb7ae44e9154172b6ff42013b61854dbb919",
    "F2_H3_B0_UNIFORM_LAMBDA.md":
        "b9535626c4ba48f69803e81f58976a82dfe2c629a31f5d9324a05de1e4a85127",
    "H3_LOCALIZED_CAS_PILOT.md":
        "2b34738b2fa9175ca37de304e96dc83bef8100b6b2cd66b4b06ad2bfa1f7b618",
    "F2_H3_B0_COMPATIBILITY_MODULE.md":
        "33726b89112a0562b89111e80cdc8f9248287e82d63c1f3fbad44919fabccb96",
    "f2_h3_b0_common_root.json":
        "a2dca1966424f7cee775257d8f145ba68a6949c7dea8a7aa698415956dac65cf",
    "f2_h3_b0_common_root.py":
        "d3a73afb23c55cbc5a775bec442897bd57830abca355ea93a35b16f0e87d1a43",
    "f2_h3_b0_compatibility_module.json":
        "944f95d762e05d3dec4ffa6599b4f0d1d2674e4127e5d168712a62de50291840",
    "f2_h3_b0_compatibility_module.py":
        "be70f604a328eba1944bf6593a83437fbd54f61cfdbca76da76011c92adf0572",
    "f2_h3_b0_uniform_lambda.json":
        "499a7c0975ac01883ecf4b7b9be14e9b00dd4284f7688810aaa175ca86ada3fd",
    "f2_h3_b0_uniform_lambda.py":
        "bbd626c4fab2827a7fd8106e2deea9fa031e3cfefc0967055c9ee2ee8f6f7ea3",
    "f2_h3_source_incidence_bezout_adapter.py":
        "92affca372ebf4e29abce5d8371ef68c0c03d094976f5795e9391c6d76f8b949",
    "lean/JC/SourceIncidenceBezout.lean":
        "8cc8c1a8aeedfe2140270626bd7fa9b0556dc4231586fbaf8878bb2fcc0713bf",
}

BASE_VARS = (
    "c2_1", "c2_2", "c2_3", "c3_5", "c7_8", "c7_9", "c7_10",
    "c8_10", "c8_11", "p",
)
FIBER_COLS = ("c8_9", "c7_7", "c8_8", "c7_6", "c8_7")
SLICE_VARS = ("c7_8", "c8_10", "c8_11")
K_ZERO = (Fraction(0), Fraction(0), Fraction(0))
K_ONE = (Fraction(1), Fraction(0), Fraction(0))


class CompatibilityEvidenceError(ValueError):
    """The frozen class evidence, arithmetic, or authority scope drifted."""


def require(condition, check_id, message):
    if not condition:
        raise CompatibilityEvidenceError("%s: %s" % (check_id, message))


def normalized_sha256(path):
    return hashlib.sha256(
        Path(path).read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True,
                       ensure_ascii=True) + "\n").encode("utf-8")


def _q(value):
    return value if isinstance(value, Fraction) else Fraction(value)


def _k(value=0):
    if isinstance(value, tuple):
        return tuple(map(_q, value))
    return (_q(value), Fraction(0), Fraction(0))


def _kadd(left, right):
    return tuple(a + b for a, b in zip(left, right))


def _kneg(value):
    return tuple(-item for item in value)


def _ksub(left, right):
    return _kadd(left, _kneg(right))


def _kmul(left, right):
    raw = [Fraction(0)] * 5
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            raw[i + j] += a * b
    # t^3 = -1/15 and t^4 = -t/15.
    for degree in range(4, 2, -1):
        raw[degree - 3] -= raw[degree] / 15
    return tuple(raw[:3])


def _kpow(value, exponent):
    result = K_ONE
    base = value
    power = exponent
    while power:
        if power & 1:
            result = _kmul(result, base)
        base = _kmul(base, base)
        power //= 2
    return result


def _solve_rational(matrix, rhs):
    work = [list(map(_q, row)) + [_q(value)]
            for row, value in zip(matrix, rhs)]
    size = len(work)
    for column in range(size):
        pivot = next((row for row in range(column, size)
                      if work[row][column]), None)
        require(pivot is not None, "K1", "singular rational system")
        work[column], work[pivot] = work[pivot], work[column]
        scale = work[column][column]
        work[column] = [value / scale for value in work[column]]
        for row in range(size):
            if row == column:
                continue
            factor = work[row][column]
            if factor:
                work[row] = [a - factor * b
                             for a, b in zip(work[row], work[column])]
    return [work[row][-1] for row in range(size)]


def _kinv(value):
    require(value != K_ZERO, "K2", "attempted to invert zero in K")
    columns = [_kmul(value, basis) for basis in (
        K_ONE, (Fraction(0), Fraction(1), Fraction(0)),
        (Fraction(0), Fraction(0), Fraction(1)))]
    matrix = [[columns[column][row] for column in range(3)]
              for row in range(3)]
    return tuple(_solve_rational(matrix, [1, 0, 0]))


@dataclass
class Poly:
    variables: tuple[str, ...]
    terms: dict[tuple[int, ...], tuple[Fraction, Fraction, Fraction]]

    def __post_init__(self):
        cleaned = {tuple(m): tuple(c) for m, c in self.terms.items()
                   if tuple(c) != K_ZERO}
        self.terms = cleaned


def _pzero(variables):
    return Poly(tuple(variables), {})


def _pconst(variables, coefficient):
    value = _k(coefficient)
    return Poly(tuple(variables), {} if value == K_ZERO else {
        (0,) * len(variables): value})


def _pvar(variables, name):
    variables = tuple(variables)
    powers = [0] * len(variables)
    powers[variables.index(name)] = 1
    return Poly(variables, {tuple(powers): K_ONE})


def _padd(left, right, scale=K_ONE):
    require(left.variables == right.variables, "P1", "polynomial ring mismatch")
    result = dict(left.terms)
    for monomial, coefficient in right.terms.items():
        result[monomial] = _kadd(
            result.get(monomial, K_ZERO), _kmul(scale, coefficient))
        if result[monomial] == K_ZERO:
            del result[monomial]
    return Poly(left.variables, result)


def _pneg(value):
    return Poly(value.variables, {m: _kneg(c) for m, c in value.terms.items()})


def _pmul(left, right):
    require(left.variables == right.variables, "P1", "polynomial ring mismatch")
    result = {}
    for lm, lc in left.terms.items():
        for rm, rc in right.terms.items():
            monomial = tuple(a + b for a, b in zip(lm, rm))
            result[monomial] = _kadd(
                result.get(monomial, K_ZERO), _kmul(lc, rc))
            if result[monomial] == K_ZERO:
                del result[monomial]
    return Poly(left.variables, result)


def _ppow(value, exponent):
    result = _pconst(value.variables, 1)
    base = value
    power = exponent
    while power:
        if power & 1:
            result = _pmul(result, base)
        base = _pmul(base, base)
        power //= 2
    return result


def _pdet(matrix):
    size = len(matrix)
    require(size and all(len(row) == size for row in matrix), "P2",
            "determinant matrix is not square")
    if size == 1:
        return matrix[0][0]
    result = _pzero(matrix[0][0].variables)
    for column in range(size):
        minor = [[matrix[row][other] for other in range(size)
                  if other != column] for row in range(1, size)]
        term = _pmul(matrix[0][column], _pdet(minor))
        result = _padd(result, term, _k(-1 if column & 1 else 1))
    return result


def _pdegree(value, variable):
    index = value.variables.index(variable)
    return max((m[index] for m in value.terms), default=-1)


def _pcoeff(value, variable, exponent):
    index = value.variables.index(variable)
    output = {}
    for monomial, coefficient in value.terms.items():
        if monomial[index] == exponent:
            powers = list(monomial)
            powers[index] = 0
            output[tuple(powers)] = coefficient
    return Poly(value.variables, output)


def _pspecialize(value, target_variables, fixed):
    target_variables = tuple(target_variables)
    result = _pzero(target_variables)
    targets = {name: _pvar(target_variables, name) for name in target_variables}
    for monomial, coefficient in value.terms.items():
        term = _pconst(target_variables, coefficient)
        for name, exponent in zip(value.variables, monomial):
            if not exponent:
                continue
            if name in targets:
                factor = targets[name]
            else:
                require(name in fixed, "P3", "missing specialization: " + name)
                factor = _pconst(target_variables, fixed[name])
            term = _pmul(term, _ppow(factor, exponent))
        result = _padd(result, term)
    return result


def _to_univariate(value, variable):
    index = value.variables.index(variable)
    degree = _pdegree(value, variable)
    result = [K_ZERO for _ in range(max(degree + 1, 1))]
    for monomial, coefficient in value.terms.items():
        require(all(power == 0 for i, power in enumerate(monomial)
                    if i != index), "P4", "polynomial is not univariate")
        result[monomial[index]] = coefficient
    return _utrim(result)


def _utrim(value):
    result = [tuple(item) for item in value]
    while len(result) > 1 and result[-1] == K_ZERO:
        result.pop()
    return result


def _uadd(left, right, scale=K_ONE):
    size = max(len(left), len(right))
    result = []
    for index in range(size):
        a = left[index] if index < len(left) else K_ZERO
        b = right[index] if index < len(right) else K_ZERO
        result.append(_kadd(a, _kmul(scale, b)))
    return _utrim(result)


def _umul(left, right):
    result = [K_ZERO] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] = _kadd(result[i + j], _kmul(a, b))
    return _utrim(result)


def _udivmod(dividend, divisor):
    numerator = _utrim(dividend)
    denominator = _utrim(divisor)
    require(denominator != [K_ZERO], "U1", "division by zero polynomial")
    quotient = [K_ZERO] * max(1, len(numerator) - len(denominator) + 1)
    inverse_lead = _kinv(denominator[-1])
    while numerator != [K_ZERO] and len(numerator) >= len(denominator):
        shift = len(numerator) - len(denominator)
        factor = _kmul(numerator[-1], inverse_lead)
        quotient[shift] = _kadd(quotient[shift], factor)
        subtractor = [K_ZERO] * shift + [_kmul(factor, item)
                                         for item in denominator]
        numerator = _uadd(numerator, subtractor, _k(-1))
    return _utrim(quotient), _utrim(numerator)


def _umonic(value):
    value = _utrim(value)
    require(value != [K_ZERO], "U2", "zero polynomial has no monic form")
    inverse = _kinv(value[-1])
    return [_kmul(inverse, item) for item in value]


def _ugcd(left, right):
    a, b = _utrim(left), _utrim(right)
    while b != [K_ZERO]:
        a, b = b, _udivmod(a, b)[1]
    return _umonic(a)


def _uegcd(left, right):
    old_r, r = _utrim(left), _utrim(right)
    old_s, s = [K_ONE], [K_ZERO]
    old_t, t = [K_ZERO], [K_ONE]
    while r != [K_ZERO]:
        quotient, remainder = _udivmod(old_r, r)
        old_r, r = r, remainder
        old_s, s = s, _uadd(old_s, _umul(quotient, s), _k(-1))
        old_t, t = t, _uadd(old_t, _umul(quotient, t), _k(-1))
    inverse = _kinv(old_r[-1])
    return ([ _kmul(inverse, item) for item in old_r],
            [ _kmul(inverse, item) for item in old_s],
            [ _kmul(inverse, item) for item in old_t])


def _rred(value, modulus):
    return _udivmod(value, modulus)[1]


def _rmul(left, right, modulus):
    return _rred(_umul(left, right), modulus)


def _rinv(value, modulus):
    gcd, coefficient, _other = _uegcd(value, modulus)
    require(len(gcd) == 1 and gcd[0] == K_ONE, "U3",
            "quotient-ring element is not invertible")
    return _rred(coefficient, modulus)


def _rpow(value, exponent, modulus):
    result = [K_ONE]
    base = _rred(value, modulus)
    power = exponent
    while power:
        if power & 1:
            result = _rmul(result, base, modulus)
        base = _rmul(base, base, modulus)
        power //= 2
    return result


def _eval_in_quotient(value, assignments, modulus):
    result = [K_ZERO]
    for monomial, coefficient in value.terms.items():
        term = [coefficient]
        for name, exponent in zip(value.variables, monomial):
            if exponent:
                require(name in assignments, "U4", "missing quotient value: " + name)
                term = _rmul(term, _rpow(assignments[name], exponent, modulus),
                             modulus)
        result = _uadd(result, term)
        result = _rred(result, modulus)
    return result


def _encode_poly(native, variables):
    variables = tuple(variables)
    output = {}
    for monomial, coefficient in native.items():
        powers = dict(monomial)
        t_degree = powers.pop("t", 0)
        require(0 <= t_degree <= 2 and set(powers) <= set(variables), "E1",
                "producer polynomial is outside the frozen K-ring")
        exponents = tuple(powers.get(name, 0) for name in variables)
        value = [Fraction(0)] * 3
        value[t_degree] = _q(coefficient)
        output[exponents] = _kadd(output.get(exponents, K_ZERO), tuple(value))
    return {
        "variables": list(variables),
        "terms": [[list(monomial), [str(item) for item in coefficient]]
                  for monomial, coefficient in sorted(output.items())
                  if coefficient != K_ZERO],
    }


def _encode_univariate(native):
    return [[str(_q(item)) for item in coefficient] for coefficient in native]


def _decode_k(value, where):
    require(isinstance(value, list) and len(value) == 3 and
            all(isinstance(item, str) for item in value), "D1",
            where + " is not a canonical K triple")
    parsed = tuple(Fraction(item) for item in value)
    require([str(item) for item in parsed] == value, "D2",
            where + " has a noncanonical K coefficient")
    return parsed


def _decode_poly(value, where):
    require(isinstance(value, dict) and set(value) == {"variables", "terms"},
            "D3", where + " has the wrong polynomial shape")
    variables = value["variables"]
    require(isinstance(variables, list) and len(variables) == len(set(variables))
            and all(isinstance(name, str) and name for name in variables),
            "D4", where + " variables are not unique names")
    terms = {}
    previous = None
    for position, record in enumerate(value["terms"]):
        require(isinstance(record, list) and len(record) == 2 and
                isinstance(record[0], list), "D5",
                "%s term %d is malformed" % (where, position))
        monomial = tuple(record[0])
        require(len(monomial) == len(variables) and
                all(type(power) is int and 0 <= power <= 64
                    for power in monomial), "D6", where + " exponent invalid")
        require(previous is None or previous < monomial, "D7",
                where + " terms are not strictly ordered")
        coefficient = _decode_k(record[1], where + " coefficient")
        require(coefficient != K_ZERO, "D8", where + " contains zero term")
        terms[monomial] = coefficient
        previous = monomial
    return Poly(tuple(variables), terms)


def _decode_univariate(value, where):
    require(isinstance(value, list) and value, "D9", where + " is empty")
    result = [_decode_k(item, where + " coefficient") for item in value]
    require(result == _utrim(result), "D10", where + " has trailing zeros")
    return result


def _projection():
    return {
        "object": "Phi_b0_compat",
        "object_sort": "LOCALIZED_COORDINATE_RING_ELEMENT",
        "coefficient_domain": "K = QQ[t]/(15*t^3+1)",
        "model": {
            "name": "X_b_materialized_depth_6_7",
            "presentation": "Delta-substituted S2 b=0 wall base",
            "equations": ["b=0", "R=0", "A=0", "OB=0"],
            "guards": ["c2_3", "p", "det5"],
            "point_universe": "ALGEBRAIC_EXTENSIONS_OF_K",
        },
        "definition": {
            "source_class": "Lambda = VD - (3/2)*c2_3*t*E321",
            "pushforward": "Phi_b0_compat = det5^2 * Lambda|det5-solve",
            "clearing_exponent": 2,
        },
        "claims": {
            "nonzero": "VERIFIED_BY_NONZERO_QUADRATIC_QUOTIENT_IMAGE",
            "unit": "REFUTED_BY_ZERO_IN_NONTRIVIAL_DEGREE_14_QUOTIENT",
            "nonzerodivisor": "OPEN_NOT_CLAIMED",
        },
        "first_open_obligation": (
            "whether Phi_b0_compat is a nonzerodivisor on every component "
            "of X_b; this requires component/primary evidence"),
        "module_rendezvous": {
            "status": "BOUND_FROZEN_SAME_PHI",
            "native_schema": "compatibility_module/1",
            "semantic_role": (
                "principal materialized-depth compatibility condition for "
                "the exact three-block fiber module"),
            "custody": (
                "fiber semantics are consumed from the digest-bound native "
                "exact-module checker; GP independently rederives the Cramer "
                "pushforward and both ring-class observations"),
        },
        "refusals": [
            "K-rationality of the degree-14 witness",
            "nonzerodivisor or componentwise genericity",
            "all-orders lifting or source sufficiency",
            "H8, H3, or (75,125) promotion",
            "wall survival or wall emptiness",
            "graph claim or transport authority",
        ],
        "graph_effect": "NONE",
    }


def _capture_native(native_root):
    root = Path(native_root)
    script = root / "f2_h3_b0_uniform_lambda.py"
    old_argv, old_path = sys.argv[:], sys.path[:]
    captured = {}
    try:
        sys.argv = [str(script), "--quiet"]
        sys.path.insert(0, str(root))
        spec = importlib.util.spec_from_file_location("gp_b0_fixture_native", script)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)

        def profile(frame, event, _argument):
            if frame.f_code is module.main.__code__ and event == "return":
                captured.update(frame.f_locals)

        sys.setprofile(profile)
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                returncode = module.main()
        finally:
            sys.setprofile(None)
        require(returncode == 0, "N1", "native fixture producer failed")
        return module, captured
    finally:
        sys.argv = old_argv
        sys.path[:] = old_path


def build_fixture(native_root=NATIVE_ROOT):
    root = Path(native_root)
    bindings = {name: normalized_sha256(root / name)
                for name in sorted(NATIVE_BINDINGS)}
    require(bindings == dict(sorted(NATIVE_BINDINGS.items())), "B1",
            "native compatibility input drifted before freeze")
    module, value = _capture_native(root)
    certificate = json.loads((root / "f2_h3_b0_uniform_lambda.json").read_text(
        encoding="utf-8"))
    module_certificate = json.loads((
        root / "f2_h3_b0_compatibility_module.json").read_text(
            encoding="utf-8"))
    matrix = [[_encode_poly(entry, BASE_VARS) for entry in row]
              for row in value["MX"]]
    rhs = [_encode_poly(entry, BASE_VARS) for entry in value["RHS"]]
    parts = [{
        "fiber_powers": [[name, exponent] for name, exponent in key],
        "coefficient": _encode_poly(body, BASE_VARS),
    } for key, body in sorted(value["parts"].items())]
    power1_numerator = module.tolist(module.spec(
        value["PHI"], dict(value["FIX"], c7_8=module.Q(1),
                            c8_10=module.Q(1))), "c8_11")
    power1_denominator = module.tolist(value["sD"], "c8_11")
    return {
        "schema": SCHEMA,
        "binding_digest_algo": "sha256-lf-normalized",
        "source_bindings": bindings,
        "native_certificate": certificate,
        "native_module_certificate": module_certificate,
        "projection": _projection(),
        "full_model": {
            "A": _encode_poly(value["AW"], BASE_VARS),
            "OB": _encode_poly(value["OBW"], BASE_VARS),
            "det5": _encode_poly(value["D5"], BASE_VARS),
            "Phi_b0_compat": _encode_poly(value["PHI"], BASE_VARS),
        },
        "pushforward": {
            "chart_matrix": matrix,
            "chart_rhs": rhs,
            "lambda_parts": parts,
            "wrong_scalar": "2/3 leaves c7_5 present",
            "power1_numerator": _encode_univariate(power1_numerator),
            "power1_denominator": _encode_univariate(power1_denominator),
        },
        "slice": {
            "fixed": {name: str(coefficient) for name, coefficient
                      in sorted(value["FIX"].items())},
            "A": _encode_poly(value["sA"], SLICE_VARS),
            "OB": _encode_poly(value["sOB"], SLICE_VARS),
            "Phi_b0_compat": _encode_poly(value["sPHI"], SLICE_VARS),
            "det5": _encode_poly(value["sD"], SLICE_VARS),
            "resultant": _encode_univariate(value["RHO"]),
            "S11": _encode_univariate(value["S11"]),
            "S10": _encode_univariate(value["S10"]),
            "guard_product": _encode_univariate(value["Wg"]),
            "final_modulus": _encode_univariate(value["MOD"]),
        },
        "authority_boundary": (
            "The exact observations license only that Phi_b0_compat is "
            "nonzero and not a unit on the stated localized materialized-"
            "depth coordinate ring. They do not license nonzerodivisor, "
            "component, rational-point, source, H8, H3, verdict, or graph "
            "authority."),
    }


def _validate_native_certificate(certificate):
    require(certificate.get("id") == "f2_h3_b0_uniform_lambda" and
            certificate.get("schema_version") == 1, "N2",
            "native receipt identity or schema changed")
    require(certificate.get("verdict") == "GENERIC_NONZERO_DIVISOR" and
            certificate.get("source_representable") is False and
            certificate.get("faces_cleared") == 0, "N3",
            "native verdict or promotion boundary changed")
    push = certificate.get("pushforward", {})
    require(push.get("formula") == "det5**2 * Lambda|_{det5-solve}" and
            push.get("terms") == 3137 and
            push.get("sha256") ==
            "9673fafbabc3a63c7058eae627d9ebb1f0005edc1ff863a26fdfae8b9b667cf7",
            "N4", "native Phi commitment changed")
    chain = certificate.get("chain", {})
    require(chain.get("rho_degree") == 26 and
            chain.get("r_final_degree") == 14 and
            chain.get("S11_degree") == 12, "N5",
            "native quotient-witness degrees changed")
    require(any("NONZERODIVISOR" in item for item in
                certificate.get("refusals", [])), "N6",
            "native nonzerodivisor refusal disappeared")


def _validate_module_certificate(certificate):
    require(certificate.get("id") == "f2_h3_b0_compatibility_module" and
            certificate.get("schema") == "compatibility_module/1" and
            certificate.get("schema_version") == 1 and
            certificate.get("verdict") == "COMPATIBILITY_PACKET_EXACT", "N9",
            "native compatibility-module identity or schema changed")
    require(certificate.get("source_representable") is False and
            certificate.get("faces_cleared") == 0, "N10",
            "native module promoted source or face authority")
    compatibility = certificate.get("compatibility", {})
    require(compatibility.get("generator") == "Phi" and
            compatibility.get("ideal") == "principal" and
            compatibility.get("phi_terms") == 3137 and
            compatibility.get("phi_sha256") ==
            "9673fafbabc3a63c7058eae627d9ebb1f0005edc1ff863a26fdfae8b9b667cf7"
            and compatibility.get("phi_sha256_matches_uniform_lambda") is True,
            "N11", "native module does not bind the identical Phi class")
    require(certificate.get("syzygy", {}).get("generator") ==
            ["1", "-(3/2)*c2_3*t"] and
            certificate.get("syzygy", {}).get("primitive") is True, "N12",
            "primitive last-block syzygy changed")
    blocks = certificate.get("blocks", [])
    require(len(blocks) == 3 and
            [(block.get("generic_rank"), block.get("localized_rank"))
             for block in blocks] == [(5, 5), (1, 1), (1, 1)] and
            certificate.get("rank_strata", {}).get("nonempty_strata") == 0,
            "N13", "localized block ranks or rank strata changed")
    fiber = certificate.get("fiber_semantics", {})
    require(fiber.get("Phi_nonzero") ==
            "fiber EMPTY (augmented rank 2 > 1)" and
            fiber.get("Phi_zero") ==
            "one reduced point in (u1, u2, s) times a free affine 2-plane in (c7_4, c8_5)",
            "N14", "materialized fiber semantics changed")
    require(certificate.get("bindings", {}).get(
        "f2_h3_b0_uniform_lambda.json") ==
        NATIVE_BINDINGS["f2_h3_b0_uniform_lambda.json"] and
        any("nonzerodivisor" in item.lower() for item in
            certificate.get("refusals", [])), "N15",
            "module custody or nonzerodivisor refusal changed")


def _clear_y(value, denominator, numerator):
    degree = _pdegree(value, "c8_10")
    result = _pzero(value.variables)
    for exponent in range(degree + 1):
        coefficient = _pcoeff(value, "c8_10", exponent)
        term = _pmul(coefficient, _ppow(numerator, exponent))
        term = _pmul(term, _ppow(denominator, degree - exponent))
        result = _padd(result, term)
    return result


def _sylvester(At, Pt, k, extra):
    m, n = 2, 4
    f = [_pcoeff(At, "c7_8", index) for index in range(m + 1)]
    g = [_pcoeff(Pt, "c7_8", index) for index in range(n + 1)]
    zero = _pzero(At.variables)
    rows = []
    for i in range(n - k):
        rows.append([f[m - (j - i)] if 0 <= j - i <= m else zero
                     for j in range(m + n - k)])
    for i in range(m - k):
        rows.append([g[n - (j - i)] if 0 <= j - i <= n else zero
                     for j in range(m + n - k)])
    columns = list(range(m + n - 2 * k - 1)) + [extra]
    return _pdet([[row[column] for column in columns] for row in rows])


def validate_fixture_value(fixture):
    require(set(fixture) == {
        "schema", "binding_digest_algo", "source_bindings",
        "native_certificate", "native_module_certificate", "projection",
        "full_model", "pushforward", "slice", "authority_boundary"}, "F1",
        "fixture shape changed")
    require(fixture["schema"] == SCHEMA and
            fixture["binding_digest_algo"] == "sha256-lf-normalized", "F2",
            "fixture schema or binding algorithm changed")
    require(fixture["source_bindings"] == dict(sorted(NATIVE_BINDINGS.items())),
            "F3", "frozen native binding changed")
    _validate_native_certificate(fixture["native_certificate"])
    _validate_module_certificate(fixture["native_module_certificate"])
    require(fixture["projection"] == _projection(), "M1",
            "scope, class, clearing exponent, rendezvous, or refusal changed")
    require("nonzero and not a unit" in fixture["authority_boundary"] and
            "do not license nonzerodivisor" in fixture["authority_boundary"],
            "M2", "authority boundary widened")

    full = {name: _decode_poly(value, "full " + name)
            for name, value in fixture["full_model"].items()}
    require(all(value.variables == BASE_VARS for value in full.values()) and
            len(full["Phi_b0_compat"].terms) == 3137 and
            len(full["OB"].terms) == 39 and len(full["det5"].terms) == 6,
            "A1", "full model polynomial size changed")

    push = fixture["pushforward"]
    matrix = [[_decode_poly(entry, "chart matrix") for entry in row]
              for row in push["chart_matrix"]]
    rhs = [_decode_poly(entry, "chart rhs") for entry in push["chart_rhs"]]
    require(len(matrix) == 5 and all(len(row) == 5 for row in matrix) and
            len(rhs) == 5, "A2", "five-row chart shape changed")
    require(_pdet(matrix) == full["det5"], "A3",
            "wall-wide chart determinant is not det5")
    numerators = []
    for column in range(5):
        numerators.append(_pdet([[
            rhs[row] if other == column else matrix[row][other]
            for other in range(5)] for row in range(5)]))

    parts = {}
    for record in push["lambda_parts"]:
        key = tuple((name, exponent) for name, exponent
                    in record["fiber_powers"])
        require(key not in parts and set(name for name, _ in key) <=
                set(FIBER_COLS), "A4", "Lambda part key changed")
        parts[key] = _decode_poly(record["coefficient"], "Lambda part")
    expected_profile = {
        (): 417, (("c7_6", 1),): 3, (("c7_7", 1),): 12,
        (("c8_7", 1),): 3, (("c8_8", 1),): 11,
        (("c8_9", 1),): 29, (("c8_9", 2),): 1,
    }
    require({key: len(value.terms) for key, value in parts.items()} ==
            expected_profile, "A5", "Lambda fiber profile changed")
    reconstructed = _pmul(_pmul(full["det5"], full["det5"]), parts[()])
    for column, numerator in zip(FIBER_COLS, numerators):
        coefficient = parts.get(((column, 1),))
        if coefficient is not None:
            reconstructed = _padd(reconstructed, _pmul(
                _pmul(full["det5"], coefficient), numerator))
    reconstructed = _padd(reconstructed, _pmul(
        parts[(("c8_9", 2),)], _pmul(numerators[0], numerators[0])))
    require(reconstructed == full["Phi_b0_compat"], "A6",
            "Cramer pushforward does not reproduce Phi_b0_compat")
    power1_numerator = _decode_univariate(
        push["power1_numerator"], "power-one numerator")
    power1_denominator = _decode_univariate(
        push["power1_denominator"], "power-one denominator")
    require(_udivmod(power1_numerator, power1_denominator)[1] != [K_ZERO],
            "A7", "one det5 power unexpectedly clears the denominator")
    require(push["wrong_scalar"] == "2/3 leaves c7_5 present", "A8",
            "wrong-eliminant-scalar refusal changed")

    slice_value = fixture["slice"]
    fixed = {name: _k(Fraction(value))
             for name, value in slice_value["fixed"].items()}
    require(fixed == {"c2_1": _k(0), "c2_2": _k(0), "c2_3": _k(1),
                      "c3_5": _k(1), "c7_10": _k(0), "c7_9": _k(0),
                      "p": _k(1)}, "S1", "slice definition changed")
    sliced = {name: _decode_poly(slice_value[name], "slice " + name)
              for name in ("A", "OB", "Phi_b0_compat", "det5")}
    for name in sliced:
        require(_pspecialize(full[name], SLICE_VARS, fixed) == sliced[name],
                "S2", name + " slice no longer binds the full model")
    ob = sliced["OB"]
    require(_pdegree(ob, "c8_10") == 1, "S3", "OB is not affine in Y")
    denominator = _pcoeff(ob, "c8_10", 1)
    numerator = _pneg(_pcoeff(ob, "c8_10", 0))
    At = _clear_y(sliced["A"], denominator, numerator)
    Pt = _clear_y(sliced["Phi_b0_compat"], denominator, numerator)
    require(_pdegree(At, "c7_8") == 2 and
            _pdegree(Pt, "c7_8") == 4, "S4",
            "cleared slice degrees changed")

    resultant = _decode_univariate(slice_value["resultant"], "resultant")
    S11 = _decode_univariate(slice_value["S11"], "S11")
    S10 = _decode_univariate(slice_value["S10"], "S10")
    computed_resultant = _to_univariate(_sylvester(At, Pt, 0, 5), "c8_11")
    computed_S11 = _to_univariate(_sylvester(At, Pt, 1, 3), "c8_11")
    computed_S10 = _to_univariate(_sylvester(At, Pt, 1, 4), "c8_11")
    require(resultant == computed_resultant and S11 == computed_S11 and
            S10 == computed_S10, "S5", "subresultant chain changed")
    require(len(resultant) - 1 == 26 and len(S11) - 1 == 12, "S6",
            "subresultant degrees changed")

    leading_A = _to_univariate(_pcoeff(At, "c7_8", 2), "c8_11")
    den_z = _to_univariate(denominator, "c8_11")
    det_z = _to_univariate(sliced["det5"], "c8_11")
    guard_product = _umul(_umul(leading_A, den_z), det_z)
    require(guard_product == _decode_univariate(
        slice_value["guard_product"], "guard product"), "S7",
        "guard product changed")
    stripped = list(resultant)
    for guard in (guard_product, S11):
        while True:
            common = _ugcd(stripped, guard)
            if len(common) == 1:
                break
            stripped = _udivmod(stripped, common)[0]
    modulus = _decode_univariate(slice_value["final_modulus"], "final modulus")
    require(_umonic(stripped) == _umonic(modulus) and len(modulus) - 1 == 14,
            "S8", "degree-14 witness modulus changed")
    require(len(_ugcd(modulus, guard_product)) == 1 and
            len(_ugcd(modulus, S11)) == 1, "S9",
            "witness lies on a guard or subresultant degeneration")

    # Nonzero observation: at Z=0, Phi is a unit in K[X]/(At).
    At0 = _to_univariate(_pspecialize(At, ("c7_8",),
                                      {"c8_10": K_ZERO, "c8_11": K_ZERO}),
                         "c7_8")
    Pt0 = _to_univariate(_pspecialize(Pt, ("c7_8",),
                                      {"c8_10": K_ZERO, "c8_11": K_ZERO}),
                         "c7_8")
    det0 = _to_univariate(_pspecialize(sliced["det5"], ("c7_8",),
                                       {"c8_10": K_ZERO,
                                        "c8_11": K_ZERO}), "c7_8")
    require(len(At0) - 1 == 2 and len(_ugcd(At0, Pt0)) == 1 and
            len(_ugcd(At0, det0)) == 1, "W1",
            "nonzero quadratic observation or its chart guard failed")
    X0, Z0 = [K_ZERO, K_ONE], [K_ZERO]
    den0_bar = _eval_in_quotient(denominator, {"c7_8": X0,
        "c8_10": [K_ZERO], "c8_11": Z0}, At0)
    num0_bar = _eval_in_quotient(numerator, {"c7_8": X0,
        "c8_10": [K_ZERO], "c8_11": Z0}, At0)
    Y0 = _rmul(num0_bar, _rinv(den0_bar, At0), At0)
    assignment0 = {"c7_8": X0, "c8_10": Y0, "c8_11": Z0}
    require(_eval_in_quotient(sliced["A"], assignment0, At0) == [K_ZERO]
            and _eval_in_quotient(sliced["OB"], assignment0, At0) ==
            [K_ZERO], "W1", "quadratic observation is not a point of X_b")
    phi0_bar = _eval_in_quotient(
        sliced["Phi_b0_compat"], assignment0, At0)
    _rinv(phi0_bar, At0)
    _rinv(_eval_in_quotient(sliced["det5"], assignment0, At0), At0)

    # Zero observation in R=K[Z]/(r_final).
    Zbar = [K_ZERO, K_ONE]
    Xbar = _rmul([_kneg(item) for item in S10], _rinv(S11, modulus), modulus)
    den_bar = _eval_in_quotient(denominator, {"c7_8": Xbar,
        "c8_10": [K_ZERO], "c8_11": Zbar}, modulus)
    num_bar = _eval_in_quotient(numerator, {"c7_8": Xbar,
        "c8_10": [K_ZERO], "c8_11": Zbar}, modulus)
    Ybar = _rmul(num_bar, _rinv(den_bar, modulus), modulus)
    assignment = {"c7_8": Xbar, "c8_10": Ybar, "c8_11": Zbar}
    require(_eval_in_quotient(sliced["A"], assignment, modulus) == [K_ZERO]
            and _eval_in_quotient(sliced["OB"], assignment, modulus) ==
            [K_ZERO] and _eval_in_quotient(
                sliced["Phi_b0_compat"], assignment, modulus) == [K_ZERO],
            "W2", "degree-14 point does not annihilate A, OB, and Phi")
    det_bar = _eval_in_quotient(sliced["det5"], assignment, modulus)
    _rinv(det_bar, modulus)
    _rinv(den_bar, modulus)
    _rinv(S11, modulus)

    return {
        "phi_terms": 3137,
        "chart_determinant": "VERIFIED_DET5",
        "clearing_exponent": 2,
        "power_one_refuted": True,
        "resultant_degree": 26,
        "nonzero_observation_dimension": 2,
        "zero_observation_dimension": 14,
        "zero_witness_guards": ["c2_3", "p", "det5", "OB-pivot", "S11"],
        "module_rendezvous": "BOUND_FROZEN_SAME_PHI",
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
        "verdict": "VERIFIED_NEITHER_ZERO_NOR_UNIT",
        "checked": checked,
        "source_bindings": fixture["source_bindings"],
        "evidence_envelope": {
            "schema": SCHEMA,
            "checked_proposition": (
                "Phi_b0_compat is nonzero and not a unit in the exact "
                "localized materialized-depth coordinate ring"),
            "licenses": [
                "Phi_b0_compat_nonzero",
                "Phi_b0_compat_not_a_unit",
                "Z(Phi_b0_compat)_meets_X_b_over_an_algebraic_extension",
            ],
            "consumed_frozen_semantics": [
                "Phi_b0_compat_generates_the_principal_materialized_compatibility_ideal",
                "Phi_nonzero_implies_materialized_fiber_empty",
                "Phi_zero_implies_one_reduced_constrained_point_times_free_A2",
            ],
            "outstanding_premises": [
                "P1..P5", "S2", "15*t^3+1=0",
                "native depth-6/7 bodies and det5 chart binding",
                fixture["projection"]["first_open_obligation"],
            ],
            "lean_theorems": [
                "GrandPortage.nonzero_of_observed_nonzero",
                "GrandPortage.notUnit_of_observed_zero",
                "GrandPortage.neitherZeroNorUnit_of_observations",
            ],
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
                "F4", "frozen compatibility fixture digest changed")
    fixture = json.loads(raw.decode("utf-8"))
    checked = validate_fixture_value(fixture)
    if check_bindings:
        check_native_bindings(fixture, native_root)
    return report_from_checked_fixture(fixture, checked)


def native_replay(native_root=NATIVE_ROOT):
    script = Path(native_root) / "f2_h3_b0_uniform_lambda.py"
    completed = subprocess.run(
        [sys.executable, str(script), "--quiet"], cwd=str(native_root),
        capture_output=True, text=True, timeout=180, check=False)
    require(completed.returncode == 0, "N7",
            "native compatibility replay failed: " + completed.stderr.strip())
    require("23/23 checks passed" in completed.stdout and
            "VERDICT: GENERIC_NONZERO_DIVISOR" in completed.stdout, "N8",
            "native replay summary changed")
    return {"verdict": "VERIFIED_NATIVE_23_OF_23", "graph_effect": "NONE"}


def _atomic_write(path, value, force=False):
    path = Path(path)
    if path.exists() and not force:
        raise CompatibilityEvidenceError(
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
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        print(json.dumps({"schema": SCHEMA, "verdict": "REFUSED",
                          "error": str(exc)}, indent=2, sort_keys=True),
              file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
