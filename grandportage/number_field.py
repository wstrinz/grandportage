"""Bounded exact certificates for points valued in a simple number field.

Version 1 deliberately supports only quadratic and cubic extensions of Q.
That is enough for the campaign's Q(i) witness while making the word "field"
checkable: in degrees two and three, absence of a rational root is exactly
irreducibility.  Coordinates are rational functions in one algebraic symbol;
denominators are licensed by inversion modulo the checked minimal polynomial.
"""

from fractions import Fraction
from math import gcd, isqrt
import re

from . import groebner as G


SCHEMA = "simple_number_field_v1"
_IDENTIFIER = re.compile(r"^[A-Za-z][A-Za-z0-9_]*$")
_MAX_DEGREE = 3
_MAX_DIVISOR_SEARCH = 1000000
_MAX_ROOT_CANDIDATES = 4096


class NumberFieldError(ValueError):
    pass


def _trim(poly):
    poly = [Fraction(value) for value in poly]
    while poly and poly[-1] == 0:
        poly.pop()
    return poly


def _add(left, right):
    out = [Fraction(0)] * max(len(left), len(right))
    for index in range(len(out)):
        out[index] = ((left[index] if index < len(left) else 0)
                      + (right[index] if index < len(right) else 0))
    return _trim(out)


def _sub(left, right):
    return _add(left, [-value for value in right])


def _mul(left, right):
    if not left or not right:
        return []
    out = [Fraction(0)] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] += a * b
    return _trim(out)


def _scale(poly, scalar):
    return _trim([Fraction(scalar) * value for value in poly])


def _divmod(left, right):
    left, right = _trim(left), _trim(right)
    if not right:
        raise NumberFieldError("polynomial division by zero")
    quotient = [Fraction(0)] * max(0, len(left) - len(right) + 1)
    while left and len(left) >= len(right):
        shift = len(left) - len(right)
        coefficient = left[-1] / right[-1]
        quotient[shift] += coefficient
        for index, value in enumerate(right):
            left[index + shift] -= coefficient * value
        left = _trim(left)
    return _trim(quotient), left


def _mod(poly, modulus):
    return _divmod(poly, modulus)[1]


def _xgcd(left, right):
    old_r, r = _trim(left), _trim(right)
    old_s, s = [Fraction(1)], []
    old_t, t = [], [Fraction(1)]
    while r:
        quotient, remainder = _divmod(old_r, r)
        old_r, r = r, remainder
        old_s, s = s, _sub(old_s, _mul(quotient, s))
        old_t, t = t, _sub(old_t, _mul(quotient, t))
    if not old_r:
        return [], [], []
    factor = Fraction(1) / old_r[-1]
    return _scale(old_r, factor), _scale(old_s, factor), _scale(old_t, factor)


def _inverse_mod(value, modulus):
    common, coefficient, _other = _xgcd(value, modulus)
    if common != [Fraction(1)]:
        raise NumberFieldError(
            "coordinate denominator is not invertible modulo the minimal "
            "polynomial")
    return _mod(coefficient, modulus)


def _pow_mod(value, exponent, modulus):
    if type(exponent) is not int or exponent < 0 or exponent > 100000:
        raise NumberFieldError("coordinate exponent is outside the exact bound")
    answer = [Fraction(1)]
    base = _mod(value, modulus)
    while exponent:
        if exponent & 1:
            answer = _mod(_mul(answer, base), modulus)
        base = _mod(_mul(base, base), modulus)
        exponent //= 2
    return answer


def _parse_univariate(expression, symbol):
    try:
        parsed = G.parse_polynomial(str(expression), [symbol], 0)
    except (G.CertificateError, TypeError, ValueError) as exc:
        raise NumberFieldError(str(exc))
    degree = max((power[0] for power in parsed.terms), default=-1)
    coefficients = [Fraction(0)] * (degree + 1)
    for power, coefficient in parsed.terms.items():
        coefficients[power[0]] = Fraction(coefficient)
    return _trim(coefficients)


def _lcm(left, right):
    return abs(left * right) // gcd(left, right) if left and right else 0


def _primitive_integer_coefficients(poly):
    denominator = 1
    for value in poly:
        denominator = _lcm(denominator, value.denominator)
    integers = [int(value * denominator) for value in poly]
    content = 0
    for value in integers:
        content = gcd(content, abs(value))
    return [value // (content or 1) for value in integers]


def _divisors(value):
    value = abs(value)
    if value == 0:
        return [0]
    if value > _MAX_DIVISOR_SEARCH:
        raise NumberFieldError(
            "minimal-polynomial rational-root search exceeds the exact bound")
    answer = set()
    for divisor in range(1, isqrt(value) + 1):
        if value % divisor == 0:
            answer.add(divisor)
            answer.add(value // divisor)
    return sorted(answer)


def _evaluate(poly, value):
    answer = Fraction(0)
    for coefficient in reversed(poly):
        answer = answer * value + coefficient
    return answer


def _check_irreducible(poly):
    degree = len(poly) - 1
    if degree not in (2, 3):
        raise NumberFieldError(
            "%s supports only quadratic and cubic extensions" % SCHEMA)
    integers = _primitive_integer_coefficients(poly)
    numerators = _divisors(integers[0])
    denominators = _divisors(integers[-1])
    candidates = set()
    for numerator in numerators:
        for denominator in denominators:
            if denominator:
                candidates.add(Fraction(numerator, denominator))
                candidates.add(Fraction(-numerator, denominator))
            if len(candidates) > _MAX_ROOT_CANDIDATES:
                raise NumberFieldError(
                    "minimal-polynomial rational-root search exceeds the "
                    "candidate bound")
    if any(_evaluate(poly, candidate) == 0 for candidate in candidates):
        raise NumberFieldError(
            "the declared minimal polynomial is reducible over Q")


def _text(value):
    value = Fraction(value)
    return (str(value.numerator) if value.denominator == 1
            else "%s/%s" % (value.numerator, value.denominator))


def _field(spec, model_variables):
    if not isinstance(spec, dict) or set(spec) != {
            "kind", "base", "symbol", "minimal_polynomial"}:
        raise NumberFieldError(
            "witness_field must be a closed simple_number_field_v1 object")
    if spec.get("kind") != SCHEMA or spec.get("base") != "Q":
        raise NumberFieldError(
            "witness_field v1 requires kind simple_number_field_v1 over Q")
    symbol = spec.get("symbol")
    if (not isinstance(symbol, str) or not _IDENTIFIER.match(symbol)
            or symbol in model_variables):
        raise NumberFieldError(
            "the algebraic symbol must be an identifier distinct from model "
            "coordinates")
    modulus = _parse_univariate(spec.get("minimal_polynomial"), symbol)
    if not modulus or modulus[-1] != 1:
        raise NumberFieldError("the minimal polynomial must be monic")
    _check_irreducible(modulus)
    return symbol, modulus


def _coordinate(value, symbol, modulus):
    if isinstance(value, dict):
        if set(value) != {"numerator", "denominator"}:
            raise NumberFieldError(
                "an extension coordinate must contain numerator and denominator")
        numerator = value["numerator"]
        denominator = value["denominator"]
    else:
        numerator, denominator = value, "1"
    top = _parse_univariate(numerator, symbol)
    bottom = _parse_univariate(denominator, symbol)
    if not bottom:
        raise NumberFieldError("coordinate denominator is zero")
    return _mod(_mul(top, _inverse_mod(bottom, modulus)), modulus)


def _evaluate_model_expression(expression, variables, coordinates, modulus):
    try:
        parsed = G.parse_polynomial(expression, variables, 0)
    except (G.CertificateError, TypeError, ValueError) as exc:
        raise NumberFieldError(str(exc))
    answer = []
    for powers, coefficient in parsed.terms.items():
        term = [Fraction(coefficient)]
        for variable, exponent in zip(variables, powers):
            term = _mod(_mul(
                term, _pow_mod(coordinates[variable], exponent, modulus)),
                modulus)
        answer = _add(answer, term)
    return _mod(answer, modulus)


def check_extension_witness(model, witness_field, witness_point):
    """Return ``(is_point, reason, deterministic_receipt)``."""
    if (model.get("characteristic") != 0
            or model.get("coefficient_domain", model.get("field")) != "Q"):
        raise NumberFieldError("extension witnesses v1 require a Q-model")
    if model.get("point_universe") != "ALGEBRAIC_CLOSURE":
        raise NumberFieldError(
            "extension witnesses v1 establish only ALGEBRAIC_CLOSURE points")
    variables = model.get("ring_vars") or []
    if not variables or not isinstance(witness_point, dict):
        raise NumberFieldError("the model and witness need structured coordinates")
    if set(witness_point) != set(variables):
        raise NumberFieldError(
            "witness coordinates must match the model ring variables exactly")
    symbol, modulus = _field(witness_field, variables)
    coordinates = dict((variable, _coordinate(
        witness_point[variable], symbol, modulus)) for variable in variables)
    equations = []
    failed = None
    for expression in model.get("generators") or []:
        value = _evaluate_model_expression(
            expression, variables, coordinates, modulus)
        equations.append({"expression": expression,
                          "value": [_text(item) for item in value]})
        if value and failed is None:
            failed = "equation %s does not vanish" % expression
    guards = []
    for expression in model.get("open_conditions") or []:
        value = _evaluate_model_expression(
            expression, variables, coordinates, modulus)
        guards.append({"expression": expression,
                       "value": [_text(item) for item in value]})
        if not value and failed is None:
            failed = "open guard %s vanishes" % expression
    receipt = {
        "method": SCHEMA,
        "field": {
            "base": "Q", "symbol": symbol,
            "minimal_polynomial": witness_field["minimal_polynomial"],
            "modulus_coefficients": [_text(item) for item in modulus],
            "degree": len(modulus) - 1,
        },
        "coordinates": dict((variable, [_text(item) for item in value])
                            for variable, value in sorted(coordinates.items())),
        "equations": equations,
        "guards": guards,
    }
    return failed is None, failed or "all equations and guards check", receipt
