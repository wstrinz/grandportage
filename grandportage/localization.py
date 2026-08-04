"""Exact certificates for identities in a principal-open localization.

This module does not change RESTRICTION transport.  It checks the separate
coordinate-algebra proposition that a rational expression is zero after a
declared finite set of polynomials has been inverted.
"""

import hashlib
import json

from . import groebner as G


SCHEMA = "localization_membership_v1"
VERIFIED = "VERIFIED_LOCALIZATION_MEMBERSHIP"
MAX_GUARDS = 16
MAX_POWER = 64


class LocalizationError(ValueError):
    """A localization certificate is malformed or mathematically false."""


def _require(condition, message):
    if not condition:
        raise LocalizationError(message)


def _closed(value, fields, where):
    _require(isinstance(value, dict), "%s must be an object" % where)
    extra = set(value) - set(fields)
    missing = set(fields) - set(value)
    _require(not extra, "%s has unknown field(s): %s" % (
        where, ", ".join(sorted(extra))))
    _require(not missing, "%s is missing field(s): %s" % (
        where, ", ".join(sorted(missing))))


def _canonical(expression, variables, characteristic, where):
    try:
        return G.canonical_polynomial_value(expression, variables, characteristic)
    except G.CertificateError as exc:
        raise LocalizationError("%s: %s" % (where, exc))


def _powers(values, count, where):
    _require(isinstance(values, list) and len(values) == count,
             "%s must give one power per guard" % where)
    _require(all(type(value) is int and 0 <= value <= MAX_POWER
                 for value in values),
             "%s powers must be integers from 0 through %d"
             % (where, MAX_POWER))
    return list(values)


def _multiply(expression, guards, powers, variables, characteristic):
    answer = expression
    for guard, power in zip(guards, powers):
        answer = G.multiply_polynomial_power(
            answer, guard, power, variables, characteristic
        )
    return answer


def verify(spec):
    """Check one closed ``localization_membership_v1`` certificate.

    The expression denotes ``numerator / product(guard_i^denominator_i)``.
    It is zero in the localization when some further guard monomial times its
    numerator lies in the recorded ideal.  The cofactor identity checks that
    fact by exact expansion; no CAS process or sampled evaluation is trusted.
    """
    _closed(spec, {
        "schema", "characteristic", "ring_vars", "generators", "guards",
        "expression", "certificate",
    }, "localization specification")
    _require(spec.get("schema") == SCHEMA,
             "schema must be %s" % SCHEMA)
    characteristic = spec.get("characteristic")
    _require(G._valid_characteristic(characteristic),
             "characteristic must be 0 or a prime")
    variables = spec.get("ring_vars")
    _require(isinstance(variables, list)
             and all(isinstance(value, str)
                     and G._IDENTIFIER.fullmatch(value)
                     for value in variables)
             and len(variables) == len(set(variables)),
             "ring_vars must be unique ASCII CAS identifiers")
    generators = spec.get("generators")
    _require(isinstance(generators, list), "generators must be a list")
    generators = [
        _canonical(value, variables, characteristic, "generator %d" % n)
        for n, value in enumerate(generators, 1)
    ]
    guards = spec.get("guards")
    _require(isinstance(guards, list) and 0 < len(guards) <= MAX_GUARDS,
             "guards must contain 1 through %d polynomials" % MAX_GUARDS)
    guards = [
        _canonical(value, variables, characteristic, "guard %d" % n)
        for n, value in enumerate(guards, 1)
    ]
    _require(all(not G.parse_polynomial(
        value, variables, characteristic
    ).is_zero for value in guards),
             "a zero polynomial cannot be inverted")
    guard_keys = [
        json.dumps(value, sort_keys=True, separators=(",", ":"))
        if isinstance(value, dict) else value for value in guards
    ]
    _require(len(guard_keys) == len(set(guard_keys)),
             "guards must remain distinct after exact normalization")

    expression = spec.get("expression")
    _closed(expression, {"numerator", "denominator_powers"}, "expression")
    numerator = _canonical(
        expression.get("numerator"), variables, characteristic,
        "expression numerator",
    )
    denominator_powers = _powers(
        expression.get("denominator_powers"), len(guards),
        "denominator_powers",
    )

    certificate = spec.get("certificate")
    _closed(certificate, {
        "localization_powers", "membership_target", "cofactors",
    }, "certificate")
    localization_powers = _powers(
        certificate.get("localization_powers"), len(guards),
        "localization_powers",
    )
    expected_target = _multiply(
        numerator, guards, localization_powers, variables, characteristic,
    )
    recorded_target = _canonical(
        certificate.get("membership_target"), variables, characteristic,
        "membership_target",
    )
    _require(G.parse_polynomial(
        recorded_target, variables, characteristic
    ) == G.parse_polynomial(
        expected_target, variables, characteristic
    ),
             "membership_target is not numerator times the declared guard "
             "powers: expected %s" % expected_target)
    cofactors = certificate.get("cofactors")
    try:
        checked = G.check_membership_identity(
            expected_target, generators, cofactors, variables, characteristic,
        )
    except G.CertificateError as exc:
        raise LocalizationError(str(exc))

    normalized = {
        "schema": SCHEMA,
        "characteristic": characteristic,
        "ring_vars": list(variables),
        "generators": generators,
        "guards": guards,
        "expression": {
            "numerator": numerator,
            "denominator_powers": denominator_powers,
        },
        "certificate": {
            "localization_powers": localization_powers,
            "membership_target": expected_target,
            "cofactors": list(cofactors),
        },
    }
    return {
        "schema": SCHEMA,
        "verdict": VERIFIED,
        "licenses": ["identity_in_declared_localization_only"],
        "normalized": normalized,
        "checked": checked,
        "spec_fingerprint": hashlib.sha256(json.dumps(
            spec, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
        ).encode("utf-8")).hexdigest(),
    }
