"""Exact translation validation for unit-times-positive-power identities.

The checker proves only ``equation = unit * base^exponent`` and that the
recorded scalar is a monomial in declared unit generators with nonzero exact
coefficient.  Turning equation-vanishing into base-vanishing additionally
requires a domain-valued semantic interpretation; this module does not invent
that premise or mint an emptiness claim.
"""

import hashlib
import json

from . import groebner as G


SCHEMA = "factor_power_v1"
VERIFIED = "VERIFIED_FACTOR_POWER_IDENTITY"
MAX_RECEIPTS = 64
MAX_EXPONENT = 64


class FactorPowerError(ValueError):
    """A factor-power receipt is malformed or mathematically false."""


def _require(condition, message):
    if not condition:
        raise FactorPowerError(message)


def _closed(value, fields, where):
    _require(isinstance(value, dict), "%s must be an object" % where)
    extra = set(value) - set(fields)
    missing = set(fields) - set(value)
    _require(not extra, "%s has unknown field(s): %s" % (
        where, ", ".join(sorted(extra))))
    _require(not missing, "%s is missing field(s): %s" % (
        where, ", ".join(sorted(missing))))


def _parse(value, variables, characteristic, budget, where):
    try:
        return G.parse_polynomial(
            value, variables, characteristic, _budget=budget
        )
    except G.CertificateError as exc:
        raise FactorPowerError("%s: %s" % (where, exc))


def _unit_monomial(polynomial, unit_indices, where):
    _require(len(polynomial.terms) == 1,
             "%s must be one nonzero unit monomial" % where)
    monomial, coefficient = next(iter(polynomial.terms.items()))
    _require(bool(coefficient),
             "%s coefficient must be nonzero" % where)
    _require(all(power == 0 or index in unit_indices
                 for index, power in enumerate(monomial)),
             "%s may use only declared unit generators" % where)
    return monomial, coefficient


def verify(spec):
    """Check one closed ``factor_power_v1`` specification."""
    _closed(spec, {
        "schema", "characteristic", "ring_vars", "unit_generators",
        "receipts",
    }, "factor-power specification")
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
             and len(variables) == len(set(variables))
             and len(variables) <= G._MAX_VARIABLES,
             "ring_vars must be bounded unique ASCII CAS identifiers")
    units = spec.get("unit_generators")
    _require(isinstance(units, list),
             "unit_generators must be a list")
    _require(all(isinstance(value, str) and value in variables
                 for value in units)
             and len(units) == len(set(units)),
             "unit_generators must be distinct ring variables")
    unit_indices = {variables.index(value) for value in units}
    receipts = spec.get("receipts")
    _require(isinstance(receipts, list)
             and 0 < len(receipts) <= MAX_RECEIPTS,
             "receipts must contain 1 through %d entries" % MAX_RECEIPTS)

    budget = G._ArithmeticBudget()
    reports = []
    seen = set()
    for position, receipt in enumerate(receipts):
        where = "receipt %d" % position
        _closed(receipt, {
            "id", "equation", "scalar", "base", "exponent",
        }, where)
        receipt_id = receipt.get("id")
        _require(isinstance(receipt_id, str) and receipt_id.strip(),
                 "%s id must be nonempty" % where)
        _require(receipt_id not in seen, "receipt ids must be unique")
        seen.add(receipt_id)
        exponent = receipt.get("exponent")
        _require(type(exponent) is int and 1 <= exponent <= MAX_EXPONENT,
                 "%s exponent must be an integer from 1 through %d"
                 % (where, MAX_EXPONENT))
        equation = _parse(
            receipt.get("equation"), variables, characteristic, budget,
            "%s equation" % where,
        )
        scalar = _parse(
            receipt.get("scalar"), variables, characteristic, budget,
            "%s scalar" % where,
        )
        base = _parse(
            receipt.get("base"), variables, characteristic, budget,
            "%s base" % where,
        )
        _require(not base.is_zero, "%s base must be nonzero" % where)
        _unit_monomial(scalar, unit_indices, "%s scalar" % where)
        try:
            expected = scalar * (base ** exponent)
        except G.CertificateError as exc:
            raise FactorPowerError("%s: %s" % (where, exc))
        _require(equation == expected,
                 "%s equation is not scalar times base^%d: expected %s"
                 % (where, exponent, G.render_polynomial(expected)))
        reports.append({
            "id": receipt_id,
            "equation": G.render_polynomial(equation),
            "scalar": G.render_polynomial(scalar),
            "base": G.render_polynomial(base),
            "exponent": exponent,
        })

    return {
        "schema": SCHEMA,
        "verdict": VERIFIED,
        "licenses": ["exact_declared_unit_monomial_times_positive_power_identity"],
        "open_obligations": [
            "equation vanishes in the interpreted target",
            "the interpreted target has no zero divisors",
            "the nonzero scalar coefficient and declared unit generators "
            "remain units in that target",
        ],
        "authority_boundary": (
            "factor identity only; no base-vanishing, emptiness, component, "
            "source-membership, or claim-transport authority"
        ),
        "receipts": reports,
        "spec_fingerprint": hashlib.sha256(json.dumps(
            spec, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
        ).encode("utf-8")).hexdigest(),
    }
