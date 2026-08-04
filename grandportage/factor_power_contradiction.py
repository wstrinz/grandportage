"""Compose a factor-power receipt with an affine unit contradiction.

This is still translation validation, not model authority.  The checker proves
that a selected verified factor base is literally ``pivot - solution`` and
that substituting that solution into a second recorded equation yields one
declared unit monomial.  A consumer must separately bind both equations to one
interpreted model and discharge the domain/unit premises.
"""

import hashlib
import json

from . import factor_power as FP
from . import groebner as G


SCHEMA = "factor_power_affine_contradiction_v1"
VERIFIED = "VERIFIED_FACTOR_POWER_AFFINE_CONTRADICTION_PATTERN"


class FactorPowerContradictionError(ValueError):
    """A proposed factor-to-affine contradiction is malformed or false."""


def _require(condition, message):
    if not condition:
        raise FactorPowerContradictionError(message)


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
        raise FactorPowerContradictionError("%s: %s" % (where, exc))


def verify(spec):
    """Check one closed factor-power/affine contradiction pattern."""
    _closed(spec, {
        "schema", "factor_power", "factor_receipt", "pivot",
        "consequence",
    }, "factor-power affine contradiction specification")
    _require(spec.get("schema") == SCHEMA,
             "schema must be %s" % SCHEMA)

    factor_spec = spec.get("factor_power")
    try:
        factor_report = FP.verify(factor_spec)
    except FP.FactorPowerError as exc:
        raise FactorPowerContradictionError(
            "nested factor-power receipt: %s" % exc
        )
    receipt_id = spec.get("factor_receipt")
    _require(isinstance(receipt_id, str),
             "factor_receipt must be a receipt id")
    raw_receipts = {
        receipt["id"]: receipt for receipt in factor_spec["receipts"]
    }
    _require(receipt_id in raw_receipts,
             "factor_receipt must select one nested verified receipt")
    factor_receipt = raw_receipts[receipt_id]

    variables = factor_spec["ring_vars"]
    characteristic = factor_spec["characteristic"]
    unit_indices = {
        variables.index(name) for name in factor_spec["unit_generators"]
    }
    budget = G._ArithmeticBudget()

    pivot = spec.get("pivot")
    _closed(pivot, {"variable", "solution"}, "pivot")
    pivot_name = pivot.get("variable")
    _require(isinstance(pivot_name, str) and pivot_name in variables,
             "pivot variable must be a declared ring variable")
    pivot_index = variables.index(pivot_name)
    solution = _parse(
        pivot.get("solution"), variables, characteristic, budget,
        "pivot solution",
    )
    _require(not solution.uses_any([pivot_index]),
             "pivot solution may not contain the pivot variable")
    base = _parse(
        factor_receipt["base"], variables, characteristic, budget,
        "selected factor base",
    )
    pivot_polynomial = G.Polynomial.variable(
        variables, characteristic, pivot_name, budget
    )
    _require(base == pivot_polynomial - solution,
             "selected factor base must equal pivot - solution exactly")

    consequence = spec.get("consequence")
    _closed(consequence, {"id", "equation", "residual"}, "consequence")
    consequence_id = consequence.get("id")
    _require(isinstance(consequence_id, str) and consequence_id.strip(),
             "consequence id must be nonempty")
    equation = _parse(
        consequence.get("equation"), variables, characteristic, budget,
        "consequence equation",
    )
    residual = _parse(
        consequence.get("residual"), variables, characteristic, budget,
        "consequence residual",
    )
    try:
        FP._unit_monomial(
            residual, unit_indices, "consequence residual"
        )
        images = dict((name, name) for name in variables)
        images[pivot_name] = pivot.get("solution")
        substituted = _parse(
            G.substitute_polynomial(
                consequence.get("equation"), variables, images,
                characteristic, _budget=budget,
            ),
            variables, characteristic, budget,
            "substituted consequence",
        )
    except (FP.FactorPowerError, G.CertificateError) as exc:
        raise FactorPowerContradictionError(str(exc))
    _require(substituted == residual,
             "consequence residual is not the exact pivot substitution: "
             "expected %s" % G.render_polynomial(substituted))

    return {
        "schema": SCHEMA,
        "verdict": VERIFIED,
        "licenses": [
            "exact_factor_to_affine_declared_unit_contradiction_pattern",
        ],
        "factor_receipt": receipt_id,
        "pivot": {
            "variable": pivot_name,
            "solution": G.render_polynomial(solution),
            "base": G.render_polynomial(base),
        },
        "consequence": {
            "id": consequence_id,
            "equation": G.render_polynomial(equation),
            "residual": G.render_polynomial(residual),
        },
        "open_obligations": [
            "the factor and consequence equations vanish in the same "
            "interpreted target",
            "the interpreted target has no zero divisors",
            "the nonzero scalar coefficients and declared unit generators "
            "remain units in that target",
        ],
        "authority_boundary": (
            "exact contradiction pattern only; no model binding, emptiness, "
            "component, source-membership, or claim-transport authority"
        ),
        "factor_report": factor_report,
        "spec_fingerprint": hashlib.sha256(json.dumps(
            spec, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
        ).encode("utf-8")).hexdigest(),
    }
