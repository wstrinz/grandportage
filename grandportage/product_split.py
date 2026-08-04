"""Exact translation validation for binary product-split identities.

The checker proves only ``equation = scalar * left * right`` with a syntactic
declared-unit monomial scalar. Turning equation vanishing into a disjunction
requires a common domain-valued interpretation; constructing exhaustive graph
branches is a further, separate authority step.
"""

import hashlib
import json

from . import factor_power as FP
from . import groebner as G


SCHEMA = "product_split_v1"
VERIFIED = "VERIFIED_BINARY_PRODUCT_SPLIT_IDENTITY"
MAX_RECEIPTS = 64


class ProductSplitError(ValueError):
    """A product-split receipt is malformed or mathematically false."""


def _require(condition, message):
    if not condition:
        raise ProductSplitError(message)


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
        raise ProductSplitError("%s: %s" % (where, exc))


def verify(spec):
    """Check one closed ``product_split_v1`` specification."""
    _closed(spec, {
        "schema", "characteristic", "ring_vars", "unit_generators",
        "receipts",
    }, "product-split specification")
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
    _require(isinstance(units, list)
             and all(isinstance(value, str) and value in variables
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
            "id", "equation", "scalar", "left", "right",
        }, where)
        receipt_id = receipt.get("id")
        _require(isinstance(receipt_id, str) and receipt_id.strip(),
                 "%s id must be nonempty" % where)
        _require(receipt_id not in seen, "receipt ids must be unique")
        seen.add(receipt_id)
        equation = _parse(
            receipt.get("equation"), variables, characteristic, budget,
            "%s equation" % where,
        )
        scalar = _parse(
            receipt.get("scalar"), variables, characteristic, budget,
            "%s scalar" % where,
        )
        left = _parse(
            receipt.get("left"), variables, characteristic, budget,
            "%s left factor" % where,
        )
        right = _parse(
            receipt.get("right"), variables, characteristic, budget,
            "%s right factor" % where,
        )
        _require(not left.is_zero and not right.is_zero,
                 "%s factors must be nonzero" % where)
        _require(left != right, "%s factors must be distinct" % where)
        try:
            FP._unit_monomial(scalar, unit_indices, "%s scalar" % where)
            expected = scalar * left * right
        except (FP.FactorPowerError, G.CertificateError) as exc:
            raise ProductSplitError(str(exc))
        _require(equation == expected,
                 "%s equation is not scalar times left times right: "
                 "expected %s"
                 % (where, G.render_polynomial(expected)))
        reports.append({
            "id": receipt_id,
            "equation": G.render_polynomial(equation),
            "scalar": G.render_polynomial(scalar),
            "left": G.render_polynomial(left),
            "right": G.render_polynomial(right),
        })

    return {
        "schema": SCHEMA,
        "verdict": VERIFIED,
        "licenses": [
            "exact_declared_unit_monomial_times_binary_product_identity",
        ],
        "open_obligations": [
            "the equation vanishes in the interpreted target",
            "the interpreted target has no zero divisors",
            "the nonzero scalar coefficient and declared unit generators "
            "remain units in that target",
        ],
        "authority_boundary": (
            "product identity only; no factor disjunction, branch creation, "
            "coverage, emptiness, component, or claim-transport authority"
        ),
        "receipts": reports,
        "spec_fingerprint": hashlib.sha256(json.dumps(
            spec, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
        ).encode("utf-8")).hexdigest(),
    }
