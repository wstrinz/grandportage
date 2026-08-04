"""Bounded translation validation for ordered localized solve chains.

Version 1 checks a literal normal form. Version 2 additionally accepts exact
cofactor receipts proving the affine normal form modulo a small, persistent
list of declared normalization equations. Every step then substitutes the
exact solution into the remaining ordered generator list. The unit may use
only declared localization generators and a nonzero coefficient.

The report is not graph authority.  It validates a native certificate and
records the exact state transition; a later graph-bound result can only earn
point-equivalence after binding the states, localization, and model semantics.
"""

from . import evidence as EV
from . import factor_power as FP
from . import groebner as G


SCHEMA = "localized_triangular_solve_chain_v1"
SCHEMA_V2 = "localized_triangular_solve_chain_v2"
VERIFIED = "VERIFIED_LOCALIZED_TRIANGULAR_SOLVE_CHAIN"
MAX_STEPS = 32
MAX_GENERATORS = 128
POINT_UNIVERSES = {"BASE", "ALGEBRAIC_CLOSURE"}


class TriangularChainError(ValueError):
    """A proposed ordered solve chain is malformed or false."""


def _require(condition, message):
    if not condition:
        raise TriangularChainError(message)


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
        raise TriangularChainError("%s: %s" % (where, exc))


def _fingerprint(payload):
    return EV.fingerprint(payload)


def _state_payload(characteristic, coefficient_domain, point_universe,
                   variables, units, generators,
                   normalization_generators=None):
    payload = EV.AffineContext(
        characteristic=characteristic,
        coefficient_domain=coefficient_domain,
        point_universe=point_universe,
        ring_vars=tuple(variables),
        unit_generators=tuple(units),
        generators=tuple(generators),
    ).as_dict()
    if normalization_generators is not None:
        payload["normalization_generators"] = list(normalization_generators)
    return payload


def state_fingerprint(characteristic, coefficient_domain, point_universe,
                      variables, units, generators,
                      normalization_generators=None):
    """Return the canonical fingerprint used by chain envelopes.

    This public helper is intended for isolated native-to-GP adapters.  It
    parses and renders every generator before hashing, so harmless polynomial
    spelling differences do not manufacture distinct mathematical states.
    """
    budget = G._ArithmeticBudget()
    normalized = [
        G.render_polynomial(_parse(
            value, variables, characteristic, budget,
            "state generator %d" % position,
        ))
        for position, value in enumerate(generators)
    ]
    normalized_context = None
    if normalization_generators is not None:
        normalized_context = [
            G.render_polynomial(_parse(
                value, variables, characteristic, budget,
                "state normalization generator %d" % position,
            ))
            for position, value in enumerate(normalization_generators)
        ]
    return _fingerprint(_state_payload(
        characteristic, coefficient_domain, point_universe,
        variables, units, normalized, normalized_context,
    ))


def _substitute(polynomial, variables, pivot, solution, characteristic,
                budget, where):
    images = dict((name, name) for name in variables)
    images[pivot] = solution
    try:
        raw = G.substitute_polynomial(
            G.render_polynomial(polynomial), variables, images,
            characteristic, _budget=budget,
        )
    except G.CertificateError as exc:
        raise TriangularChainError("%s: %s" % (where, exc))
    return _parse(raw, variables, characteristic, budget, where)


def verify(spec):
    """Check one closed ordered localized triangular solve chain."""
    schema = spec.get("schema") if isinstance(spec, dict) else None
    _require(schema in {SCHEMA, SCHEMA_V2},
             "schema must be %s or %s" % (SCHEMA, SCHEMA_V2))
    fields = {
        "schema", "characteristic", "coefficient_domain",
        "point_universe", "ring_vars", "unit_generators",
        "source_receipt", "initial_generators", "steps",
    }
    if schema == SCHEMA_V2:
        fields.add("normalization_generators")
    _closed(spec, fields, "localized triangular solve chain")
    normalized_modulo_context = schema == SCHEMA_V2

    characteristic = spec.get("characteristic")
    _require(G._valid_characteristic(characteristic),
             "characteristic must be 0 or a prime")
    coefficient_domain = spec.get("coefficient_domain")
    expected_domain = "Q" if characteristic == 0 else "F_%d" % characteristic
    _require(coefficient_domain == expected_domain,
             "coefficient_domain must be %s for characteristic %d"
             % (expected_domain, characteristic))
    point_universe = spec.get("point_universe")
    _require(point_universe in POINT_UNIVERSES,
             "point_universe must be BASE or ALGEBRAIC_CLOSURE")
    source_receipt = spec.get("source_receipt")
    _closed(source_receipt, {"id", "sha256"}, "source_receipt")
    _require(isinstance(source_receipt.get("id"), str)
             and source_receipt["id"].strip(),
             "source_receipt id must be nonempty")
    source_sha256 = source_receipt.get("sha256")
    _require(isinstance(source_sha256, str)
             and len(source_sha256) == 71
             and source_sha256.startswith("sha256:")
             and all(value in "0123456789abcdef"
                     for value in source_sha256[7:]),
             "source_receipt sha256 must be sha256:<64 lowercase hex>")

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

    raw_generators = spec.get("initial_generators")
    _require(isinstance(raw_generators, list)
             and 0 < len(raw_generators) <= MAX_GENERATORS,
             "initial_generators must contain 1 through %d entries"
             % MAX_GENERATORS)
    raw_steps = spec.get("steps")
    _require(isinstance(raw_steps, list)
             and 0 < len(raw_steps) <= MAX_STEPS,
             "steps must contain 1 through %d entries" % MAX_STEPS)

    step_fields = {
        "id", "input_state_fingerprint", "equation_index", "equation",
        "pivot", "coefficient", "solution", "output_generators",
        "output_state_fingerprint",
    }
    if normalized_modulo_context:
        step_fields.add("normalization_cofactors")
    seen_ids = set()
    pivots = []
    for position, step in enumerate(raw_steps):
        where = "step %d" % position
        _closed(step, step_fields, where)
        step_id = step.get("id")
        _require(isinstance(step_id, str) and step_id.strip(),
                 "%s id must be nonempty" % where)
        _require(step_id not in seen_ids, "step ids must be unique")
        seen_ids.add(step_id)
        pivot = step.get("pivot")
        _require(isinstance(pivot, str) and pivot in variables,
                 "%s pivot must be a declared ring variable" % where)
        _require(pivot not in units,
                 "%s pivot may not be a localization generator" % where)
        _require(pivot not in pivots, "pivot variables must be unique")
        pivots.append(pivot)
    pivot_indices = {variables.index(value) for value in pivots}

    budget = G._ArithmeticBudget()
    context = []
    if normalized_modulo_context:
        raw_context = spec.get("normalization_generators")
        _require(isinstance(raw_context, list)
                 and 0 < len(raw_context) <= 16,
                 "normalization_generators must contain 1 through 16 entries")
        context = [
            _parse(value, variables, characteristic, budget,
                   "normalization generator %d" % position)
            for position, value in enumerate(raw_context)
        ]
        _require(all(not value.is_zero for value in context),
                 "normalization generators must be nonzero")
        _require(all(not value.uses_any(pivot_indices) for value in context),
                 "normalization generators may not use chain pivot variables")
    context_rendered = [G.render_polynomial(value) for value in context]
    current = [
        _parse(value, variables, characteristic, budget,
               "initial generator %d" % position)
        for position, value in enumerate(raw_generators)
    ]
    current_rendered = [G.render_polynomial(value) for value in current]
    current_fingerprint = _fingerprint(_state_payload(
        characteristic, coefficient_domain, point_universe,
        variables, units, current_rendered,
        context_rendered if normalized_modulo_context else None,
    ))
    reports = []

    for position, step in enumerate(raw_steps):
        where = "step %d (%s)" % (position, step["id"])
        _require(step.get("input_state_fingerprint") == current_fingerprint,
                 "%s input_state_fingerprint does not match current state"
                 % where)
        equation_index = step.get("equation_index")
        _require(type(equation_index) is int
                 and 0 <= equation_index < len(current),
                 "%s equation_index is outside the current generator list"
                 % where)
        equation = _parse(
            step.get("equation"), variables, characteristic, budget,
            "%s equation" % where,
        )
        _require(equation == current[equation_index],
                 "%s equation is not the selected current generator" % where)

        pivot = step["pivot"]
        coefficient = _parse(
            step.get("coefficient"), variables, characteristic, budget,
            "%s coefficient" % where,
        )
        try:
            FP._unit_monomial(
                coefficient, unit_indices, "%s coefficient" % where
            )
        except FP.FactorPowerError as exc:
            raise TriangularChainError(str(exc))
        solution = _parse(
            step.get("solution"), variables, characteristic, budget,
            "%s solution" % where,
        )
        _require(not solution.uses_any(pivot_indices),
                 "%s solution may not use any chain pivot variable" % where)
        pivot_polynomial = G.Polynomial.variable(
            variables, characteristic, pivot, budget
        )
        expected = coefficient * (pivot_polynomial - solution)
        normalized_expected = expected
        normalized_cofactors = []
        if normalized_modulo_context:
            raw_cofactors = step.get("normalization_cofactors")
            _require(isinstance(raw_cofactors, list)
                     and len(raw_cofactors) == len(context),
                     "%s normalization_cofactors must align exactly with "
                     "normalization_generators" % where)
            normalized_cofactors = [
                _parse(value, variables, characteristic, budget,
                       "%s normalization cofactor %d" % (where, index))
                for index, value in enumerate(raw_cofactors)
            ]
            for context_generator, cofactor in zip(
                    context, normalized_cofactors):
                normalized_expected = (
                    normalized_expected + context_generator * cofactor
                )
        _require(equation == normalized_expected,
                 "%s equation is not coefficient * (pivot - solution)%s: "
                 "expected %s" % (
                     where,
                     " modulo the declared normalization receipt"
                     if normalized_modulo_context else "",
                     G.render_polynomial(normalized_expected),
                 ))

        derived = []
        for generator_position, generator in enumerate(current):
            if generator_position == equation_index:
                continue
            substituted = _substitute(
                generator, variables, pivot, step.get("solution"),
                characteristic, budget,
                "%s output generator %d"
                % (where, generator_position),
            )
            if not substituted.is_zero:
                derived.append(substituted)
        derived_rendered = [G.render_polynomial(value) for value in derived]

        output_generators = step.get("output_generators")
        _require(isinstance(output_generators, list)
                 and len(output_generators) <= MAX_GENERATORS,
                 "%s output_generators must be a bounded list" % where)
        proposed = [
            _parse(value, variables, characteristic, budget,
                   "%s proposed output generator %d" % (where, index))
            for index, value in enumerate(output_generators)
        ]
        proposed_rendered = [G.render_polynomial(value) for value in proposed]
        _require(proposed_rendered == derived_rendered,
                 "%s output_generators are not the exact ordered "
                 "substitution result" % where)

        output_fingerprint = _fingerprint(_state_payload(
            characteristic, coefficient_domain, point_universe,
            variables, units, derived_rendered,
            context_rendered if normalized_modulo_context else None,
        ))
        _require(step.get("output_state_fingerprint") == output_fingerprint,
                 "%s output_state_fingerprint does not match derived state"
                 % where)
        step_report = {
            "id": step["id"],
            "input_state_fingerprint": current_fingerprint,
            "equation_index": equation_index,
            "equation": G.render_polynomial(equation),
            "pivot": pivot,
            "coefficient": G.render_polynomial(coefficient),
            "solution": G.render_polynomial(solution),
            "output_state_fingerprint": output_fingerprint,
            "output_generator_count": len(derived),
        }
        if normalized_modulo_context:
            step_report["normalization_cofactors"] = [
                G.render_polynomial(value) for value in normalized_cofactors
            ]
        reports.append(step_report)
        current = derived
        current_fingerprint = output_fingerprint

    open_obligations = [
        "bind the initial and intermediate states to exact graph models",
        "interpret every declared localization generator as a unit",
    ]
    if normalized_modulo_context:
        open_obligations.append(
            "interpret every normalization generator as zero"
        )
    open_obligations.append(
        "prove the checked substitutions induce forward and reverse point maps"
    )

    return {
        "schema": schema,
        "verdict": VERIFIED,
        "source_receipt": dict(source_receipt),
        "licenses": [
            "exact_ordered_localized_triangular_substitution_chain"
            + ("_modulo_declared_normalization_generators"
               if normalized_modulo_context else ""),
        ],
        "normalization_generators": context_rendered,
        "checked_steps": len(reports),
        "steps": reports,
        "final_generators": [G.render_polynomial(value) for value in current],
        "final_state_fingerprint": current_fingerprint,
        "open_obligations": open_obligations,
        "authority_boundary": (
            "standalone ordered translation validation only; no graph model "
            "equivalence, emptiness, ambient identity, parent coverage, "
            "source-membership, or H3 authority"
        ),
        "spec_fingerprint": _fingerprint(spec),
    }
