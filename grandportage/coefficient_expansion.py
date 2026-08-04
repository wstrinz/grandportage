"""Small translation validator for polynomial-to-coefficient lowering.

The checker has two deliberately different outcomes.  A selected set of
coefficients is a sound necessary condition for a polynomial identity.  Only
complete coverage through the declared degree licenses the converse.  Neither
outcome says anything about a later elimination or CAS computation.
"""

import hashlib
import json

from . import groebner as G


SCHEMA = "coefficient_expansion_v1"
VERIFIED_COMPLETE = "VERIFIED_COEFFICIENT_EXPANSION"
VERIFIED_SELECTED = "VERIFIED_COEFFICIENT_SELECTION"
COMPLETE = "complete"
SELECTED = "selected"


class CoefficientExpansionError(ValueError):
    """A proposed coefficient lowering is malformed or mathematically false."""


def _require(condition, message):
    if not condition:
        raise CoefficientExpansionError(message)


def _closed(value, fields, where):
    _require(isinstance(value, dict), "%s must be an object" % where)
    extra = set(value) - set(fields)
    _require(not extra, "%s has unknown field(s): %s" % (
        where, ", ".join(sorted(extra))))


def _identifiers(values, where):
    _require(isinstance(values, list), "%s must be a list" % where)
    _require(all(isinstance(value, str) and G._IDENTIFIER.fullmatch(value)
                 for value in values),
             "%s must contain only ASCII CAS identifiers" % where)
    _require(len(values) == len(set(values)),
             "%s must not contain duplicates" % where)
    return list(values)


def _parse(expression, variables, characteristic, where):
    try:
        return G.parse_polynomial(expression, variables, characteristic)
    except G.CertificateError as exc:
        raise CoefficientExpansionError("%s: %s" % (where, exc))


def _coefficient(polynomial, parameter_index, exponent):
    terms = {}
    for monomial, value in polynomial.terms.items():
        if monomial[parameter_index] != exponent:
            continue
        coefficient_monomial = list(monomial)
        coefficient_monomial[parameter_index] = 0
        terms[tuple(coefficient_monomial)] = value
    return G.Polynomial(
        polynomial.variables, polynomial.characteristic, terms
    )


def _canonical_payload(value):
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    )


def verify(spec):
    """Check one closed ``coefficient_expansion_v1`` specification.

    Source variables denote polynomial-valued template inputs.  ``images``
    lowers each one to an exact expression in scalar coefficient variables and
    one distinguished polynomial parameter.  Each equation records either all
    coefficient rows or an explicitly selected subset.
    """
    _closed(spec, {
        "schema", "characteristic", "parameter", "coefficient_variables",
        "source_variables", "images", "bounded_variables", "equations",
    }, "coefficient-expansion specification")
    _require(spec.get("schema") == SCHEMA,
             "schema must be %s" % SCHEMA)
    characteristic = spec.get("characteristic")
    _require(G._valid_characteristic(characteristic),
             "characteristic must be 0 or a prime")
    parameter = spec.get("parameter")
    _require(isinstance(parameter, str) and G._IDENTIFIER.fullmatch(parameter),
             "parameter must be an ASCII CAS identifier")
    coefficient_variables = _identifiers(
        spec.get("coefficient_variables"), "coefficient_variables"
    )
    source_variables = _identifiers(
        spec.get("source_variables"), "source_variables"
    )
    _require(source_variables, "source_variables must not be empty")
    _require(set(source_variables).isdisjoint(coefficient_variables)
             and parameter not in source_variables
             and parameter not in coefficient_variables,
             "source, coefficient, and parameter identifiers must be disjoint")
    variables = source_variables + coefficient_variables + [parameter]
    _require(len(variables) <= G._MAX_VARIABLES,
             "coefficient expansion exceeds the %d-variable checker limit"
             % G._MAX_VARIABLES)
    source_indices = range(len(source_variables))
    parameter_index = len(variables) - 1

    images = spec.get("images")
    _require(isinstance(images, dict) and set(images) == set(source_variables),
             "images must give exactly one image for every source variable")
    parsed_images = {}
    for name in source_variables:
        parsed = _parse(
            images[name], variables, characteristic, "image of %s" % name
        )
        _require(not parsed.uses_any(source_indices),
                 "image of %s may not use a source variable" % name)
        parsed_images[name] = parsed

    bounded = spec.get("bounded_variables")
    _require(isinstance(bounded, dict), "bounded_variables must be an object")
    _require(set(bounded) <= set(source_variables),
             "bounded_variables may name only source variables")
    used_coordinates = []
    for name, declaration in bounded.items():
        _closed(declaration, {"cap", "coefficients"},
                "bounded variable %s" % name)
        cap = declaration.get("cap")
        _require(type(cap) is int and 0 <= cap <= 256,
                 "cap of %s must be an integer from 0 to 256" % name)
        coordinates = _identifiers(
            declaration.get("coefficients"),
            "coefficients of bounded variable %s" % name,
        )
        _require(len(coordinates) == cap + 1,
                 "cap %d for %s requires exactly %d coefficient coordinates"
                 % (cap, name, cap + 1))
        _require(set(coordinates) <= set(coefficient_variables),
                 "coefficient coordinates of %s must belong to the scalar ring"
                 % name)
        used_coordinates.extend(coordinates)
        pieces = []
        for exponent, coordinate in enumerate(coordinates):
            if exponent == 0:
                pieces.append(coordinate)
            elif exponent == 1:
                pieces.append("%s*%s" % (coordinate, parameter))
            else:
                pieces.append("%s*%s^%d" % (
                    coordinate, parameter, exponent
                ))
        expected = _parse(
            "+".join(pieces), variables, characteristic,
            "canonical bounded image of %s" % name,
        )
        _require(parsed_images[name] == expected,
                 "image of %s does not exactly pack its declared 0..%d "
                 "coefficient coordinates" % (name, cap))
    _require(len(used_coordinates) == len(set(used_coordinates)),
             "a coefficient coordinate cannot pack two bounded variables")

    equations = spec.get("equations")
    _require(isinstance(equations, list) and equations,
             "equations must be a nonempty list")
    _require(len(equations) <= G._MAX_GENERATORS,
             "too many coefficient equations")
    identities = {
        name: images[name] for name in source_variables
    }
    identities.update((name, name) for name in coefficient_variables)
    identities[parameter] = parameter
    reports = []
    seen_ids = set()
    all_complete = True
    for position, equation in enumerate(equations):
        where = "equation %d" % position
        _closed(equation, {
            "id", "expression", "degree", "coverage", "coefficients",
        }, where)
        equation_id = equation.get("id")
        _require(isinstance(equation_id, str) and equation_id.strip(),
                 "%s id must be a nonempty string" % where)
        _require(equation_id not in seen_ids,
                 "equation ids must be unique")
        seen_ids.add(equation_id)
        degree = equation.get("degree")
        _require(type(degree) is int and 0 <= degree <= G._MAX_EXPONENT,
                 "%s degree must be a nonnegative bounded integer" % where)
        coverage = equation.get("coverage")
        _require(coverage in {COMPLETE, SELECTED},
                 "%s coverage must be complete or selected" % where)
        rows = equation.get("coefficients")
        _require(isinstance(rows, dict) and rows,
                 "%s coefficients must be a nonempty object" % where)
        row_indices = set()
        for key in rows:
            _require(isinstance(key, str) and key.isdigit()
                     and key == str(int(key)),
                     "%s coefficient keys must be canonical nonnegative "
                     "integers" % where)
            row_indices.add(int(key))
        _require(max(row_indices) <= degree,
                 "%s selects a coefficient above its declared degree" % where)
        if coverage == COMPLETE:
            _require(row_indices == set(range(degree + 1)),
                     "%s complete coverage must contain every coefficient "
                     "from 0 through %d" % (where, degree))
        else:
            all_complete = False

        source_expression = _parse(
            equation.get("expression"), variables, characteristic,
            "%s source expression" % where,
        )
        _require(not source_expression.uses_any(
            range(len(source_variables), len(variables))
        ), "%s source expression may use only source variables and exact "
           "scalar constants" % where)
        try:
            expanded_text = G.substitute_polynomial(
                equation.get("expression"), variables, identities,
                characteristic, _preserve_sparse=True,
            )
        except G.CertificateError as exc:
            raise CoefficientExpansionError("%s lowering failed: %s" % (
                where, exc
            ))
        expanded = _parse(
            expanded_text, variables, characteristic,
            "%s expanded polynomial" % where,
        )
        _require(not expanded.uses_any(source_indices),
                 "%s lowering left a source variable behind" % where)
        overflow = [
            monomial[parameter_index] for monomial in expanded.terms
            if monomial[parameter_index] > degree
        ]
        if overflow:
            raise CoefficientExpansionError(
                "%s omitted overflow coefficient y^%d above declared degree %d"
                % (where, max(overflow), degree)
            )
        checked = {}
        for exponent in sorted(row_indices):
            expected = _parse(
                rows[str(exponent)], variables, characteristic,
                "%s coefficient %d" % (where, exponent),
            )
            _require(not expected.uses_any(source_indices)
                     and not expected.uses_any([parameter_index]),
                     "%s coefficient %d must be a scalar-ring polynomial"
                     % (where, exponent))
            actual = _coefficient(expanded, parameter_index, exponent)
            _require(actual == expected,
                     "%s coefficient %d is wrong: expected %s, computed %s"
                     % (where, exponent, G.render_polynomial(expected),
                        G.render_polynomial(actual)))
            checked[str(exponent)] = G.render_polynomial(actual)
        reports.append({
            "id": equation_id,
            "coverage": coverage,
            "degree": degree,
            "checked_coefficients": checked,
        })

    verdict = VERIFIED_COMPLETE if all_complete else VERIFIED_SELECTED
    licenses = (["polynomial_identity_iff_all_rows_zero"] if all_complete else
                ["polynomial_identity_implies_selected_rows_zero"])
    return {
        "schema": SCHEMA,
        "verdict": verdict,
        "licenses": licenses,
        "coefficient_variables": coefficient_variables,
        "bounded_variables": bounded,
        "equations": reports,
        "spec_fingerprint": hashlib.sha256(
            _canonical_payload(spec).encode("utf-8")
        ).hexdigest(),
    }
