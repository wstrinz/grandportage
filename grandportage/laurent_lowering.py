"""Closed translation validator for finite Laurent straight-line programs.

This checker owns only exact Laurent arithmetic.  It does not derive a source
template, prove a chart change, integrate a series, or license transport.  A
producer supplies finite Laurent inputs over an exact polynomial coefficient
ring; the checker independently evaluates bounded add/multiply/scale/formal
derivative nodes and verifies the declared equalities.
"""

import hashlib
import json

from . import groebner as G


SCHEMA = "laurent_lowering_v1"
VERIFIED = "VERIFIED_LAURENT_LOWERING"
_MAX_INPUTS = 64
_MAX_NODES = 256
_MAX_LAURENT_TERMS = 4096
_MAX_ABS_EXPONENT = 100000


class LaurentLoweringError(ValueError):
    """A Laurent program is malformed or a declared equality is false."""


def _require(condition, message):
    if not condition:
        raise LaurentLoweringError(message)


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


def _canonical_payload(value):
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    )


def _parse_polynomial(expression, variables, characteristic, budget, where):
    try:
        return G.parse_polynomial(
            expression, variables, characteristic, _budget=budget
        )
    except G.CertificateError as exc:
        raise LaurentLoweringError("%s: %s" % (where, exc))


def _parse_exponent(key, where):
    _require(isinstance(key, str), "%s exponent keys must be strings" % where)
    try:
        exponent = int(key)
    except ValueError:
        raise LaurentLoweringError(
            "%s exponent keys must be canonical integers" % where
        )
    _require(str(exponent) == key,
             "%s exponent keys must be canonical integers" % where)
    _require(abs(exponent) <= _MAX_ABS_EXPONENT,
             "%s exponent exceeds the checker limit" % where)
    return exponent


def _normalize(terms):
    return dict((exponent, coefficient)
                for exponent, coefficient in terms.items()
                if not coefficient.is_zero)


def _check_size(terms, where):
    _require(len(terms) <= _MAX_LAURENT_TERMS,
             "%s exceeds the %d-term Laurent limit"
             % (where, _MAX_LAURENT_TERMS))
    _require(all(abs(exponent) <= _MAX_ABS_EXPONENT for exponent in terms),
             "%s exponent exceeds the checker limit" % where)
    return terms


def _add(left, right):
    terms = dict(left)
    for exponent, coefficient in right.items():
        if exponent in terms:
            terms[exponent] = terms[exponent] + coefficient
        else:
            terms[exponent] = coefficient
    return _normalize(terms)


def _multiply(left, right):
    _require(len(left) * len(right) <= _MAX_LAURENT_TERMS * 16,
             "Laurent multiplication exceeds the operation budget")
    terms = {}
    for left_exponent, left_coefficient in left.items():
        for right_exponent, right_coefficient in right.items():
            exponent = left_exponent + right_exponent
            _require(abs(exponent) <= _MAX_ABS_EXPONENT,
                     "Laurent multiplication exponent exceeds checker limit")
            product = left_coefficient * right_coefficient
            terms[exponent] = (
                terms[exponent] + product if exponent in terms else product
            )
    return _check_size(_normalize(terms), "Laurent multiplication")


def _scale(value, scalar):
    return _normalize(dict(
        (exponent, coefficient * scalar)
        for exponent, coefficient in value.items()
    ))


def _derivative(value, variables, characteristic, budget):
    terms = {}
    for exponent, coefficient in value.items():
        if exponent == 0:
            continue
        scalar = G.Polynomial.scalar(
            variables, characteristic, exponent, budget
        )
        terms[exponent - 1] = coefficient * scalar
    return _normalize(terms)


def _render(value):
    return dict(
        (str(exponent), G.render_polynomial(value[exponent]))
        for exponent in sorted(value)
    )


def _export_polynomial(value, shift, variables, series_variable,
                       characteristic, budget, where):
    _require(type(shift) is int and 0 <= shift <= _MAX_ABS_EXPONENT,
             "%s shift must be a nonnegative bounded integer" % where)
    polynomial_variables = variables + [series_variable]
    terms = {}
    support = []
    for exponent, coefficient in value.items():
        polynomial_exponent = exponent + shift
        _require(0 <= polynomial_exponent <= G._MAX_EXPONENT,
                 "%s does not clear every negative Laurent exponent" % where)
        support.append(polynomial_exponent)
        for monomial, scalar in coefficient.terms.items():
            terms[tuple(monomial) + (polynomial_exponent,)] = scalar
    polynomial = G.Polynomial(
        polynomial_variables, characteristic, terms, budget
    )
    return {
        "shift": shift,
        "support": sorted(support),
        "degree": max(support, default=0),
        "polynomial": G.encode_sparse_polynomial(polynomial),
    }


def verify(spec):
    """Evaluate and check one closed ``laurent_lowering_v1`` program."""
    _closed(spec, {
        "schema", "characteristic", "series_variable",
        "coefficient_variables", "inputs", "program", "equalities", "exports",
    }, "Laurent-lowering specification")
    _require(spec.get("schema") == SCHEMA,
             "schema must be %s" % SCHEMA)
    characteristic = spec.get("characteristic")
    _require(G._valid_characteristic(characteristic),
             "characteristic must be 0 or a prime")
    series_variable = spec.get("series_variable")
    _require(isinstance(series_variable, str)
             and G._IDENTIFIER.fullmatch(series_variable),
             "series_variable must be an ASCII CAS identifier")
    variables = _identifiers(
        spec.get("coefficient_variables"), "coefficient_variables"
    )
    _require(series_variable not in variables,
             "series_variable must not be a coefficient variable")
    _require(len(variables) + 1 <= G._MAX_VARIABLES,
             "Laurent coefficient ring exceeds the variable limit")
    budget = G._ArithmeticBudget()

    raw_inputs = spec.get("inputs")
    _require(isinstance(raw_inputs, dict) and raw_inputs,
             "inputs must be a nonempty object")
    _require(len(raw_inputs) <= _MAX_INPUTS, "too many Laurent inputs")
    _require(all(isinstance(name, str) and G._IDENTIFIER.fullmatch(name)
                 for name in raw_inputs),
             "input names must be ASCII CAS identifiers")
    values = {}
    for name, raw_terms in raw_inputs.items():
        where = "input %s" % name
        _require(isinstance(raw_terms, dict), "%s must be an object" % where)
        _require(len(raw_terms) <= _MAX_LAURENT_TERMS,
                 "%s has too many terms" % where)
        terms = {}
        for key, expression in raw_terms.items():
            exponent = _parse_exponent(key, where)
            coefficient = _parse_polynomial(
                expression, variables, characteristic, budget,
                "%s coefficient y^%d" % (where, exponent),
            )
            if not coefficient.is_zero:
                terms[exponent] = coefficient
        values[name] = terms

    program = spec.get("program")
    _require(isinstance(program, list), "program must be a list")
    _require(len(program) <= _MAX_NODES, "too many Laurent program nodes")
    program_reports = []
    for position, node in enumerate(program):
        where = "program node %d" % position
        _require(isinstance(node, dict), "%s must be an object" % where)
        operation = node.get("op")
        fields = {
            "add": {"id", "op", "left", "right"},
            "multiply": {"id", "op", "left", "right"},
            "scale": {"id", "op", "arg", "scalar"},
            "shift": {"id", "op", "arg", "exponent"},
            "derivative": {"id", "op", "arg"},
        }
        _require(isinstance(operation, str) and operation in fields,
                 "%s has unsupported op" % where)
        _closed(node, fields[operation], where)
        node_id = node.get("id")
        _require(isinstance(node_id, str)
                 and G._IDENTIFIER.fullmatch(node_id),
                 "%s id must be an ASCII CAS identifier" % where)
        _require(node_id not in values, "%s id is duplicated" % where)

        def reference(field):
            name = node.get(field)
            _require(isinstance(name, str) and name in values,
                     "%s %s must reference an earlier value" % (where, field))
            return values[name]

        if operation == "add":
            result = _add(reference("left"), reference("right"))
        elif operation == "multiply":
            result = _multiply(reference("left"), reference("right"))
        elif operation == "scale":
            scalar = _parse_polynomial(
                node.get("scalar"), variables, characteristic, budget,
                "%s scalar" % where,
            )
            result = _scale(reference("arg"), scalar)
        elif operation == "shift":
            exponent = node.get("exponent")
            _require(type(exponent) is int
                     and abs(exponent) <= _MAX_ABS_EXPONENT,
                     "%s exponent must be a bounded integer" % where)
            result = dict(
                (old_exponent + exponent, coefficient)
                for old_exponent, coefficient in reference("arg").items()
            )
        else:
            result = _derivative(
                reference("arg"), variables, characteristic, budget
            )
        values[node_id] = _check_size(result, where)
        program_reports.append({
            "id": node_id,
            "op": operation,
            "support": sorted(result),
            "terms": _render(result),
        })

    equalities = spec.get("equalities")
    _require(isinstance(equalities, list) and equalities,
             "equalities must be a nonempty list")
    _require(len(equalities) <= G._MAX_GENERATORS,
             "too many Laurent equalities")
    equality_reports = []
    seen = set()
    for position, equality in enumerate(equalities):
        where = "equality %d" % position
        _closed(equality, {"id", "left", "right"}, where)
        equality_id = equality.get("id")
        _require(isinstance(equality_id, str) and equality_id.strip(),
                 "%s id must be nonempty" % where)
        _require(equality_id not in seen, "equality ids must be unique")
        seen.add(equality_id)
        left_name = equality.get("left")
        right_name = equality.get("right")
        _require(isinstance(left_name, str) and isinstance(right_name, str)
                 and left_name in values and right_name in values,
                 "%s sides must reference computed values" % where)
        difference = _add(values[left_name], _scale(
            values[right_name],
            G.Polynomial.scalar(variables, characteristic, -1, budget),
        ))
        _require(not difference,
                 "%s is false; left-right is %s"
                 % (where, _render(difference)))
        equality_reports.append({
            "id": equality_id,
            "left": left_name,
            "right": right_name,
        })

    exports = spec.get("exports", [])
    _require(isinstance(exports, list), "exports must be a list")
    _require(len(exports) <= _MAX_NODES, "too many Laurent exports")
    export_reports = []
    export_ids = set()
    for position, export in enumerate(exports):
        where = "export %d" % position
        _closed(export, {"id", "node", "shift"}, where)
        export_id = export.get("id")
        _require(isinstance(export_id, str)
                 and G._IDENTIFIER.fullmatch(export_id),
                 "%s id must be an ASCII CAS identifier" % where)
        _require(export_id not in export_ids, "export ids must be unique")
        export_ids.add(export_id)
        node = export.get("node")
        _require(isinstance(node, str) and node in values,
                 "%s node must reference a computed value" % where)
        report = _export_polynomial(
            values[node], export.get("shift"), variables, series_variable,
            characteristic, budget, where,
        )
        report.update({"id": export_id, "node": node})
        export_reports.append(report)

    licenses = ["declared_finite_laurent_equalities"]
    if export_reports:
        licenses.append("canonical_shifted_polynomial_exports")
    return {
        "schema": SCHEMA,
        "verdict": VERIFIED,
        "licenses": licenses,
        "authority_boundary": (
            "exact Laurent arithmetic only; no source derivation, chart "
            "validity, antiderivative existence, or claim transport"
        ),
        "program": program_reports,
        "equalities": equality_reports,
        "exports": export_reports,
        "spec_fingerprint": hashlib.sha256(
            _canonical_payload(spec).encode("utf-8")
        ).hexdigest(),
    }
