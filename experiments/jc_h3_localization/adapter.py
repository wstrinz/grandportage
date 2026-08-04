#!/usr/bin/env python3
"""Translate one serialized JC H3 pivot into narrow GP localization evidence."""

from fractions import Fraction
import copy
import hashlib
import json
from pathlib import Path
import re
import sys

from grandportage import groebner as G
from grandportage import localization as L


SCHEMA = "jc_h3_localization_pivot_v1"
MODEL_DIGEST = re.compile(r"^[0-9a-f]{64}$")
EQUATION_ID = re.compile(r"^[ -~]{1,128}$")
MAX_GENERATORS = 128
MAX_NATIVE_DISPLAY = 4096
EXPECTED_MODEL_DIGESTS = {
    "q": "a17f0a4fa0ab0b10de3c4e84310ad51ed84d95c0becb93e3dce156cf5c513999",
    "p": "479ed41d5caa6531a0feabb1aecacd08a8c517f0771d6048dfe7fd1e6f80626c",
}


class AdapterError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise AdapterError(message)


def closed(value, fields, where):
    require(isinstance(value, dict), "%s must be an object" % where)
    extra = set(value) - set(fields)
    missing = set(fields) - set(value)
    require(not extra, "%s has unknown fields: %s" % (
        where, ", ".join(sorted(extra))))
    require(not missing, "%s is missing fields: %s" % (
        where, ", ".join(sorted(missing))))


def fraction_text(value):
    return (str(value.numerator) if value.denominator == 1 else
            "%d/%d" % (value.numerator, value.denominator))


def scale(expression, scalar, variables, characteristic):
    polynomial = G.parse_polynomial(expression, variables, characteristic)
    factor = G.Polynomial.scalar(
        variables, characteristic, scalar, polynomial._budget
    )
    return G.portable_polynomial(polynomial * factor)


def affine_parts(expression, pivot, variables, characteristic):
    polynomial = G.parse_polynomial(expression, variables, characteristic)
    index = variables.index(pivot)
    coefficient_terms = {}
    constant_terms = {}
    for monomial, value in polynomial.terms.items():
        exponent = monomial[index]
        require(exponent <= 1,
                "pivot %s is nonlinear in the recorded equation" % pivot)
        if exponent == 1:
            stripped = list(monomial)
            stripped[index] = 0
            coefficient_terms[tuple(stripped)] = value
        else:
            constant_terms[monomial] = value
    coefficient = G.Polynomial(
        polynomial.variables, polynomial.characteristic, coefficient_terms,
    )
    constant = G.Polynomial(
        polynomial.variables, polynomial.characteristic, constant_terms,
    )
    require(not coefficient.is_zero,
            "pivot %s has zero coefficient" % pivot)
    return coefficient, constant


def translate(envelope):
    closed(envelope, {
        "schema", "chart", "model_digest", "characteristic", "ring_vars",
        "current_generators", "guards", "equation_id",
        "equation_polynomial", "pivot", "coefficient", "unit_witness",
        "substitution",
    }, "pivot envelope")
    require(envelope["schema"] == SCHEMA,
            "schema must be %s" % SCHEMA)
    require(envelope["chart"] in ("q", "p"), "chart must be q or p")
    require(isinstance(envelope["model_digest"], str)
            and MODEL_DIGEST.fullmatch(envelope["model_digest"]),
            "model_digest must be the frozen 64-hex chart digest")
    require(envelope["model_digest"] == EXPECTED_MODEL_DIGESTS[envelope["chart"]],
            "model_digest does not match the frozen %s chart"
            % envelope["chart"])
    characteristic = envelope["characteristic"]
    require(characteristic == 0,
            "the frozen H3 charts are over Q and require characteristic 0")
    variables = envelope["ring_vars"]
    require(isinstance(variables, list)
            and len(variables) == len(set(variables))
            and all(isinstance(value, str)
                    and G._IDENTIFIER.fullmatch(value) for value in variables),
            "ring_vars must be unique ASCII identifiers")
    pivot = envelope["pivot"]
    require(pivot in variables, "pivot must be a recorded ring variable")
    require(pivot not in envelope["guards"],
            "a declared chart guard cannot also be eliminated as a pivot")
    guards = envelope["guards"]
    expected_guards = ["q", "t"] if envelope["chart"] == "q" else ["p", "t"]
    require(guards == expected_guards,
            "%s chart guards must be exactly %s" % (
                envelope["chart"], expected_guards))
    require(all(guard in variables for guard in guards),
            "every guard must be a ring variable")

    equation = G.parse_polynomial(
        envelope["equation_polynomial"], variables, characteristic,
    )
    require(isinstance(envelope["equation_id"], str)
            and EQUATION_ID.fullmatch(envelope["equation_id"]),
            "equation_id must be 1 through 128 printable ASCII characters")
    require(isinstance(envelope["current_generators"], list)
            and 0 < len(envelope["current_generators"]) <= MAX_GENERATORS,
            "current_generators must contain 1 through %d entries" % MAX_GENERATORS)
    generators = [
        G.parse_polynomial(value, variables, characteristic)
        for value in envelope["current_generators"]
    ]
    matches = [index for index, value in enumerate(generators)
               if value == equation]
    require(len(matches) == 1,
            "the exact pivot equation must occur once in current_generators")
    equation_index = matches[0]
    derived_coefficient, constant = affine_parts(
        equation, pivot, variables, characteristic,
    )
    recorded_coefficient = G.parse_polynomial(
        envelope["coefficient"], variables, characteristic,
    )
    require(recorded_coefficient == derived_coefficient,
            "recorded coefficient %s differs from exact affine coefficient %s"
            % (G.render_polynomial(recorded_coefficient),
               G.render_polynomial(derived_coefficient)))

    witness = envelope["unit_witness"]
    closed(witness, {"coefficient", "powers", "inverse"}, "unit_witness")
    require(isinstance(witness["coefficient"], str),
            "unit coefficient must be a rational string")
    try:
        rational = Fraction(witness["coefficient"])
    except (ValueError, ZeroDivisionError) as exc:
        raise AdapterError("unit coefficient must be rational: %s" % exc)
    require(rational != 0, "unit coefficient must be nonzero")
    powers = witness["powers"]
    require(isinstance(powers, dict) and set(powers) <= set(guards),
            "unit powers may name only declared chart guards")
    require(all(type(value) is int and 0 < value <= L.MAX_POWER
                for value in powers.values()),
            "recorded unit powers must be positive bounded integers")
    power_list = [powers.get(guard, 0) for guard in guards]
    witnessed_coefficient = fraction_text(rational)
    for guard, power in zip(guards, power_list):
        witnessed_coefficient = G.multiply_polynomial_power(
            witnessed_coefficient, guard, power, variables, characteristic,
        )
    require(G.parse_polynomial(
        witnessed_coefficient, variables, characteristic
    ) == derived_coefficient,
            "unit witness denotes %s, not pivot coefficient %s" % (
                witnessed_coefficient, derived_coefficient))
    require(isinstance(witness["inverse"], str)
            and 0 < len(witness["inverse"]) <= MAX_NATIVE_DISPLAY,
            "native inverse display must be a bounded nonempty string")
    require(isinstance(envelope["substitution"], str)
            and envelope["substitution"].strip()
            and len(envelope["substitution"]) <= MAX_NATIVE_DISPLAY,
            "native substitution display must be a nonempty string")

    # If a*x+b=0 and a=c*D for rational c and guard monomial D, then
    # x=(-b/c)/D.  The localized identity has numerator equation/c and
    # denominator D; its ideal-membership cofactor is exactly 1/c.
    inverse_scalar = Fraction(1, 1) / rational
    solution_numerator = scale(
        constant, -inverse_scalar, variables, characteristic,
    )
    identity_numerator = scale(
        equation, inverse_scalar, variables, characteristic,
    )
    cofactors = ["0"] * len(generators)
    cofactors[equation_index] = fraction_text(inverse_scalar)
    spec = {
        "schema": L.SCHEMA,
        "characteristic": characteristic,
        "ring_vars": variables,
        "generators": [
            G.portable_polynomial(value) for value in generators
        ],
        "guards": guards,
        "expression": {
            "numerator": identity_numerator,
            "denominator_powers": power_list,
        },
        "certificate": {
            "localization_powers": [0] * len(guards),
            "membership_target": identity_numerator,
            "cofactors": cofactors,
        },
    }
    report = L.verify(spec)
    source_fingerprint = hashlib.sha256(json.dumps(
        envelope, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
    ).encode("utf-8")).hexdigest()
    return {
        "schema": "jc_h3_gp_localization_replay_v1",
        "chart": envelope["chart"],
        "model_digest": envelope["model_digest"],
        "equation_id": envelope["equation_id"],
        "pivot": pivot,
        "derived_substitution": {
            "numerator": solution_numerator,
            "denominator_powers": power_list,
        },
        "source_fingerprint": source_fingerprint,
        "gp_report": report,
        "authority": "one identity in the declared localization only",
        "whole_elimination_chain_authority": False,
        "ambient_identity_authority": False,
        "source_membership_authority": False,
        "native_inverse_display": witness["inverse"],
        "native_inverse_display_is_not_trusted": True,
        "native_substitution_display": envelope["substitution"],
        "native_substitution_display_is_not_trusted": True,
    }


def self_test(root):
    q_path = root / "q-control.json"
    p_path = root / "p-control.json"
    q = json.loads(q_path.read_text(encoding="utf-8"))
    p = json.loads(p_path.read_text(encoding="utf-8"))
    q_report = translate(q)
    p_report = translate(p)
    assert q_report["derived_substitution"] == {
        "numerator": "(-1/3)*p+(-1/3)*I4",
        "denominator_powers": [2, 1],
    }
    assert p_report["derived_substitution"] == {
        "numerator": "(1/15)*I4",
        "denominator_powers": [1, 3],
    }
    mutations = []
    for label, mutate in (
        ("cross-chart guard", lambda value: value.update({"guards": ["p", "t"]})),
        ("changed equation", lambda value: value.update({"equation_polynomial":
                                                          "3*q*t*x+p+I4"})),
        ("undeclared unit", lambda value: value["unit_witness"]["powers"].update({"p": 1})),
        ("wrong coefficient", lambda value: value.update({"coefficient": "3*q*t"})),
        ("missing generator", lambda value: value.update({"current_generators":
                                                           ["15*t^3+1"]})),
        ("changed model", lambda value: value.update({
            "model_digest": "0" * 64})),
        ("wrong characteristic", lambda value: value.update({
            "characteristic": 5})),
        ("guard pivot", lambda value: value.update({"pivot": "q"})),
        ("duplicate equation", lambda value: value.update({
            "current_generators": ["3*q^2*t*x+p+I4"] * 2})),
    ):
        changed = copy.deepcopy(q)
        mutate(changed)
        try:
            translate(changed)
        except (AdapterError, G.CertificateError, L.LocalizationError):
            mutations.append(label)
    assert len(mutations) == 9, mutations
    return {"controls": 2, "refused_mutations": mutations}


def main(argv):
    root = Path(__file__).resolve().parent
    if argv == ["--self-test"]:
        print(json.dumps(self_test(root), indent=2, sort_keys=True))
        return 0
    if len(argv) != 1:
        sys.stderr.write("usage: adapter.py ENVELOPE.json | --self-test\n")
        return 2
    try:
        envelope = json.loads(Path(argv[0]).read_text(encoding="utf-8"))
        print(json.dumps(translate(envelope), indent=2, sort_keys=True))
    except (OSError, ValueError, G.CertificateError,
            L.LocalizationError, AdapterError) as exc:
        sys.stderr.write("JC H3 LOCALIZATION ADAPTER REFUSED\n  %s\n" % exc)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
