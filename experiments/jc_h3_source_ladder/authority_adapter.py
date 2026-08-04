"""Compile a checked localized solve chain to an ordinary affine equivalence.

The localization is algebraized by adjoining one inverse coordinate per
declared unit generator. This lets the existing exact mapped-ring-isomorphism
verifier check the compiled endpoints without learning a new localization
semantics. The adapter remains campaign-specific and does not mutate JC.
"""

import argparse
from fractions import Fraction
import json
from pathlib import Path

from grandportage import check as C
from grandportage import format as F
from grandportage import groebner as G
from grandportage import kernel as K
from grandportage import store as S
from grandportage import triangular as TRI
from grandportage import verify as V


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_SPEC = (ROOT / "fixtures" / "jc_source_ladder" /
                "localized_triangular_solve_chain_v1.json")
SOURCE_MODEL = "JC-SOURCE-TOP-LOCALIZED"
TARGET_MODEL = "JC-SOURCE-TOP-NORMALIZED"
EDGE = "JC-SOURCE-TOP-SOLVE-EQUIVALENCE"
SECOND_SOURCE_MODEL = "JC-SOURCE-SECOND-LOCALIZED"
SECOND_TARGET_MODEL = "JC-SOURCE-SECOND-NORMALIZED"
SECOND_EDGE = "JC-SOURCE-SECOND-SOLVE-EQUIVALENCE"


def _canonical(value, variables, characteristic):
    return G.canonical_polynomial(value, variables, characteristic)


def _unique_nonzero(values, variables, characteristic, where):
    result = []
    for value in values:
        canonical = _canonical(value, variables, characteristic)
        if G.parse_polynomial(canonical, variables, characteristic).is_zero:
            continue
        if canonical in result:
            raise ValueError("%s contains duplicate generator %s" % (
                where, canonical))
        result.append(canonical)
    return result


def _context_inverse_witness(unit, context, variables, characteristic):
    """Find and check a polynomial inverse forced by a binomial context."""
    unit_index = variables.index(unit)
    zero_monomial = (0,) * len(variables)
    for generator in context:
        polynomial = G.parse_polynomial(
            generator, variables, characteristic)
        if len(polynomial.terms) != 2:
            continue
        constant = polynomial.terms.get(zero_monomial)
        if constant is None:
            continue
        power_terms = [
            (monomial, coefficient)
            for monomial, coefficient in polynomial.terms.items()
            if monomial != zero_monomial
        ]
        monomial, coefficient = power_terms[0]
        exponent = monomial[unit_index]
        if (exponent <= 0
                or any(power for index, power in enumerate(monomial)
                       if index != unit_index)):
            continue
        if characteristic == 0:
            inverse_coefficient = -Fraction(coefficient, constant)
        else:
            inverse_coefficient = (
                -int(coefficient) * pow(int(constant), -1, characteristic)
            ) % characteristic
        witness_monomial = list(monomial)
        witness_monomial[unit_index] -= 1
        witness = G.render_polynomial(G.Polynomial(
            variables, characteristic,
            {tuple(witness_monomial): inverse_coefficient},
        ))
        target = _canonical(
            "%s*(%s)-1" % (unit, witness), variables, characteristic)
        try:
            G.standard_representation(
                target, [generator], variables, characteristic)
        except G.CertificateError:
            continue
        return witness
    return None


def _zero_vector(length):
    return ["0"] * length


def _unit_vector(length, index):
    result = _zero_vector(length)
    result[index] = "1"
    return result


def _add(left, right, variables, characteristic):
    return _canonical("(%s)+(%s)" % (left, right), variables, characteristic)


def _subtract(left, right, variables, characteristic):
    return _canonical("(%s)-(%s)" % (left, right), variables, characteristic)


def _multiply(left, right, variables, characteristic):
    return _canonical("(%s)*(%s)" % (left, right), variables, characteristic)


def _scale_vector(scalar, vector, variables, characteristic):
    return [
        _multiply(scalar, value, variables, characteristic)
        for value in vector
    ]


def _subtract_vectors(left, right, variables, characteristic):
    return [
        _subtract(a, b, variables, characteristic)
        for a, b in zip(left, right)
    ]


def _coefficient_inverse(coefficient, unit_witnesses, variables,
                         characteristic):
    polynomial = G.parse_polynomial(
        coefficient, variables, characteristic)
    if len(polynomial.terms) != 1:
        raise ValueError("a checked solve coefficient is not one monomial")
    monomial, scalar = next(iter(polynomial.terms.items()))
    if characteristic == 0:
        inverse_scalar = Fraction(1, 1) / scalar
    else:
        inverse_scalar = pow(int(scalar), -1, characteristic)
    factors = [str(inverse_scalar)]
    for index, exponent in enumerate(monomial):
        if not exponent:
            continue
        unit = variables[index]
        if unit not in unit_witnesses:
            raise ValueError("coefficient uses undeclared unit %s" % unit)
        factors.extend([unit_witnesses[unit]] * exponent)
    return _canonical("*".join("(%s)" % value for value in factors),
                      variables, characteristic)


def _ring_iso_certificate(spec, report, extended, context,
                          inverse_equations, unit_witnesses,
                          source_generators, target_generators,
                          forward, inverse):
    """Compose exact pullback cofactors from the checked solve receipts."""
    characteristic = spec["characteristic"]
    initial = [
        _canonical(value, extended, characteristic)
        for value in spec["initial_generators"]
    ]
    source_count = len(source_generators)
    context_count = len(context)
    initial_offset = context_count
    inverse_offset = context_count + len(initial)
    relation_generators = list(context) + list(inverse_equations)
    relation_indices = (
        list(range(context_count))
        + list(range(inverse_offset, source_count))
    )

    current_polynomials = list(initial)
    current_representations = [
        _unit_vector(source_count, initial_offset + index)
        for index in range(len(initial))
    ]
    pivot_representations = {}

    for checked, authored in zip(report["steps"], spec["steps"]):
        equation_index = authored["equation_index"]
        pivot = checked["pivot"]
        solution = _canonical(
            checked["solution"], extended, characteristic)
        residual = _canonical(
            "%s-(%s)" % (pivot, solution), extended, characteristic)
        coefficient_inverse = _coefficient_inverse(
            checked["coefficient"], unit_witnesses,
            extended, characteristic)
        defect = _canonical(
            "(%s)*(%s)-1" % (
                coefficient_inverse, checked["coefficient"]),
            extended, characteristic)
        defect_cofactors = (
            G.standard_representation(
                defect, relation_generators, extended, characteristic)
            if relation_generators else []
        )
        debt_cofactors = list(
            checked.get("normalization_cofactors") or [])
        debt_cofactors += [
            "0" for _value in inverse_equations
        ]
        if len(debt_cofactors) != len(relation_generators):
            raise ValueError("normalization receipt has the wrong arity")

        equation_representation = current_representations[equation_index]
        residual_representation = _scale_vector(
            coefficient_inverse, equation_representation,
            extended, characteristic)
        for relation_index, debt, unit_defect in zip(
                relation_indices, debt_cofactors, defect_cofactors):
            correction = _add(
                _multiply(coefficient_inverse, debt,
                          extended, characteristic),
                _multiply(residual, unit_defect,
                          extended, characteristic),
                extended, characteristic)
            residual_representation[relation_index] = _subtract(
                residual_representation[relation_index], correction,
                extended, characteristic)
        G.check_membership_identity(
            residual, source_generators, residual_representation,
            extended, characteristic)
        pivot_representations[pivot] = residual_representation

        images = dict((name, name) for name in extended)
        images[pivot] = solution
        expected_outputs = [
            _canonical(value, extended, characteristic)
            for value in authored["output_generators"]
        ]
        next_polynomials = []
        next_representations = []
        output_index = 0
        division_variables = [pivot] + [
            value for value in extended if value != pivot
        ]
        for index, old in enumerate(current_polynomials):
            if index == equation_index:
                continue
            output = G.substitute_polynomial(
                old, extended, images, characteristic)
            if G.parse_polynomial(
                    output, extended, characteristic).is_zero:
                continue
            output = _canonical(output, extended, characteristic)
            if output != expected_outputs[output_index]:
                raise ValueError("chain output drift while composing proof")
            difference = _subtract(
                old, output, extended, characteristic)
            quotient = G.standard_representation(
                difference, [residual], division_variables,
                characteristic)[0]
            output_representation = _subtract_vectors(
                current_representations[index],
                _scale_vector(
                    quotient, residual_representation,
                    extended, characteristic),
                extended, characteristic)
            G.check_membership_identity(
                output, source_generators, output_representation,
                extended, characteristic)
            next_polynomials.append(output)
            next_representations.append(output_representation)
            output_index += 1
        if output_index != len(expected_outputs):
            raise ValueError("chain output count drift while composing proof")
        current_polynomials = next_polynomials
        current_representations = next_representations

    forward_cofactors = []
    forward_cofactors.extend(
        _unit_vector(source_count, index)
        for index in range(context_count)
    )
    forward_cofactors.extend(
        pivot_representations[step["pivot"]]
        for step in report["steps"]
    )
    forward_cofactors.extend(current_representations)
    forward_cofactors.extend(
        _unit_vector(source_count, inverse_offset + index)
        for index in range(len(inverse_equations))
    )
    if len(forward_cofactors) != len(target_generators):
        raise ValueError("forward proof has the wrong generator count")
    for generator, cofactors in zip(target_generators, forward_cofactors):
        pulled = G.substitute_polynomial(
            generator, extended, forward, characteristic)
        G.check_membership_identity(
            pulled, source_generators, cofactors,
            extended, characteristic)

    inverse_cofactors = []
    for generator in source_generators:
        pulled = G.substitute_polynomial(
            generator, extended, inverse, characteristic)
        cofactors = G.standard_representation(
            pulled, target_generators, extended, characteristic)
        G.check_membership_identity(
            pulled, target_generators, cofactors,
            extended, characteristic)
        inverse_cofactors.append(cofactors)
    return {
        "schema": "mapped_ring_iso_v1",
        "forward_cofactors": forward_cofactors,
        "inverse_cofactors": inverse_cofactors,
    }


def compile_events(spec):
    """Return graph events after independently replaying the chain."""
    report = TRI.verify(spec)
    receipt = report["source_receipt"]
    if receipt["id"] == "f2_h3_source_second_face":
        source_model = SECOND_SOURCE_MODEL
        target_model = SECOND_TARGET_MODEL
        edge_id = SECOND_EDGE
    else:
        source_model = SOURCE_MODEL
        target_model = TARGET_MODEL
        edge_id = EDGE
    variables = list(spec["ring_vars"])
    characteristic = spec["characteristic"]
    inverse_variables = []
    inverse_equations = []
    inverse_witnesses = {}
    context = list(report.get("normalization_generators") or [])
    for unit in spec["unit_generators"]:
        witness = _context_inverse_witness(
            unit, context, variables, characteristic)
        if witness is not None:
            inverse_witnesses[unit] = witness
            continue
        inverse = "GP_INV_%s" % unit
        if inverse in variables or inverse in inverse_variables:
            raise ValueError("inverse coordinate %s collides with the ring" % inverse)
        inverse_variables.append(inverse)
        inverse_equations.append("%s*%s-1" % (unit, inverse))
    extended = variables + inverse_variables
    source_generators = _unique_nonzero(
        context + list(spec["initial_generators"]) + inverse_equations,
        extended, characteristic, "compiled source")
    pivots = [step["pivot"] for step in report["steps"]]
    target_generators = _unique_nonzero(
        context + pivots + list(report["final_generators"])
        + inverse_equations,
        extended, characteristic, "compiled target")

    solutions = dict((step["pivot"], step["solution"])
                     for step in report["steps"])
    forward = {}
    inverse = {}
    for variable in extended:
        if variable in solutions:
            forward[variable] = _canonical(
                "%s-(%s)" % (variable, solutions[variable]),
                extended, characteristic)
            inverse[variable] = _canonical(
                "%s+(%s)" % (variable, solutions[variable]),
                extended, characteristic)
        else:
            forward[variable] = variable
            inverse[variable] = variable

    common = {
        "characteristic": characteristic,
        "coefficient_domain": spec["coefficient_domain"],
        "point_universe": spec["point_universe"],
        "ring_vars": extended,
        "cite": receipt["sha256"],
    }
    source = dict(common, **{
        "ev": "model",
        "id": source_model,
        "what": (
            "the frozen JC checked chain with every declared localization "
            "unit represented by an explicit inverse coordinate; receipt %s"
            % receipt["id"]),
        "generators": source_generators,
    })
    target = dict(common, **{
        "ev": "model",
        "id": target_model,
        "what": (
            "the same localized model after the checked ordered "
            "pivot translations; every solved pivot is the zero coordinate"),
        "generators": target_generators,
    })
    unit_witnesses = dict(inverse_witnesses)
    unit_witnesses.update(dict(
        (unit, "GP_INV_%s" % unit)
        for unit in spec["unit_generators"]
        if unit not in unit_witnesses
    ))
    ring_iso_certificate = _ring_iso_certificate(
        spec, report, extended, context, inverse_equations,
        unit_witnesses, source_generators, target_generators,
        forward, inverse)

    edge = {
        "ev": "edge",
        "id": edge_id,
        "src": source_model,
        "dst": target_model,
        "type": K.EQUIVALENCE,
        "map_kind": K.POLYNOMIAL,
        "why": (
            "the checked ordered affine translations become an ordinary "
            "polynomial equivalence after adjoining explicit inverses for "
            "the declared localization generators"),
        "forward": forward,
        "inverse": inverse,
        "ring_iso": True,
        "ring_iso_certificate": ring_iso_certificate,
        "cite": receipt["sha256"],
    }
    return {
        "events": [source, target, edge],
        "source_model": source_model,
        "target_model": target_model,
        "edge_id": edge_id,
        "ring_iso_certificate": ring_iso_certificate,
        "chain_report": report,
        "inverse_variables": inverse_variables,
        "inverse_witnesses": inverse_witnesses,
        "source_generators": source_generators,
        "target_generators": target_generators,
        "forward": forward,
        "inverse": inverse,
    }


def graph_from_spec(spec):
    compiled = compile_events(spec)
    graph = S.Graph()
    graph.apply(F.meta_event())
    for event in compiled["events"]:
        graph.apply(event)
    graph.validate()
    return graph, compiled


def write_campaign(root, spec, record=False):
    graph_path = Path(S.graph_path(str(root)))
    if graph_path.exists():
        raise ValueError("campaign graph already exists: %s" % graph_path)
    compiled = compile_events(spec)
    S.append(compiled["events"], root=str(root))
    results = V.verify_all(root=str(root)) if record else []
    graph = S.load(S.graph_path(str(root)))
    findings = C.run(graph)
    if record and graph.edges[compiled["edge_id"]].get("ring_iso_verdict") != V.ISO_VERIFIED:
        raise AssertionError("compiled chain did not earn ring-isomorphism authority")
    return {
        "graph": str(graph_path),
        "ring_iso_verdict": graph.edges[compiled["edge_id"]].get("ring_iso_verdict"),
        "findings": [finding.as_dict() for finding in findings],
        "verify_results": [list(item[:3]) for item in results],
        "compiled": compiled,
    }


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--spec", type=Path, default=DEFAULT_SPEC)
    parser.add_argument("--campaign-root", type=Path)
    parser.add_argument("--record", action="store_true")
    args = parser.parse_args(argv)
    if args.record and args.campaign_root is None:
        parser.error("--record requires --campaign-root")
    spec = json.loads(args.spec.read_text(encoding="utf-8"))
    graph, compiled = graph_from_spec(spec)
    output = {
        "chain_verdict": compiled["chain_report"]["verdict"],
        "checked_steps": compiled["chain_report"]["checked_steps"],
        "source_receipt": compiled["chain_report"]["source_receipt"],
        "inverse_variables": compiled["inverse_variables"],
        "inverse_witnesses": compiled["inverse_witnesses"],
        "source_model": compiled["source_model"],
        "target_model": compiled["target_model"],
        "edge": compiled["edge_id"],
        "graph_effect": (
            "declares one mapped EQUIVALENCE; identity transport requires "
            "a current verify.ring_iso verdict, which --record persists"),
        "authority_boundary": (
            "exact algebraized-localization models only; native source "
            "extraction, parent coverage, actual-source membership, and H3 "
            "remain outside"),
        "folded_models": sorted(graph.models),
    }
    if args.campaign_root is not None:
        campaign = write_campaign(args.campaign_root, spec, args.record)
        output["campaign"] = {
            key: value for key, value in campaign.items() if key != "compiled"
        }
    print(json.dumps(output, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
