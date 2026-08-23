"""Deliberately naive exact-polynomial reference oracle.

This module is an audit anchor for the optimized checker.  It must not import
Grand Portage's sparse-polynomial implementation or reuse any of its helpers.
Polynomials are plain dictionaries from exponent tuples to exact coefficients.
The intentionally small budget makes inability to check explicit rather than
turning the oracle into a second production engine.
"""

import ast
from fractions import Fraction
import re


REFERENCE_CHECKED = "REFERENCE_CHECKED"
REFERENCE_UNCHECKED = "REFERENCE_UNCHECKED"
_IDENTIFIER = re.compile(r"^[A-Za-z][A-Za-z0-9_]*$")


class ReferenceError(ValueError):
    pass


class ReferenceUnchecked(ReferenceError):
    """The independent evaluator declined an input outside its audit budget."""


class ReferenceMismatch(ReferenceError):
    """The independently expanded certificate is false."""


class Budget:
    def __init__(self, max_terms=2000, max_degree=256, max_steps=250000):
        self.max_terms = max_terms
        self.max_degree = max_degree
        self.steps = max_steps

    def spend(self, amount=1):
        self.steps -= max(1, amount)
        if self.steps < 0:
            raise ReferenceUnchecked("reference arithmetic budget exceeded")

    def check(self, terms):
        if len(terms) > self.max_terms:
            raise ReferenceUnchecked("reference term-count budget exceeded")
        if any(sum(monomial) > self.max_degree for monomial in terms):
            raise ReferenceUnchecked("reference degree budget exceeded")


def _coefficient(value, characteristic):
    if characteristic:
        if isinstance(value, Fraction):
            denominator = value.denominator % characteristic
            if not denominator:
                raise ReferenceError("inadmissible denominator")
            return (value.numerator * pow(denominator, -1, characteristic)) \
                % characteristic
        return int(value) % characteristic
    try:
        return Fraction(value)
    except (TypeError, ValueError, ZeroDivisionError) as exc:
        raise ReferenceError("invalid exact coefficient") from exc


def _clean(terms, characteristic, budget):
    answer = {}
    for monomial, coefficient in terms.items():
        coefficient = _coefficient(coefficient, characteristic)
        if coefficient:
            answer[tuple(monomial)] = coefficient
    budget.check(answer)
    return answer


def add(left, right, characteristic, budget):
    budget.spend(len(left) + len(right))
    answer = dict(left)
    for monomial, coefficient in right.items():
        answer[monomial] = _coefficient(
            answer.get(monomial, 0) + coefficient, characteristic)
    return _clean(answer, characteristic, budget)


def scale(polynomial, coefficient, characteristic, budget):
    coefficient = _coefficient(coefficient, characteristic)
    budget.spend(len(polynomial))
    return _clean({
        monomial: _coefficient(value * coefficient, characteristic)
        for monomial, value in polynomial.items()
    }, characteristic, budget)


def multiply(left, right, characteristic, budget):
    budget.spend(max(1, len(left) * len(right)))
    answer = {}
    for left_monomial, left_coefficient in left.items():
        for right_monomial, right_coefficient in right.items():
            monomial = tuple(a + b for a, b in
                             zip(left_monomial, right_monomial))
            answer[monomial] = _coefficient(
                answer.get(monomial, 0)
                + left_coefficient * right_coefficient,
                characteristic,
            )
    return _clean(answer, characteristic, budget)


def _power(value, exponent, characteristic, budget, arity):
    if type(exponent) is not int or exponent < 0:
        raise ReferenceError("polynomial exponent must be nonnegative")
    if exponent > budget.max_degree:
        raise ReferenceUnchecked("reference degree budget exceeded")
    answer = {(0,) * arity: _coefficient(1, characteristic)}
    for _ in range(exponent):
        answer = multiply(answer, value, characteristic, budget)
    return answer


def _scalar_value(polynomial, arity):
    if any(monomial != (0,) * arity for monomial in polynomial):
        raise ReferenceError("polynomial division requires a scalar")
    return polynomial.get((0,) * arity, 0)


def parse(value, variables, characteristic=0, budget=None):
    budget = budget or Budget()
    variables = tuple(variables)
    if (len(set(variables)) != len(variables)
            or any(type(name) is not str or not _IDENTIFIER.fullmatch(name)
                   for name in variables)):
        raise ReferenceError("invalid reference ring variables")
    arity = len(variables)
    indices = {name: index for index, name in enumerate(variables)}
    if isinstance(value, dict):
        if set(value) != {"schema", "terms"} \
                or value.get("schema") != "sparse_polynomial_v1" \
                or not isinstance(value.get("terms"), list):
            raise ReferenceError("invalid sparse polynomial")
        if len(value["terms"]) > budget.max_terms:
            raise ReferenceUnchecked("reference term-count budget exceeded")
        terms = {}
        for term in value["terms"]:
            if not isinstance(term, dict) or set(term) != {
                    "coefficient", "powers"}:
                raise ReferenceError("invalid sparse term")
            monomial = [0] * arity
            if not isinstance(term["powers"], list):
                raise ReferenceError("invalid sparse powers")
            for factor in term["powers"]:
                if (not isinstance(factor, list) or len(factor) != 2
                        or factor[0] not in indices
                        or type(factor[1]) is not int or factor[1] <= 0):
                    raise ReferenceError("invalid sparse power")
                monomial[indices[factor[0]]] = factor[1]
            monomial = tuple(monomial)
            if monomial in terms:
                raise ReferenceError("duplicate sparse monomial")
            terms[monomial] = _coefficient(term["coefficient"], characteristic)
        return _clean(terms, characteristic, budget)
    if type(value) is not str or not value.strip():
        raise ReferenceError("polynomial must be a nonempty string")
    try:
        tree = ast.parse(value.replace("^", "**"), mode="eval")
    except (SyntaxError, RecursionError) as exc:
        raise ReferenceError("invalid polynomial syntax") from exc

    def visit(node):
        budget.spend()
        if isinstance(node, ast.Constant) and type(node.value) is int:
            coefficient = _coefficient(node.value, characteristic)
            return {} if not coefficient else {(0,) * arity: coefficient}
        if isinstance(node, ast.Name) and node.id in indices:
            monomial = [0] * arity
            monomial[indices[node.id]] = 1
            return {tuple(monomial): _coefficient(1, characteristic)}
        if isinstance(node, ast.UnaryOp):
            operand = visit(node.operand)
            if isinstance(node.op, ast.UAdd):
                return operand
            if isinstance(node.op, ast.USub):
                return scale(operand, -1, characteristic, budget)
        if isinstance(node, ast.BinOp):
            left = visit(node.left)
            right = visit(node.right)
            if isinstance(node.op, ast.Add):
                return add(left, right, characteristic, budget)
            if isinstance(node.op, ast.Sub):
                return add(left, scale(right, -1, characteristic, budget),
                           characteristic, budget)
            if isinstance(node.op, ast.Mult):
                return multiply(left, right, characteristic, budget)
            if isinstance(node.op, ast.Div):
                scalar = _scalar_value(right, arity)
                if not scalar:
                    raise ReferenceError(
                        "inadmissible denominator" if characteristic
                        else "division by zero")
                inverse = (_coefficient(Fraction(1, 1) / scalar, 0)
                           if not characteristic else
                           pow(int(scalar), -1, characteristic))
                return scale(left, inverse, characteristic, budget)
            if isinstance(node.op, ast.Pow) \
                    and isinstance(node.right, ast.Constant):
                return _power(left, node.right.value, characteristic,
                              budget, arity)
        raise ReferenceError("unsupported polynomial syntax")

    return visit(tree.body)


def substitute(polynomial, variables, images, characteristic=0, budget=None):
    budget = budget or Budget()
    variables = tuple(variables)
    source = parse(polynomial, variables, characteristic, budget)
    if not isinstance(images, dict) or set(images) != set(variables):
        raise ReferenceError("substitution must cover the reference ring")
    parsed_images = {
        name: parse(images[name], variables, characteristic, budget)
        for name in variables
    }
    answer = {}
    for monomial, coefficient in source.items():
        term = {(0,) * len(variables): coefficient}
        for name, exponent in zip(variables, monomial):
            term = multiply(term, _power(parsed_images[name], exponent,
                                         characteristic, budget,
                                         len(variables)),
                            characteristic, budget)
        answer = add(answer, term, characteristic, budget)
    return answer


def canonical_form(polynomial, variables, characteristic=0, budget=None):
    parsed = parse(polynomial, variables, characteristic, budget)
    return tuple(sorted(parsed.items(), reverse=True))


def reduce_by_explicit_cofactors(target, generators, cofactors, variables,
                                 characteristic=0, budget=None):
    """Check ``target = sum(cofactor_i * generator_i)`` independently."""
    if (not isinstance(generators, list) or not isinstance(cofactors, list)
            or len(generators) != len(cofactors)):
        raise ReferenceError("one cofactor is required per generator")
    budget = budget or Budget()
    wanted = parse(target, variables, characteristic, budget)
    expanded = {}
    for generator, cofactor in zip(generators, cofactors):
        product = multiply(
            parse(generator, variables, characteristic, budget),
            parse(cofactor, variables, characteristic, budget),
            characteristic, budget,
        )
        expanded = add(expanded, product, characteristic, budget)
    if expanded != wanted:
        raise ReferenceMismatch("reference cofactor expansion disagrees")
    return REFERENCE_CHECKED
