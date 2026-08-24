"""Exact, bounded checks at a selected real algebraic embedding.

This module is deliberately smaller than real algebraic geometry.  It answers
one question: the sign of a univariate rational polynomial at the unique real
root selected by a model's exact isolating interval.  Every operation uses
``Fraction`` arithmetic.  Failure to isolate or to decide within the bounded
refinement budget is inconclusive and never grants authority.
"""

from fractions import Fraction

from . import groebner as G


class OrderedError(ValueError):
    pass


ORDERED_RELATIONS = (
    "POSITIVE", "NEGATIVE", "NONNEGATIVE", "NONPOSITIVE",
)
_MAX_ORDERED_DEGREE = 64
_MAX_COEFFICIENT_BITS = 4096


def _trim(poly):
    poly = list(poly)
    while poly and poly[-1] == 0:
        poly.pop()
    return poly


def _coefficients(expression, variable):
    parsed = G.parse_polynomial(expression, [variable], 0)
    degree = max((power[0] for power in parsed.terms), default=-1)
    if degree > _MAX_ORDERED_DEGREE:
        raise OrderedError(
            "ordered polynomial degree %d exceeds the exact bound %d"
            % (degree, _MAX_ORDERED_DEGREE))
    if any(max(Fraction(value).numerator.bit_length(),
               Fraction(value).denominator.bit_length())
           > _MAX_COEFFICIENT_BITS for value in parsed.terms.values()):
        raise OrderedError("ordered polynomial coefficient exceeds the bit bound")
    answer = [Fraction(0)] * (degree + 1)
    for power, coefficient in parsed.terms.items():
        answer[power[0]] = Fraction(coefficient)
    return _trim(answer)


def _evaluate(poly, value):
    answer = Fraction(0)
    for coefficient in reversed(poly):
        answer = answer * value + coefficient
    return answer


def _derivative(poly):
    return _trim([power * coefficient
                  for power, coefficient in enumerate(poly)][1:])


def _divmod(left, right):
    left = _trim(left)
    right = _trim(right)
    if not right:
        raise OrderedError("polynomial division by zero")
    quotient = [Fraction(0)] * max(0, len(left) - len(right) + 1)
    while left and len(left) >= len(right):
        shift = len(left) - len(right)
        coefficient = left[-1] / right[-1]
        quotient[shift] = coefficient
        for index, value in enumerate(right):
            left[index + shift] -= coefficient * value
        left = _trim(left)
    return _trim(quotient), left


def _monic(poly):
    poly = _trim(poly)
    if not poly:
        return []
    leading = poly[-1]
    return [value / leading for value in poly]


def _gcd(left, right):
    left, right = _trim(left), _trim(right)
    while right:
        _quotient, remainder = _divmod(left, right)
        left, right = right, remainder
    return _monic(left)


def _sturm(poly):
    poly = _trim(poly)
    if len(poly) < 2:
        raise OrderedError("the selected generator must be nonconstant")
    sequence = [poly, _derivative(poly)]
    while sequence[-1]:
        _quotient, remainder = _divmod(sequence[-2], sequence[-1])
        if not remainder:
            break
        sequence.append([-value for value in remainder])
        if len(sequence) > len(poly) + 1:
            raise OrderedError("Sturm sequence exceeded its degree bound")
    return [value for value in sequence if value]


def _variations(sequence, at):
    signs = []
    for polynomial in sequence:
        value = _evaluate(polynomial, at)
        if value:
            signs.append(1 if value > 0 else -1)
    return sum(left != right for left, right in zip(signs, signs[1:]))


def _root_count(sequence, lo, hi):
    if lo >= hi:
        return 0
    return _variations(sequence, lo) - _variations(sequence, hi)


def _remove_root(poly, root):
    """Remove the full ``(x-root)`` factor and return the remaining factor."""
    factor = [-root, Fraction(1)]
    answer = list(poly)
    removed = False
    while len(answer) > 1:
        quotient, remainder = _divmod(answer, factor)
        if remainder:
            break
        answer = quotient
        removed = True
    return answer if removed else None


def _interval_mul(left, right):
    products = [left[0] * right[0], left[0] * right[1],
                left[1] * right[0], left[1] * right[1]]
    return min(products), max(products)


def _interval_evaluate(poly, lo, hi):
    value = (Fraction(0), Fraction(0))
    interval = (lo, hi)
    for coefficient in reversed(poly):
        product = _interval_mul(value, interval)
        value = product[0] + coefficient, product[1] + coefficient
    return value


def _text(value):
    return (str(value.numerator) if value.denominator == 1
            else "%s/%s" % (value.numerator, value.denominator))


def selected_real_sign(model, expression, max_refinements=256):
    """Return ``(sign, certificate)`` or raise ``OrderedError``.

    The certificate is intentionally a deterministic replay receipt rather
    than a search transcript.  The store recomputes it from the model and atom
    before activating a recorded verdict.
    """
    if type(max_refinements) is not int or not 0 <= max_refinements <= 256:
        raise OrderedError("ordered refinement bound must be from 0 to 256")
    if model.get("point_universe") != "REAL_CLOSURE":
        raise OrderedError("ordered conditions require point_universe REAL_CLOSURE")
    if model.get("characteristic") != 0:
        raise OrderedError("REAL_CLOSURE requires characteristic 0")
    embedding = model.get("embedding")
    if not isinstance(embedding, dict) or embedding.get("kind") != "REAL":
        raise OrderedError("REAL_CLOSURE requires a selected REAL embedding")
    ring = model.get("ring_vars") or []
    generators = model.get("generators")
    variable = embedding.get("var")
    if ring != [variable] or not isinstance(generators, list) or len(generators) != 1:
        raise OrderedError(
            "ordered verification currently requires one ring variable and "
            "one selected generator")
    interval = embedding.get("isolating_interval") or {}
    try:
        lo, hi = Fraction(interval["lo"]), Fraction(interval["hi"])
    except (KeyError, TypeError, ValueError, ZeroDivisionError):
        raise OrderedError("the selected REAL embedding needs exact interval bounds")
    generator = _coefficients(generators[0], variable)
    wanted = _coefficients(expression, variable)
    if not generator:
        raise OrderedError("the selected generator must be nonzero")
    lo_root = _evaluate(generator, lo) == 0
    hi_root = _evaluate(generator, hi) == 0
    if lo_root and hi_root:
        raise OrderedError("the selected interval contains roots at both endpoints")
    endpoint_root = lo if lo_root else hi if hi_root else None
    if endpoint_root is not None:
        remaining = _remove_root(generator, endpoint_root)
        if (remaining and len(remaining) > 1
                and _root_count(_sturm(remaining), lo, hi)):
            raise OrderedError(
                "the selected interval contains another real root besides "
                "its endpoint root")
        exact = _evaluate(wanted, endpoint_root)
        sign = 1 if exact > 0 else -1 if exact < 0 else 0
        certificate = {
            "method": "selected_real_interval_v1",
            "generator": generators[0],
            "embedding": embedding,
            "root_interval": {
                "lo": _text(endpoint_root), "hi": _text(endpoint_root)},
            "value_interval": {"lo": _text(exact), "hi": _text(exact)},
            "sign": sign,
        }
        return sign, certificate
    sequence = _sturm(generator)
    if _root_count(sequence, lo, hi) != 1:
        raise OrderedError("the selected interval must isolate exactly one real root")

    common = _gcd(generator, wanted)
    if len(common) > 1 and _root_count(_sturm(common), lo, hi) == 1:
        sign = 0
        value_interval = (Fraction(0), Fraction(0))
    else:
        sign = None
        value_interval = _interval_evaluate(wanted, lo, hi)
        for _step in range(max_refinements + 1):
            if value_interval[0] > 0:
                sign = 1
                break
            if value_interval[1] < 0:
                sign = -1
                break
            midpoint = (lo + hi) / 2
            if _evaluate(generator, midpoint) == 0:
                exact = _evaluate(wanted, midpoint)
                sign = (1 if exact > 0 else -1 if exact < 0 else 0)
                lo = hi = midpoint
                value_interval = (exact, exact)
                break
            if _root_count(sequence, lo, midpoint) == 1:
                hi = midpoint
            else:
                lo = midpoint
            value_interval = _interval_evaluate(wanted, lo, hi)
        if sign is None:
            raise OrderedError(
                "exact interval refinement did not separate the sign within "
                "%d steps" % max_refinements)

    certificate = {
        "method": "selected_real_interval_v1",
        "generator": generators[0],
        "embedding": embedding,
        "root_interval": {"lo": _text(lo), "hi": _text(hi)},
        "value_interval": {
            "lo": _text(value_interval[0]),
            "hi": _text(value_interval[1]),
        },
        "sign": sign,
    }
    return sign, certificate


def relation_holds(relation, sign):
    return {
        "POSITIVE": sign > 0,
        "NEGATIVE": sign < 0,
        "NONNEGATIVE": sign >= 0,
        "NONPOSITIVE": sign <= 0,
    }[relation]
