"""Independent exact checker for ``selected_real_interval_v2`` receipts.

This module intentionally does not import :mod:`grandportage.ordered`.  It
recomputes the Sturm chain, variation counts, refinement, and interval sign
using a separately authored dense-polynomial implementation.  Sturm's theorem
is the named mathematical premise behind the root-count step.
"""

from fractions import Fraction

from . import groebner as G


METHOD = "selected_real_interval_v2"
_MAX_DEGREE = 64
_MAX_BITS = 4096


class OrderedReceiptError(ValueError):
    pass


def _trim(poly):
    poly = [Fraction(value) for value in poly]
    while poly and poly[-1] == 0:
        poly.pop()
    return poly


def _coefficients(expression, variable):
    try:
        parsed = G.parse_polynomial(expression, [variable], 0)
    except (G.CertificateError, TypeError, ValueError) as exc:
        raise OrderedReceiptError(str(exc))
    degree = max((power[0] for power in parsed.terms), default=-1)
    if degree > _MAX_DEGREE:
        raise OrderedReceiptError("ordered polynomial degree exceeds the bound")
    answer = [Fraction(0)] * (degree + 1)
    for power, coefficient in parsed.terms.items():
        value = Fraction(coefficient)
        if max(value.numerator.bit_length(), value.denominator.bit_length()) > _MAX_BITS:
            raise OrderedReceiptError("ordered coefficient exceeds the bit bound")
        answer[power[0]] = value
    return _trim(answer)


def _evaluate(poly, value):
    answer = Fraction(0)
    for coefficient in reversed(poly):
        answer = answer * value + coefficient
    return answer


def _derivative(poly):
    return _trim([index * value for index, value in enumerate(poly)][1:])


def _divmod(left, right):
    left, right = _trim(left), _trim(right)
    if not right:
        raise OrderedReceiptError("polynomial division by zero")
    quotient = [Fraction(0)] * max(0, len(left) - len(right) + 1)
    while left and len(left) >= len(right):
        shift = len(left) - len(right)
        coefficient = left[-1] / right[-1]
        quotient[shift] += coefficient
        for index, value in enumerate(right):
            left[index + shift] -= coefficient * value
        left = _trim(left)
    return _trim(quotient), left


def _monic(poly):
    poly = _trim(poly)
    return ([value / poly[-1] for value in poly] if poly else [])


def _gcd(left, right):
    left, right = _trim(left), _trim(right)
    while right:
        _quotient, remainder = _divmod(left, right)
        left, right = right, remainder
    return _monic(left)


def _sturm(poly):
    poly = _trim(poly)
    if len(poly) < 2:
        raise OrderedReceiptError("the selected generator must be nonconstant")
    sequence = [poly, _derivative(poly)]
    while sequence[-1]:
        _quotient, remainder = _divmod(sequence[-2], sequence[-1])
        if not remainder:
            break
        sequence.append([-value for value in remainder])
        if len(sequence) > len(poly) + 1:
            raise OrderedReceiptError("Sturm chain exceeds its degree bound")
    return [value for value in sequence if value]


def _variations(sequence, at):
    signs = []
    for polynomial in sequence:
        value = _evaluate(polynomial, at)
        if value:
            signs.append(1 if value > 0 else -1)
    return sum(left != right for left, right in zip(signs, signs[1:]))


def _root_count(sequence, lo, hi):
    return 0 if lo >= hi else _variations(sequence, lo) - _variations(sequence, hi)


def _remove_root(poly, root):
    factor = [-root, Fraction(1)]
    answer, removed = list(poly), False
    while len(answer) > 1:
        quotient, remainder = _divmod(answer, factor)
        if remainder:
            break
        answer, removed = quotient, True
    return answer if removed else None


def _interval_mul(left, right):
    products = (left[0] * right[0], left[0] * right[1],
                left[1] * right[0], left[1] * right[1])
    return min(products), max(products)


def _interval_evaluate(poly, lo, hi):
    value = (Fraction(0), Fraction(0))
    for coefficient in reversed(poly):
        product = _interval_mul(value, (lo, hi))
        value = product[0] + coefficient, product[1] + coefficient
    return value


def _text(value):
    value = Fraction(value)
    return (str(value.numerator) if value.denominator == 1
            else "%s/%s" % (value.numerator, value.denominator))


def _certificate(generator_text, expression, embedding, selection,
                 root_interval, value_interval, sign, sequence,
                 zero_gcd=None, endpoint_root=None):
    return {
        "method": METHOD,
        "generator": generator_text,
        "expression": expression,
        "embedding": embedding,
        "selection_interval": {"lo": _text(selection[0]),
                               "hi": _text(selection[1])},
        "root_interval": {"lo": _text(root_interval[0]),
                          "hi": _text(root_interval[1])},
        "value_interval": {"lo": _text(value_interval[0]),
                           "hi": _text(value_interval[1])},
        "sign": sign,
        "sturm_chain": [[_text(value) for value in polynomial]
                        for polynomial in sequence],
        "variations": {"lo": _variations(sequence, root_interval[0]),
                       "hi": _variations(sequence, root_interval[1])},
        "zero_gcd": ([_text(value) for value in zero_gcd]
                     if zero_gcd else None),
        "endpoint_root": (_text(endpoint_root)
                          if endpoint_root is not None else None),
    }


def expected_receipt(model, expression, max_refinements=256):
    if model.get("point_universe") != "REAL_CLOSURE" or model.get("characteristic") != 0:
        raise OrderedReceiptError("ordered receipt requires characteristic-zero REAL_CLOSURE")
    embedding = model.get("embedding") or {}
    variable = embedding.get("var")
    if embedding.get("kind") != "REAL":
        raise OrderedReceiptError("ordered receipt requires a selected REAL embedding")
    ring, generators = model.get("ring_vars") or [], model.get("generators")
    if ring != [variable] or not isinstance(generators, list) or len(generators) != 1:
        raise OrderedReceiptError("ordered receipt requires one variable and generator")
    try:
        lo = Fraction(embedding["isolating_interval"]["lo"])
        hi = Fraction(embedding["isolating_interval"]["hi"])
    except (KeyError, TypeError, ValueError, ZeroDivisionError):
        raise OrderedReceiptError("invalid selected interval")
    generator = _coefficients(generators[0], variable)
    wanted = _coefficients(expression, variable)
    sequence = _sturm(generator)
    selection = (lo, hi)
    lo_root, hi_root = _evaluate(generator, lo) == 0, _evaluate(generator, hi) == 0
    if lo_root and hi_root:
        raise OrderedReceiptError("both selection endpoints are roots")
    endpoint = lo if lo_root else hi if hi_root else None
    if endpoint is not None:
        remaining = _remove_root(generator, endpoint)
        if remaining and len(remaining) > 1 and _root_count(_sturm(remaining), lo, hi):
            raise OrderedReceiptError("selection contains another root")
        exact = _evaluate(wanted, endpoint)
        sign = 1 if exact > 0 else -1 if exact < 0 else 0
        common = _gcd(generator, wanted) if sign == 0 else None
        return _certificate(generators[0], expression, embedding, selection,
                            (endpoint, endpoint), (exact, exact), sign,
                            sequence, common, endpoint)
    if _root_count(sequence, lo, hi) != 1:
        raise OrderedReceiptError("selection does not isolate one root")
    common = _gcd(generator, wanted)
    if len(common) > 1 and _root_count(_sturm(common), lo, hi) == 1:
        sign, value_interval = 0, (Fraction(0), Fraction(0))
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
                sign = 1 if exact > 0 else -1 if exact < 0 else 0
                lo = hi = midpoint
                value_interval = (exact, exact)
                break
            if _root_count(sequence, lo, midpoint) == 1:
                hi = midpoint
            else:
                lo = midpoint
            value_interval = _interval_evaluate(wanted, lo, hi)
        if sign is None:
            raise OrderedReceiptError("bounded refinement did not decide sign")
    return _certificate(generators[0], expression, embedding, selection,
                        (lo, hi), value_interval, sign, sequence,
                        common if sign == 0 else None)


def verify(model, expression, receipt):
    """Recompute and compare the complete exact receipt."""
    if not isinstance(receipt, dict) or receipt.get("method") != METHOD:
        raise OrderedReceiptError("expected a selected_real_interval_v2 receipt")
    expected = expected_receipt(model, expression)
    if receipt != expected:
        raise OrderedReceiptError(
            "ordered receipt does not replay under the independent Sturm "
            "checker")
    return receipt["sign"]
