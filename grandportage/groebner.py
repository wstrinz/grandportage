"""Small exact checker for Gröbner/elimination certificates.

The search engine is deliberately absent from this module.  A backend may
propose a basis and reduction witnesses; this code only parses exact
polynomials, expands finite identities, and checks the leading-monomial
inequalities required by Buchberger's criterion.

Version 1 is intentionally narrow: coefficients are Q or a prime field and the
monomial order is pure lexicographic order with eliminated variables first.
That is already enough for the elimination theorem, while keeping the trusted
checker substantially smaller than a CAS.
"""

import ast
from fractions import Fraction
from functools import lru_cache
import re


class CertificateError(ValueError):
    """A proposed certificate is malformed or mathematically false."""


_MAX_EXPRESSION_LENGTH = 100000
_MAX_AST_NODES = 20000
_MAX_EXPONENT = 100000
_MAX_TERMS = 50000
_MAX_COEFFICIENT_BITS = 8192
_MAX_VARIABLES = 64
_MAX_GENERATORS = 256
_MAX_BASIS = 64
_MAX_TERM_PRODUCTS = 250000
_MAX_MULTIPLICATION_BIT_WORK = 20000000
_MAX_TOTAL_ARITHMETIC_WORK = 20000000
_MAX_CERTIFICATE_NODES = 250000
_MAX_CERTIFICATE_CHARACTERS = 2000000
_MAX_SPARSE_FACTOR_ENTRIES = 250000
_IDENTIFIER = re.compile(r"^[A-Za-z][A-Za-z0-9_]*$")
SPARSE_POLYNOMIAL_SCHEMA = "sparse_polynomial_v1"


def _valid_characteristic(value):
    if type(value) is not int or value < 0 or value.bit_length() > 32:
        return False
    return _prime_characteristic(value)


@lru_cache(maxsize=64)
def _prime_characteristic(value):
    if value == 0:
        return True
    if value < 2 or value % 2 == 0:
        return value == 2
    divisor = 3
    while divisor * divisor <= value:
        if value % divisor == 0:
            return False
        divisor += 2
    return True

def _coefficient(value, characteristic):
    if characteristic == 0:
        answer = Fraction(value)
        if (answer.numerator.bit_length() > _MAX_COEFFICIENT_BITS
                or answer.denominator.bit_length() > _MAX_COEFFICIENT_BITS):
            raise CertificateError("a rational coefficient is too large")
        return answer
    answer = int(value) % characteristic
    if answer.bit_length() > _MAX_COEFFICIENT_BITS:
        raise CertificateError("a finite-field coefficient is too large")
    return answer


def _coefficient_bits(value):
    if isinstance(value, Fraction):
        return max(value.numerator.bit_length(), value.denominator.bit_length())
    return int(value).bit_length()


def _add(a, b, characteristic):
    return _coefficient(a + b, characteristic)


def _mul(a, b, characteristic):
    return _coefficient(a * b, characteristic)


def _inverse(a, characteristic):
    if not a:
        raise CertificateError("division by zero in a polynomial coefficient")
    if characteristic == 0:
        return Fraction(1, 1) / a
    try:
        return pow(int(a), -1, characteristic)
    except ValueError:
        raise CertificateError(
            "%s is not invertible modulo %s" % (a, characteristic)
        )


class _ArithmeticBudget:
    """One global work budget shared by every polynomial in a proof check."""

    def __init__(self, remaining=_MAX_TOTAL_ARITHMETIC_WORK):
        self.remaining = remaining

    def spend(self, amount):
        amount = max(1, int(amount))
        if amount > self.remaining:
            raise CertificateError(
                "certificate exceeded the global arithmetic-work budget"
            )
        self.remaining -= amount


class Polynomial:
    """Sparse exact polynomial with a fixed ordered variable tuple."""

    def __init__(self, variables, characteristic, terms=None, budget=None):
        self.variables = tuple(variables)
        self.characteristic = characteristic
        self._budget = budget or _ArithmeticBudget()
        zero = _coefficient(0, characteristic)
        self.terms = {}
        for monomial, coefficient in (terms or {}).items():
            monomial = tuple(monomial)
            if len(monomial) != len(self.variables):
                raise CertificateError("monomial has the wrong arity")
            coefficient = _coefficient(coefficient, characteristic)
            if coefficient != zero:
                self.terms[monomial] = coefficient
        if len(self.terms) > _MAX_TERMS:
            raise CertificateError("a polynomial has too many terms")

    @classmethod
    def scalar(cls, variables, characteristic, value, budget=None):
        value = _coefficient(value, characteristic)
        if not value:
            return cls(variables, characteristic, budget=budget)
        return cls(variables, characteristic, {
            (0,) * len(tuple(variables)): value,
        }, budget=budget)

    @classmethod
    def variable(cls, variables, characteristic, name, budget=None):
        variables = tuple(variables)
        try:
            index = variables.index(name)
        except ValueError:
            raise CertificateError(
                "unknown variable %r; expected one of %s"
                % (name, ", ".join(variables))
            )
        monomial = [0] * len(variables)
        monomial[index] = 1
        return cls(variables, characteristic, {
            tuple(monomial): _coefficient(1, characteristic),
        }, budget=budget)

    def _same_ring(self, other):
        if not isinstance(other, Polynomial):
            raise CertificateError("polynomial operation received a non-polynomial")
        if (self.variables != other.variables
                or self.characteristic != other.characteristic):
            raise CertificateError("polynomials belong to different rings")
        if self._budget is not other._budget:
            raise CertificateError(
                "polynomials belong to different checker invocations"
            )

    def __add__(self, other):
        self._same_ring(other)
        bits = max(
            [_coefficient_bits(value) for value in self.terms.values()]
            + [_coefficient_bits(value) for value in other.terms.values()]
            + [1]
        )
        self._budget.spend((len(self.terms) + len(other.terms)) * bits)
        terms = dict(self.terms)
        for monomial, coefficient in other.terms.items():
            value = _add(
                terms.get(monomial, _coefficient(0, self.characteristic)),
                coefficient,
                self.characteristic,
            )
            if value:
                terms[monomial] = value
            else:
                terms.pop(monomial, None)
        return Polynomial(
            self.variables, self.characteristic, terms, self._budget
        )

    def __neg__(self):
        bits = max((_coefficient_bits(value)
                    for value in self.terms.values()), default=1)
        self._budget.spend(len(self.terms) * bits)
        return Polynomial(
            self.variables,
            self.characteristic,
            dict((m, _mul(-1, c, self.characteristic))
                 for m, c in self.terms.items()),
            self._budget,
        )

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        self._same_ring(other)
        products = len(self.terms) * len(other.terms)
        left_bits = max((_coefficient_bits(value)
                         for value in self.terms.values()), default=1)
        right_bits = max((_coefficient_bits(value)
                          for value in other.terms.values()), default=1)
        work = products * left_bits * right_bits
        if (products > _MAX_TERM_PRODUCTS
                or work > _MAX_MULTIPLICATION_BIT_WORK):
            raise CertificateError(
                "polynomial multiplication exceeded the operation budget"
            )
        self._budget.spend(work)
        terms = {}
        for left_monomial, left_coefficient in self.terms.items():
            for right_monomial, right_coefficient in other.terms.items():
                monomial = tuple(
                    a + b for a, b in zip(left_monomial, right_monomial)
                )
                value = _add(
                    terms.get(monomial, _coefficient(0, self.characteristic)),
                    _mul(left_coefficient, right_coefficient,
                         self.characteristic),
                    self.characteristic,
                )
                if value:
                    terms[monomial] = value
                else:
                    terms.pop(monomial, None)
                if len(terms) > _MAX_TERMS:
                    raise CertificateError(
                        "polynomial multiplication exceeded the term budget"
                    )
        return Polynomial(
            self.variables, self.characteristic, terms, self._budget
        )

    def __pow__(self, exponent):
        if type(exponent) is not int or not 0 <= exponent <= _MAX_EXPONENT:
            raise CertificateError(
                "polynomial exponent must be an integer between 0 and %d"
                % _MAX_EXPONENT
            )
        answer = Polynomial.scalar(
            self.variables, self.characteristic, 1, self._budget
        )
        base = self
        while exponent:
            if exponent & 1:
                answer = answer * base
            exponent //= 2
            if exponent:
                base = base * base
        return answer

    def divide_by_scalar(self, scalar):
        if any(any(power for power in monomial)
               for monomial in scalar.terms):
            raise CertificateError(
                "division is allowed only by a nonzero scalar coefficient"
            )
        if len(scalar.terms) != 1:
            raise CertificateError(
                "division is allowed only by a nonzero scalar coefficient"
            )
        coefficient = next(iter(scalar.terms.values()))
        inverse = _inverse(coefficient, self.characteristic)
        return self * Polynomial.scalar(
            self.variables, self.characteristic, inverse, self._budget
        )

    @property
    def is_zero(self):
        return not self.terms

    def leading_term(self):
        """Return the coefficient and monomial for pure lexicographic order."""
        if self.is_zero:
            raise CertificateError("the zero polynomial has no leading term")
        monomial = max(self.terms)
        return self.terms[monomial], monomial

    def uses_any(self, indices):
        return any(
            any(monomial[index] for index in indices)
            for monomial in self.terms
        )

    def __eq__(self, other):
        return (
            isinstance(other, Polynomial)
            and self.variables == other.variables
            and self.characteristic == other.characteristic
            and self.terms == other.terms
        )


def _parse_sparse_polynomial(value, variables, characteristic, budget):
    """Decode the canonical bounded sparse-polynomial object format."""
    if set(value) != {"schema", "terms"}:
        raise CertificateError(
            "a sparse polynomial must contain exactly schema and terms"
        )
    if value["schema"] != SPARSE_POLYNOMIAL_SCHEMA:
        raise CertificateError(
            "sparse polynomial schema must be %s"
            % SPARSE_POLYNOMIAL_SCHEMA
        )
    terms = value["terms"]
    if not isinstance(terms, list) or len(terms) > _MAX_TERMS:
        raise CertificateError(
            "sparse polynomial terms must be a list of at most %d entries"
            % _MAX_TERMS
        )
    variable_indices = dict(
        (name, index) for index, name in enumerate(variables)
    )
    decoded = {}
    previous = None
    factor_entries = 0
    for position, term in enumerate(terms):
        if not isinstance(term, dict) or set(term) != {
                "coefficient", "powers"}:
            raise CertificateError(
                "sparse term %d must contain exactly coefficient and powers"
                % position
            )
        coefficient_text = term["coefficient"]
        if type(coefficient_text) is not str:
            raise CertificateError(
                "sparse term %d coefficient must be a canonical string"
                % position
            )
        try:
            if characteristic == 0:
                coefficient = _coefficient(
                    Fraction(coefficient_text), characteristic
                )
            else:
                if not re.fullmatch(r"[0-9]+", coefficient_text):
                    raise ValueError
                coefficient = _coefficient(
                    int(coefficient_text), characteristic
                )
        except (ValueError, ZeroDivisionError):
            raise CertificateError(
                "sparse term %d coefficient is invalid" % position
            )
        if not coefficient or _coefficient_text(coefficient) != coefficient_text:
            raise CertificateError(
                "sparse term %d coefficient is not nonzero canonical form"
                % position
            )
        powers = term["powers"]
        if not isinstance(powers, list):
            raise CertificateError(
                "sparse term %d powers must be a list" % position
            )
        factor_entries += len(powers)
        if factor_entries > _MAX_SPARSE_FACTOR_ENTRIES:
            raise CertificateError(
                "sparse polynomial has too many variable-power entries"
            )
        monomial = [0] * len(variables)
        last_index = -1
        for factor in powers:
            if (not isinstance(factor, list) or len(factor) != 2
                    or type(factor[0]) is not str
                    or type(factor[1]) is not int):
                raise CertificateError(
                    "sparse term %d powers must be [variable, exponent] pairs"
                    % position
                )
            name, exponent = factor
            if name not in variable_indices:
                raise CertificateError(
                    "sparse term %d names unknown variable %r"
                    % (position, name)
                )
            index = variable_indices[name]
            if index <= last_index:
                raise CertificateError(
                    "sparse term %d powers are not in ring-variable order"
                    % position
                )
            if not 0 < exponent <= _MAX_EXPONENT:
                raise CertificateError(
                    "sparse term %d exponent must be between 1 and %d"
                    % (position, _MAX_EXPONENT)
                )
            monomial[index] = exponent
            last_index = index
        monomial = tuple(monomial)
        if previous is not None and monomial >= previous:
            raise CertificateError(
                "sparse terms must be unique and in descending lexicographic "
                "order"
            )
        decoded[monomial] = coefficient
        previous = monomial
    return Polynomial(variables, characteristic, decoded, budget)


def parse_polynomial(expression, variables, characteristic=0, _budget=None):
    """Parse infix syntax or a canonical sparse polynomial object."""
    if isinstance(expression, (dict, Polynomial)):
        if not _valid_characteristic(characteristic):
            raise CertificateError(
                "characteristic must be 0 or a prime field characteristic"
            )
        variables = tuple(variables)
        if (any(type(name) is not str or not _IDENTIFIER.fullmatch(name)
                for name in variables)
                or len(set(variables)) != len(variables)):
            raise CertificateError(
                "ring variables must be unique ASCII CAS identifiers"
            )
        budget = _budget or _ArithmeticBudget()
        if isinstance(expression, Polynomial):
            if (expression.variables != variables
                    or expression.characteristic != characteristic):
                raise CertificateError("polynomials belong to different rings")
            if expression._budget is budget:
                return expression
            return Polynomial(
                variables, characteristic, expression.terms, budget
            )
        return _parse_sparse_polynomial(
            expression, variables, characteristic, budget
        )
    if type(expression) is not str or not expression.strip():
        raise CertificateError("a polynomial must be a nonempty string")
    if len(expression) > _MAX_EXPRESSION_LENGTH:
        raise CertificateError("polynomial expression is too long")
    if not _valid_characteristic(characteristic):
        raise CertificateError(
            "characteristic must be 0 or a prime field characteristic"
        )
    budget = _budget or _ArithmeticBudget()
    if (any(type(name) is not str or not _IDENTIFIER.fullmatch(name)
            for name in variables)
            or len(set(variables)) != len(tuple(variables))):
        raise CertificateError(
            "ring variables must be unique ASCII CAS identifiers"
        )
    try:
        tree = ast.parse(expression.replace("^", "**"), mode="eval")
    except (SyntaxError, RecursionError, MemoryError) as exc:
        raise CertificateError(
            "invalid polynomial syntax: %s"
            % getattr(exc, "msg", str(exc))
        )
    if sum(1 for _node in ast.walk(tree)) > _MAX_AST_NODES:
        raise CertificateError("polynomial expression is too complex")

    def visit(node):
        if isinstance(node, ast.Constant):
            if type(node.value) is not int:
                raise CertificateError("only integer literals are allowed")
            return Polynomial.scalar(
                variables, characteristic, node.value, budget
            )
        if isinstance(node, ast.Name):
            return Polynomial.variable(
                variables, characteristic, node.id, budget
            )
        if isinstance(node, ast.UnaryOp):
            value = visit(node.operand)
            if isinstance(node.op, ast.UAdd):
                return value
            if isinstance(node.op, ast.USub):
                return -value
        if isinstance(node, ast.BinOp):
            left = visit(node.left)
            right = visit(node.right)
            if isinstance(node.op, ast.Add):
                return left + right
            if isinstance(node.op, ast.Sub):
                return left - right
            if isinstance(node.op, ast.Mult):
                return left * right
            if isinstance(node.op, ast.Div):
                return left.divide_by_scalar(right)
            if isinstance(node.op, ast.Pow):
                if not isinstance(node.right, ast.Constant):
                    raise CertificateError("a polynomial exponent must be literal")
                return left ** node.right.value
        raise CertificateError(
            "unsupported polynomial syntax %s" % type(node).__name__
        )

    try:
        return visit(tree.body)
    except (RecursionError, MemoryError) as exc:
        raise CertificateError(
            "polynomial evaluation exceeded the resource budget: %s" % exc
        )


def _coefficient_text(value):
    if isinstance(value, Fraction):
        if value.denominator == 1:
            return str(value.numerator)
        return "%s/%s" % (value.numerator, value.denominator)
    return str(int(value))


def render_polynomial(polynomial):
    """Emit one parsed polynomial in an unambiguous certificate/CAS form.

    This renderer belongs to the untrusted producer boundary: it makes hostile
    CAS output inert before that output can become source text for a later
    phase.  The checker still reparses and recomputes every identity.
    """
    if not isinstance(polynomial, Polynomial):
        raise TypeError("render_polynomial expects a parsed Polynomial")
    if polynomial.is_zero:
        return "0"
    pieces = []
    for monomial in sorted(polynomial.terms, reverse=True):
        coefficient = polynomial.terms[monomial]
        factors = []
        for variable, exponent in zip(polynomial.variables, monomial):
            if exponent == 1:
                factors.append(variable)
            elif exponent:
                factors.append("%s^%d" % (variable, exponent))
        monomial_text = "*".join(factors)
        coefficient_text = _coefficient_text(coefficient)
        if monomial_text:
            term = monomial_text if coefficient_text == "1" else (
                "-%s" % monomial_text if coefficient_text == "-1" else
                "(%s)*%s" % (coefficient_text, monomial_text)
            )
        else:
            term = coefficient_text
        if pieces and not term.startswith("-"):
            pieces.append("+" + term)
        else:
            pieces.append(term)
    return "".join(pieces)

def encode_sparse_polynomial(polynomial):
    """Return the unique bounded JSON encoding of a parsed polynomial."""
    if not isinstance(polynomial, Polynomial):
        raise TypeError("encode_sparse_polynomial expects a parsed Polynomial")
    terms = []
    for monomial in sorted(polynomial.terms, reverse=True):
        terms.append({
            "coefficient": _coefficient_text(polynomial.terms[monomial]),
            "powers": [
                [name, exponent]
                for name, exponent in zip(polynomial.variables, monomial)
                if exponent
            ],
        })
    return {"schema": SPARSE_POLYNOMIAL_SCHEMA, "terms": terms}


def portable_polynomial(polynomial, prefer_sparse=False):
    """Use legacy infix for small values and sparse JSON for large values."""
    if not isinstance(polynomial, Polynomial):
        raise TypeError("portable_polynomial expects a parsed Polynomial")
    if prefer_sparse or len(polynomial.terms) > 1000:
        return encode_sparse_polynomial(polynomial)
    rendered = render_polynomial(polynomial)
    if len(rendered) > _MAX_EXPRESSION_LENGTH:
        return encode_sparse_polynomial(polynomial)
    try:
        tree = ast.parse(rendered.replace("^", "**"), mode="eval")
    except (SyntaxError, RecursionError, MemoryError):
        return encode_sparse_polynomial(polynomial)
    if sum(1 for _node in ast.walk(tree)) > _MAX_AST_NODES:
        return encode_sparse_polynomial(polynomial)
    return rendered


def canonical_polynomial_value(value, variables, characteristic=0,
                               _budget=None):
    """Normalize either accepted encoding without forcing a large infix AST."""
    polynomial = parse_polynomial(value, variables, characteristic, _budget)
    return portable_polynomial(polynomial, prefer_sparse=isinstance(value, dict))



def canonical_polynomial(expression, variables, characteristic=0,
                         _budget=None):
    """Parse then re-emit one exact polynomial; commands cannot survive."""
    return render_polynomial(parse_polynomial(
        expression, variables, characteristic, _budget
    ))


def substitute_polynomial(expression, variables, images, characteristic=0,
                          _budget=None, _preserve_sparse=False):
    """Apply one bounded, simultaneous exact-polynomial substitution.

    `images` gives the point-map image of every variable in the shared ring.
    Evaluating the parsed sparse polynomial makes simultaneity structural: a
    swapped variable is never revisited as it would be by sequential text
    replacement. The result is canonical exact-polynomial syntax.
    """
    variables = tuple(variables)
    if (not isinstance(images, dict)
            or set(images) != set(variables)):
        raise CertificateError(
            "a polynomial substitution must give exactly one image for every "
            "ring variable; got %s for %s"
            % (", ".join(sorted(images)) if isinstance(images, dict) else
               type(images).__name__, ", ".join(variables))
        )
    budget = _budget or _ArithmeticBudget()
    source = parse_polynomial(expression, variables, characteristic, budget)
    parsed_images = dict(
        (name, parse_polynomial(images[name], variables,
                                characteristic, budget))
        for name in variables
    )
    nonidentity_indices = [
        index for index, name in enumerate(variables)
        if parsed_images[name] != Polynomial.variable(
            variables, characteristic, name, budget)
    ]
    # Sparse campaign artifacts routinely carry thousands of terms while a
    # coordinate change touches only one variable. Re-expanding a polynomial
    # whose support misses every changed coordinate is not validation work;
    # it is a quadratic rendering tax. The parsed image comparison above is
    # exact, so this shortcut changes only resource use, not accepted maths.
    if not source.uses_any(nonidentity_indices):
        if _preserve_sparse:
            return portable_polynomial(
                source, prefer_sparse=isinstance(expression, dict)
            )
        return render_polynomial(source)
    answer = Polynomial.scalar(variables, characteristic, 0, budget)
    for monomial, coefficient in source.terms.items():
        term = Polynomial.scalar(
            variables, characteristic, coefficient, budget)
        for name, exponent in zip(variables, monomial):
            if exponent:
                term = term * (parsed_images[name] ** exponent)
        answer = answer + term
    if _preserve_sparse:
        return portable_polynomial(
            answer, prefer_sparse=(isinstance(expression, dict)
                                   or any(isinstance(value, dict)
                                          for value in images.values()))
        )
    return render_polynomial(answer)


def guarded_rational_substitute(expression, source_variables, target_variables,
                                images, guard, characteristic=0,
                                _budget=None):
    """Substitute numerators divided by powers of one chart guard.

    The output is a polynomial numerator and one common denominator exponent.
    Restricting every denominator to a power of the declared guard makes
    definedness local and keeps normalization finite and exact. Source and
    target rings may have different variables, unlike ordinary coordinate
    rewriting.
    """
    source_variables = tuple(source_variables)
    target_variables = tuple(target_variables)
    if not isinstance(images, dict) or set(images) != set(source_variables):
        raise CertificateError(
            "a guarded substitution must give exactly one image for every "
            "source variable"
        )
    source = parse_polynomial(
        expression, source_variables, characteristic, _ArithmeticBudget()
    )
    budget = _budget or _ArithmeticBudget()
    guard_poly = parse_polynomial(
        guard, target_variables, characteristic, budget
    )
    if guard_poly.is_zero:
        raise CertificateError("a rational-lift chart guard must be nonzero")
    parsed = {}
    for name in source_variables:
        image = images[name]
        if not isinstance(image, dict) or set(image) != {
                "numerator", "denominator_power"}:
            raise CertificateError(
                "the image of %s must contain numerator and denominator_power"
                % name
            )
        power = image["denominator_power"]
        if type(power) is not int or not 0 <= power <= 64:
            raise CertificateError(
                "the denominator power of %s must be an integer from 0 to 64"
                % name
            )
        parsed[name] = (
            parse_polynomial(
                image["numerator"], target_variables, characteristic, budget
            ),
            power,
        )

    terms = []
    common_power = 0
    for monomial, coefficient in source.terms.items():
        term = Polynomial.scalar(
            target_variables, characteristic, coefficient, budget
        )
        denominator_power = 0
        for name, exponent in zip(source_variables, monomial):
            if exponent:
                numerator, power = parsed[name]
                term = term * (numerator ** exponent)
                denominator_power += power * exponent
                if denominator_power > _MAX_EXPONENT:
                    raise CertificateError(
                        "guarded substitution denominator is too large"
                    )
        terms.append((term, denominator_power))
        common_power = max(common_power, denominator_power)

    answer = Polynomial.scalar(
        target_variables, characteristic, 0, budget
    )
    for term, denominator_power in terms:
        answer = answer + term * (guard_poly ** (
            common_power - denominator_power
        ))
    return render_polynomial(answer), common_power


def multiply_polynomial_power(expression, factor, exponent, variables,
                              characteristic=0, _budget=None):
    """Return ``expression * factor^exponent`` in canonical exact syntax."""
    if type(exponent) is not int or exponent < 0:
        raise CertificateError(
            "polynomial multiplier exponent must be nonnegative"
        )
    budget = _budget or _ArithmeticBudget()
    value = parse_polynomial(expression, variables, characteristic, budget)
    multiplier = parse_polynomial(factor, variables, characteristic, budget)
    product = value * (multiplier ** exponent)
    return portable_polynomial(
        product, prefer_sparse=isinstance(expression, dict)
    )


def check_membership_identity(target, generators, cofactors, variables,
                              characteristic=0, _budget=None):
    """Check one finite ideal-membership identity by exact expansion only.

    Search may come from Singular or another backend. This checker trusts only
    the stored equality ``target = sum(cofactor_i * generator_i)``.
    """
    if (not isinstance(generators, list)
            or not isinstance(cofactors, list)
            or len(generators) != len(cofactors)):
        raise CertificateError(
            "a membership identity needs one cofactor per generator"
        )
    budget = _budget or _ArithmeticBudget()
    wanted = parse_polynomial(target, variables, characteristic, budget)
    expanded = Polynomial.scalar(variables, characteristic, 0, budget)
    for generator, cofactor in zip(generators, cofactors):
        expanded = expanded + (
            parse_polynomial(cofactor, variables, characteristic, budget)
            * parse_polynomial(generator, variables, characteristic, budget)
        )
    difference = expanded - wanted
    if not difference.is_zero:
        raise CertificateError(
            "membership cofactors expand to the wrong polynomial: %s"
            % render_polynomial(difference)
        )
    return {
        "target": portable_polynomial(
            wanted, prefer_sparse=isinstance(target, dict)
        ),
        "generator_count": len(generators),
    }

def s_polynomial(expression_left, expression_right, variables,
                 characteristic=0, _budget=None):
    """Return the canonical pure-lex S-polynomial for producer phase two."""
    budget = _budget or _ArithmeticBudget()
    left = parse_polynomial(
        expression_left, variables, characteristic, budget
    )
    right = parse_polynomial(
        expression_right, variables, characteristic, budget
    )
    if left.is_zero or right.is_zero:
        raise CertificateError("basis polynomials must be nonzero")
    left_coefficient, left_monomial = left.leading_term()
    right_coefficient, right_monomial = right.leading_term()
    lcm = _monomial_lcm(left_monomial, right_monomial)
    left_multiplier = _term(
        variables, characteristic, _inverse(left_coefficient, characteristic),
        _monomial_quotient(lcm, left_monomial), budget
    )
    right_multiplier = _term(
        variables, characteristic,
        _inverse(right_coefficient, characteristic),
        _monomial_quotient(lcm, right_monomial), budget
    )
    return render_polynomial(left_multiplier * left - right_multiplier * right)


def standard_representation(target, basis, variables, characteristic=0,
                            _budget=None):
    """Deterministically reduce ``target`` by an ordered basis.

    The returned coefficients form a standard representation: every selected
    reducer product has leading monomial at most the current dividend's, hence
    strictly below the original S-pair lcm after leading-term cancellation.
    Generic CAS ``lift`` does not promise this stronger property.
    """
    budget = _budget or _ArithmeticBudget()
    dividend = parse_polynomial(target, variables, characteristic, budget)
    parsed_basis = [
        parse_polynomial(value, variables, characteristic, budget)
        for value in basis
    ]
    if any(value.is_zero for value in parsed_basis):
        raise CertificateError("basis polynomials must be nonzero")
    quotients = [
        Polynomial.scalar(variables, characteristic, 0, budget)
        for _value in parsed_basis
    ]
    while not dividend.is_zero:
        dividend_coefficient, dividend_monomial = dividend.leading_term()
        reduced = False
        for index, generator in enumerate(parsed_basis):
            generator_coefficient, generator_monomial = generator.leading_term()
            if any(a < b for a, b in zip(
                    dividend_monomial, generator_monomial)):
                continue
            multiplier = _term(
                variables,
                characteristic,
                _mul(
                    dividend_coefficient,
                    _inverse(generator_coefficient, characteristic),
                    characteristic,
                ),
                _monomial_quotient(dividend_monomial, generator_monomial),
                budget,
            )
            quotients[index] = quotients[index] + multiplier
            dividend = dividend - multiplier * generator
            reduced = True
            break
        if not reduced:
            raise CertificateError(
                "polynomial does not reduce to zero by the proposed basis"
            )
    return [render_polynomial(value) for value in quotients]


def retained_basis(basis, variables, eliminated, characteristic=0,
                   _budget=None):
    """Select and canonicalize the pure-lex basis elements in the subring."""
    eliminated_indices = [variables.index(value) for value in eliminated]
    answer = []
    for expression in basis:
        parsed = parse_polynomial(
            expression, variables, characteristic, _budget
        )
        if not parsed.uses_any(eliminated_indices):
            answer.append(render_polynomial(parsed))
    return answer


def _parse_vector(values, variables, characteristic, expected, field, budget):
    if not isinstance(values, list) or len(values) != expected:
        raise CertificateError(
            "%s must contain exactly %d polynomials" % (field, expected)
        )
    return [
        parse_polynomial(value, variables, characteristic, budget)
        for value in values
    ]


def _check_rows(rows, targets, generators, variables, characteristic, field,
                budget):
    if not isinstance(rows, list) or len(rows) != len(targets):
        raise CertificateError(
            "%s must have one row for each of its %d targets"
            % (field, len(targets))
        )
    parsed_rows = []
    for index, (row, target) in enumerate(zip(rows, targets)):
        coefficients = _parse_vector(
            row, variables, characteristic, len(generators),
            "%s[%d]" % (field, index), budget
        )
        expanded = Polynomial.scalar(
            variables, characteristic, 0, budget
        )
        for coefficient, generator in zip(coefficients, generators):
            expanded = expanded + coefficient * generator
        if expanded != target:
            raise CertificateError(
                "%s[%d] does not expand to its declared target"
                % (field, index)
            )
        parsed_rows.append(coefficients)
    return parsed_rows


def _monomial_lcm(left, right):
    return tuple(max(a, b) for a, b in zip(left, right))


def _monomial_quotient(numerator, denominator):
    if any(a < b for a, b in zip(numerator, denominator)):
        raise CertificateError("a leading monomial does not divide its lcm")
    return tuple(a - b for a, b in zip(numerator, denominator))


def _term(variables, characteristic, coefficient, monomial, budget):
    return Polynomial(
        variables, characteristic, {monomial: coefficient}, budget
    )


def _enforce_certificate_budget(certificate):
    """Reject oversized or cyclic proof objects before polynomial expansion."""
    stack = [certificate]
    seen = set()
    nodes = 0
    characters = 0
    while stack:
        value = stack.pop()
        nodes += 1
        if nodes > _MAX_CERTIFICATE_NODES:
            raise CertificateError("certificate exceeds the node budget")
        if isinstance(value, str):
            characters += len(value)
            if characters > _MAX_CERTIFICATE_CHARACTERS:
                raise CertificateError(
                    "certificate exceeds the text-size budget"
                )
        elif type(value) is dict:
            marker = id(value)
            if marker in seen:
                raise CertificateError("certificate contains a cycle")
            seen.add(marker)
            if any(type(key) is not str for key in value):
                raise CertificateError(
                    "certificate object keys must be strings"
                )
            stack.extend(value.keys())
            stack.extend(value.values())
        elif type(value) is list:
            marker = id(value)
            if marker in seen:
                raise CertificateError("certificate contains a cycle")
            seen.add(marker)
            stack.extend(value)
        elif value is None or type(value) in (bool, int):
            pass
        else:
            raise CertificateError(
                "certificate must contain only JSON-shaped values"
            )


def preflight_certificate(certificate):
    """Bound one JSON-shaped proof object before copying or expanding it."""
    if not isinstance(certificate, dict):
        raise CertificateError("certificate must be an object")
    _enforce_certificate_budget(certificate)
    return True


def check_elimination_certificate(certificate):
    """Validate a ``groebner_elimination_v1`` certificate.

    Success establishes the completeness inclusion ``I ∩ S ⊆ J`` through
    Buchberger's criterion and the elimination theorem.  Exact contraction
    additionally requires GP's independent no-invention check ``J ⊆ I ∩ S``.
    The checker returns a compact normalized summary and never executes a
    backend.
    """
    preflight_certificate(certificate)
    required = {
        "method", "characteristic", "ring_vars", "eliminated",
        "source_generators", "basis", "target_generators",
        "source_in_basis", "critical_pairs", "retained_in_target",
    }
    unknown = set(certificate) - required
    missing = required - set(certificate)
    if missing or unknown:
        raise CertificateError(
            "certificate fields mismatch (missing %s; unknown %s)"
            % (sorted(missing), sorted(unknown))
        )
    if certificate["method"] != "groebner_elimination_v1":
        raise CertificateError("unsupported Gröbner certificate method")
    variables = certificate["ring_vars"]
    eliminated = certificate["eliminated"]
    characteristic = certificate["characteristic"]
    if (not isinstance(variables, list) or not variables
            or any(type(v) is not str or not _IDENTIFIER.fullmatch(v)
                   for v in variables)
            or len(set(variables)) != len(variables)
            or len(variables) > _MAX_VARIABLES):
        raise CertificateError(
            "ring_vars must be nonempty unique ASCII CAS identifiers"
        )
    if (not isinstance(eliminated, list) or not eliminated
            or any(type(v) is not str for v in eliminated)
            or len(set(eliminated)) != len(eliminated)
            or any(v not in variables for v in eliminated)):
        raise CertificateError(
            "eliminated must be a nonempty unique subset of ring_vars"
        )
    # Pure lex is an elimination order only with the eliminated block first.
    if variables[:len(eliminated)] != eliminated:
        raise CertificateError(
            "groebner_elimination_v1 requires eliminated variables first "
            "in pure lexicographic order"
        )

    budget = _ArithmeticBudget()

    def polynomials(field):
        values = certificate[field]
        if (not isinstance(values, list)
                or len(values) > _MAX_GENERATORS):
            raise CertificateError("%s must be a bounded list" % field)
        return [
            parse_polynomial(value, variables, characteristic, budget)
            for value in values
        ]

    source = polynomials("source_generators")
    basis = polynomials("basis")
    target = polynomials("target_generators")
    if (not basis or len(basis) > _MAX_BASIS
            or any(item.is_zero for item in basis)):
        raise CertificateError(
            "basis must contain at most %d nonzero polynomials" % _MAX_BASIS
        )

    eliminated_indices = [variables.index(v) for v in eliminated]
    if any(item.uses_any(eliminated_indices) for item in target):
        raise CertificateError(
            "target_generators must belong to the retained-coordinate ring"
        )

    _check_rows(
        certificate["source_in_basis"], source, basis, variables,
        characteristic, "source_in_basis", budget
    )

    expected_pairs = [
        (left, right)
        for left in range(len(basis))
        for right in range(left + 1, len(basis))
    ]
    pair_rows = certificate["critical_pairs"]
    if not isinstance(pair_rows, list) or len(pair_rows) != len(expected_pairs):
        raise CertificateError(
            "critical_pairs must cover all %d unordered basis pairs"
            % len(expected_pairs)
        )
    seen = set()
    for position, row in enumerate(pair_rows):
        if not isinstance(row, dict) or set(row) != {"i", "j", "reducers"}:
            raise CertificateError(
                "critical_pairs[%d] must contain i, j, reducers" % position
            )
        if type(row["i"]) is not int or type(row["j"]) is not int:
            raise CertificateError(
                "critical_pairs[%d] indices must be integers" % position
            )
        pair = (row["i"], row["j"])
        if pair not in expected_pairs or pair in seen:
            raise CertificateError(
                "critical_pairs[%d] names an unexpected or repeated pair"
                % position
            )
        seen.add(pair)
        left_coefficient, left_monomial = basis[pair[0]].leading_term()
        right_coefficient, right_monomial = basis[pair[1]].leading_term()
        lcm = _monomial_lcm(left_monomial, right_monomial)
        left_multiplier = _term(
            variables, characteristic, _inverse(left_coefficient, characteristic),
            _monomial_quotient(lcm, left_monomial), budget
        )
        right_multiplier = _term(
            variables, characteristic,
            _inverse(right_coefficient, characteristic),
            _monomial_quotient(lcm, right_monomial), budget
        )
        s_polynomial = (
            left_multiplier * basis[pair[0]]
            - right_multiplier * basis[pair[1]]
        )
        reducers = _parse_vector(
            row["reducers"], variables, characteristic, len(basis),
            "critical_pairs[%d].reducers" % position, budget
        )
        expanded = Polynomial.scalar(
            variables, characteristic, 0, budget
        )
        for reducer, generator in zip(reducers, basis):
            product = reducer * generator
            expanded = expanded + product
            if (not product.is_zero
                    and not product.leading_term()[1] < lcm):
                raise CertificateError(
                    "critical_pairs[%d] has a reducer term not below the "
                    "pair lcm in lex order" % position
                )
        if expanded != s_polynomial:
            raise CertificateError(
                "critical_pairs[%d] does not expand to the S-polynomial"
                % position
            )
    if seen != set(expected_pairs):
        raise CertificateError("critical_pairs does not cover every basis pair")

    retained = [item for item in basis
                if not item.uses_any(eliminated_indices)]
    retained_strings = [
        value for value, item in zip(certificate["basis"], basis)
        if not item.uses_any(eliminated_indices)
    ]
    retained_only = tuple(v for v in variables if v not in set(eliminated))
    for field in ("retained_in_target",):
        rows = certificate[field]
        if not isinstance(rows, list):
            raise CertificateError("%s must be a list" % field)
        for row in rows:
            if not isinstance(row, list):
                raise CertificateError("%s rows must be lists" % field)
            for coefficient in row:
                parsed = parse_polynomial(
                    coefficient, variables, characteristic, budget
                )
                if parsed.uses_any(eliminated_indices):
                    raise CertificateError(
                        "%s uses an eliminated variable" % field
                    )
    _check_rows(
        certificate["retained_in_target"], retained, target, variables,
        characteristic, "retained_in_target", budget
    )

    return {
        "method": "groebner_elimination_v1",
        "characteristic": characteristic,
        "ring_vars": list(variables),
        "eliminated": list(eliminated),
        "retained_ring_vars": list(retained_only),
        "source_generator_count": len(source),
        "basis_count": len(basis),
        "critical_pair_count": len(expected_pairs),
        "retained_basis": retained_strings,
        "target_generator_count": len(target),
    }
