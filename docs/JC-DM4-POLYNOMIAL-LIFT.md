# JC `dm4` polynomial-lift audit

## Status

This is a proof audit, not yet graph authority. It sharpens the conjecture
suggested by the v14 coefficient campaign:

> Over `Q[y]`, any rational-function `dm4` satisfying the three source
> equations `G1`, `G2`, and `G3` with polynomial retained coordinates is itself
> a polynomial.

If the v13 finite-chart point-lift formulas base-change from `Q` to `Q(y)`,
this says an exact scalar-target point has a polynomial lift. It does **not**
say that the lift respects any declared degree cap; v14 proves that it need
not.

The arithmetic contradiction is machine-checked in
`lean/GrandPortage/JCDm4Valuation.lean`. Connecting it to Mathlib's polynomial
valuation and the v13 chart theorem remains future work.

## Equations used

Write `a=dm1`, `b=dm2`, `c=dm3`, and `q=dm4`. Only these equations are needed:

```text
G1 = (3/2)d1*a^2 + 3*d2*a*b + 3*a*q + 3*b*c = 0
G2 = -(3/2)d0*a^2 + (3/2)d2*b^2 + 3*b*q + (3/2)c^2 = 0
G3 = -3*d0*a*b - (3/2)d1*b^2 - (1/2)a^3 + 3*c*q = 0
```

All retained quantities are polynomials over a characteristic-zero field and
`q` is initially allowed to lie in the fraction field.

## Pole contradiction

Assume `q` has a pole at an irreducible polynomial. Let

```text
alpha = v(a), beta = v(b), gamma = v(c), delta = v(q).
```

For nonzero polynomials `a,b,c`, the first three valuations are nonnegative and
`delta < 0`.

In `G1`, `a*q` is strictly below the `d1*a^2` and `d2*a*b` terms. Therefore it
can cancel only with `b*c`, forcing

```text
alpha + delta = beta + gamma.                 (1)
```

In `G2`, `b*q` is strictly below `d2*b^2`. Equation (1) also makes it strictly
below `d0*a^2`. Therefore it can cancel only with `c^2`, forcing

```text
beta + delta = 2*gamma.                       (2)
```

Equations (1) and (2), nonnegativity, and `delta < 0` imply

```text
gamma + delta < alpha + beta
gamma + delta < 2*beta
gamma + delta < 3*alpha.
```

Thus `c*q` has strictly lower valuation than every other term in `G3`. It is a
unique minimum, so the sum cannot vanish. This contradicts `G3=0`.

The initial informal sketch instead claimed a final inequality
`gamma > 2*beta`. That was not the right conclusion; the unique-minimum
argument above is the corrected proof spine.

## Zero charts

The pole argument assumed `a,b,c` nonzero. The remaining cases are direct:

- If `a != 0` and `b=0` or `c=0`, `G1` solves `q` as a polynomial expression.
- If `a=0` and `b != 0`, `G1` gives `c=0`, and `G2` gives
  `q=-(1/2)d2*b`.
- If `a=b=0`, `G2` gives `c=0`; choose `q=0` when constructing a lift.

These use that the coefficient ring is a domain of characteristic zero.

## What remains before promotion

1. Pin the exact field-generality of the v13 finite-chart lift theorem and
   confirm its formulas over `Q(y)`.
2. Formalize the unique-minimum valuation lemma and the three polynomial
   equations using a genuine fraction-field valuation.
3. Check the zero charts against the complete v13 target, including the
   `Phi=0` fallback condition.
4. Keep degree bounds as a separate operation-contract obligation.

The statement does not cover truncated jets, rings with nilpotents,
positive characteristic, or arbitrary coefficient algebras.
