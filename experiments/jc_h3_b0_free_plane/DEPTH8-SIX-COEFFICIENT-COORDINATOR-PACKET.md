# JC → GP request: depth-eight free-plane boundary coefficients

**Date:** 2026-08-02

**GP reference:** `812adec` — `Verify JC b0 free-plane factor ledger`

**Native receipt consumed:** `f2_h3_b0_free_plane_receipt.json`

**Status:** Fulfilled by JC commit `033f63a`, synchronized at `fcbec5d`.
The response also supplied the transported rank-two block and its symbolic
residual compatibility.

## Request

Please produce one bounded, coefficient-only native receipt on the exact
materialized locus

```text
X_b : b = c5_7 = 0, R = 0, A = 0, OB = 0, Delta = 0
guards: c2_3 != 0, p != 0, det5 != 0
field: K = QQ[t]/(15*t^3 + 1)
```

for the depth-eight boundary triple

```text
E[2,19]
E[3,20]
E[4,22]
```

The requested payload is exactly six coefficients:

```text
coef(E[2,19]|X_b, c8_5)
coef(E[2,19]|X_b, c9_7)
coef(E[3,20]|X_b, c8_5)
coef(E[3,20]|X_b, c9_7)
coef(E[4,22]|X_b, c8_5)
coef(E[4,22]|X_b, c9_7)
```

## Required custody

For each coefficient, please retain:

- the exact sparse polynomial before restriction;
- the exact restricted polynomial on `X_b`;
- ring-variable order and coefficient domain;
- source body identity and source/body digest;
- every substitution or denominator-clearing receipt used;
- an exact zero result rather than a term-count or numerical test;
- an explicit factorization when a nonzero coefficient is divisible by `b`,
  `Delta`, `R`, or another named factor.

No full body materialization is requested if the coefficient can be extracted
and checked directly from an already-authorized source representation.

## Decision surface

This receipt should answer only:

1. Does any boundary equation genuinely constrain `c8_5` on `X_b`?
2. Does any boundary equation retain a nonzero `c9_7` coefficient after the
   landed `c9_7 <-> c9_7+(3/2)*c2_3*c7_4` normalization, thereby turning the
   pivot-absorbed `c7_4` direction into a compatibility direction?

Every outcome is useful, including all six coefficients being zero.

## Mandatory refusals

The receipt must not claim or infer:

- that a coefficient is a unit without a declared guard and unit witness;
- that `b`, `Delta`, `R`, or `R+c3_5*b` is invertible or a nonzerodivisor;
- that the row-one depth-eight rung solving `c9_6` is a compatibility equation;
- a free-plane component, irreducibility, or exhaustive component coverage;
- an all-orders lift or nonlinear nonextension;
- actual-source sufficiency or membership;
- H8, H3, or a `(75,125)` verdict change.

If the authority-bearing source object for any coefficient is not currently
materialized, return `AUTHORITY_OBJECT_MISSING` for that coefficient and name
the smallest missing source receipt. Do not fit, infer, or reconstruct the
coefficient from another chart.

## GP handback

Please return:

- the native checker;
- its frozen JSON certificate;
- a short human-readable note;
- the commit containing all three;
- the exact pass count and command used.

GP will ingest the result through `exceptional_factor_column_v1`, independently
replay the exact arithmetic, mutation-test scope widening, and retain graph
effect `NONE` unless a separately modeled operation contract earns something
stronger.
