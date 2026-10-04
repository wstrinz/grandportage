# Phase 0a deleted dm4 polynomial-lift quantifier extraction

The deleted audit states a universal claim: every rational `q=dm4` satisfying its displayed G1-G3 equations with polynomial retained coordinates is polynomial. Its own zero-chart paragraph instead chooses `q=0` to construct a polynomial solution when `a=b=0`. Those quantifiers differ.

Set `a=b=c=d0=d1=d2=0` over `Q[y]`. Every term in G1-G3 then vanishes independently of `q`. Exact local reference arithmetic gives:

| Case | Choice of `q` in `Q(y)` | G1/G2/G3 residuals | Reduced denominator | Observation |
| --- | --- | --- | --- | --- |
| GP-X341 | `1/y` | `0/0/0` | `y` | `REFUSE` universal polynomiality |
| GP-X342 | `0` | `0/0/0` | `1` | `ACCEPT` polynomial solution for these equations |

The second row supplies existence for the **same retained zero chart**. It does not make the arbitrary rational solution in the first row polynomial. The negative result addresses the literal opening statement only; it does not refute a separate existential polynomial-lift claim.

## Source, reuse, and authority

The full deleted `docs/JC-DM4-POLYNOMIAL-LIFT.md` blob `36e9e90cecee7209ef1098ca8f79118c02381bb6` was read from the predecessor read-only repository. The universal sentence is at lines 8-10, G1-G3 at 23-32, and the zero-chart choice at 74-83. The deleted-document review records the same source and its SHA-256. The retained `JCDm4Valuation.lean` proves a conditional integer inequality spine under supplied nonzero-chart balances and leaves genuine valuations and zero charts for future work. This counterexample does not test that theorem.

GP-A22 concerns a degree cap for a forced polynomial `dm4`; GP-X25 and GP-X26 are bounded polynomial witnesses. None tests an arbitrary rational solution on the zero chart. The two new cases use local SymPy 1.14.0 exact arithmetic as a reference layer. They record `native_rational_lift_verdict: null`, `full_v13_target_checked: false`, and `nonzero_chart_valuation_theorem_tested: false`. The positive case makes no full target or `Phi=0` fallback assertion.

## Replay and preservation

The immutable baseline had 381 cases. The new immutable run has 383: **368 AGREES, 12 KNOWN_DIFFERENCE, 1 DIAGNOSTIC_OBSERVED, 1 PENDING, 1 UNSUPPORTED**. Both new cases agree. All 381 prior case SHA-256 values, expected and observed verdicts, statuses, layers, and routes are unchanged. GP-X236 and GP-X237 differ only in regenerated completion markers in their reason strings; normalized reasons match.

- Baseline: `reports/oracle-runs/20260928T220044757918Z.json`.
- New run: `reports/oracle-runs/20260928T224802105393Z.json`.
- Machine-readable observations and file hashes: `reports/PHASE-0A-DM4-POLYNOMIAL-LIFT-EVIDENCE.json`.
