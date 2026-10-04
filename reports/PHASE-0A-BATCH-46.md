# Phase 0a — exact polynomial representation boundaries

Read groebner.py lines 1–604 completely: characteristic checks, coefficients, arithmetic budgets, sparse Polynomial class, infix/sparse parsing and rendering/encoding/canonicalization. Substitution and certificate paths remain for the next slice. POLYNOMIAL-REVIEW.json records exact source hash and definition intervals; no whole-file or whole-checker review is claimed.

Five bounded controls establish precise limits. Ordinary x^2 round-trips. Infix x^100000*x evaluates exactly to x^100001; sparse encoding emits that exponent, but sparse parsing refuses it above 100000. Thus the advertised bounded encoding is not closed over every arithmetic result. This is a representation/resource mismatch, not a false mathematical identity. Proposed treatment: explicitly choose intermediate/output versus syntactic limits and enforce the declared encoding contract; do not silently raise a cap.

Direct internal construction permits a negative exponent and the native-Polynomial parse branch preserves it, while serialized sparse parsing refuses. divide_by_scalar accepts a scalar Polynomial from another ring because it extracts the coefficient without the ordinary same-ring check; ordinary cross-ring addition refuses. These are trusted-caller assumptions exposed through direct Python API calls, not demonstrated JSON/infix proof bypasses. Either validate the invariants there or enforce and document the boundary. The infix parser constructs its operands within a common ring and budget.

Equality across separately parsed same-ring polynomials succeeds while arithmetic rejects distinct budget objects. This supports representation comparison without allowing unaccounted mixed-invocation arithmetic. No generalized resource-bound proof follows from these small controls.

The coefficient TypeError remains a diagnostic robustness defect; no crash was converted to a normal corpus refusal. Corpus remains 348 with unchanged latest replay, expectations and oracle. Source totals remain 71 partial / 297 unreviewed. No CAS, campaign, graph mutation or Lean spike occurred. Phase 0 active.
