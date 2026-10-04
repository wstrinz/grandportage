# Phase 0a partial-mapping adjudication

Reassessed exactly 22 former partial rows against the pinned historical tests, including parameterized mutation premises, and the existing neutral corpus.

| Disposition | Count |
|---|---:|
| covered | 20 |
| partially_covered | 1 |
| unresolved | 1 |

Genuinely unmatched mechanisms:
- `test_zeroing_depth13_endpoint_refuses_minimal_shift_claim`: A neutral refusal case for a purported minimal shift whose claimed last nonzero endpoint has been zeroed. X118 is positive, so it cannot by itself cover this mutation refusal.
- `test_explicit_residual_pullback_and_finite_unit_replay`: Replay of a unit witness specifically in a finite quotient algebra (as distinct from the existing localized ideal-unit replay).

The JSON supplies per-row assertions, case-level equivalence, incidental differences, and source pointers. No prior review, corpus expectation, adapter, or oracle file was modified.
