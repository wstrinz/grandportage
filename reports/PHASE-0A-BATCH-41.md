# Phase 0a — factor-power and affine-composition review

Fully read both checker modules, both dedicated test files and both GP-owned fixtures. All 26 retained test instances pass. Per-source hashes and test names are in FACTOR-COMPOSITION-REVIEW.json; exact neutral observations are in FACTOR-COMPOSITION-BOUNDARY.json.

Ten direct controls verify ordinary factor identity, the maximum exponent, declared-variable-unit identity, valid affine composition, and refusals for exponent overflow, Boolean exponent, undeclared scalar, self-referential pivot, wrong residual and zero residual. Exponent 65 is a bounded-checker refusal, not evidence that the identity is false. The composition verifies x^2 and substitution of x=0 into x+1, but leaves both equations' same-model vanishing as an explicit obligation. It grants no emptiness authority.

The unit-monomial helper shared with product splits validates syntax and nonzero coefficients in the declared polynomial ring; it cannot establish actual invertibility in an arbitrary target. The exact countermodel 2^2=0 in Z/4Z with 2 nonzero demonstrates the need to exclude nonzero nilpotents for vanishing-power inference. The advertised domain premise is sufficient but stronger than that property. This observation neither admits characteristic four in GP nor silently changes successor semantics.

No new false mathematical acceptance was reproduced. Further work includes portable fixed-expectation extraction and complete validation/budget/dependency dispositions. Corpus remains 332 cases, latest full replay unchanged. No legacy implementation, graph record, campaign source or Lean spike changed. Coverage now 68 partial / 300 unreviewed; no fully semantic review claimed. Phase 0 active.
