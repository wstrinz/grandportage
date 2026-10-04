# Phase 0a - formal interpreter and composition review

Six complete source files read and hashed.

Derivation is an explicit restricted equational calculus. Induction establishes eval equality under precisely its Laws; it is not a normalizer or a complete commutative-ring calculus. Rational constants, divisions and parser correctness remain outside Expr.

Ordered certificate interpretation uses derivation_sound, vanishing of each paired generator/cofactor term and the Atlas ordered contradiction lemma. The supplied integer instance discharges Laws/Ordering. Gaussian evaluation exhibits a root and the same equality while refuting Ordering; it is not a formalization of the complex field.

OperationMap explicitly preserves zero, one, add, multiply and negation. Syntax induction proves eval_map without injectivity, order or ring laws; roots travel forward and emptiness pulls backward. Integer-to-Gaussian transport supplies a concrete counterexample to forward emptiness from operation preservation alone.

Cancellation derives c*g=0 from the derivation/equation and uses no-zero-divisors plus c nonzero to infer g=0. The Fin4 witness c=g=2 retains the other premises and refutes cancellation. Fin2, the zero algebra and a product of integers establish distinct profile separations. Ordering here is an SOS nonnegative cone, not a total ordered-domain interface.

The catalog links reviewed in Batch 81 have the expected bounded interpretation: unit nontriviality, SOS ordering and cancellation no-zero-divisors each have a retained deletion countermodel. This source review does not certify an automatic dictionary or formally check the current build.

InterpreterParity serializes expressions from the actual sample, while its Python comparator replays candidate and fixture with the same exact SOS verifier and compares receipts. It binds one example; it does not prove the renderer, decoder or normalizer correct for arbitrary expressions.

Seven offline tests pass with native SOS verification, persisted verdicts and graph reload. They cover declaration versus replay, ordered reach across a two-step prefix, refusal at C/F2, structural refusal for changed point universes, false cofactors, stale input and a different valid square rejected by sample comparison. No Singular or Lean executable was invoked.

Formal source arguments remain distinct from a fresh Lean build and the deferred 0.50 spike. No source, expectation, adapter, campaign harvest or publication changed. All 352 corpus cases validate unchanged. Phase 0 remains active.
