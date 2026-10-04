# Phase 0a — exact simple number-field witnesses

Fully read number_field.py and test_number_field_witness.py; read the point_witness extension branch with surrounding preflight and the native store replay branch. Nine offline tests pass, including exact quadratic conjugates, wrong coordinates, invalid field/denominator refusal, ordered-scope refusal, native recording and reissued receipt tampering. One live Singular identity test was deliberately excluded.

Four additional controls accept a root of a^3-2 and the inverse coordinate satisfying 2*x^3-1, refute a guard vanishing at that root, and refuse reducible a^3-a as a field declaration. No CAS required.

Soundness: for degree two or three over Q, reducibility is equivalent to a rational root. Exhaustive rational-root testing within the admitted bounds establishes irreducibility. The quotient is a field; extended Euclid verifies denominator invertibility, and exact polynomial reduction checks equations and nonzero guards. An embedding into an algebraic closure gives the claimed point. This relies on exact parser/arithmetic correctness and proper model binding; it does not certify a rational point or chosen ordered embedding. The store recomputes the witness and compares the entire receipt and verdict rather than trusting a producer-positive flag.

Degree/root-search/exponent limits are conservative support boundaries, not proofs of nonexistence. They are not a global bit-size or memory budget for all arithmetic. Further malformed-input, caller-precondition and resource controls remain open, as does portable extraction of any cases not already represented. No checker is newly admitted by this review.

All 352 corpus cases validate unchanged. No frozen-source edits, live CAS, campaign harvest, Lean work or publication. Phase 0 remains active.
