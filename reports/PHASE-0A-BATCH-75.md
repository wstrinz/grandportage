# Phase 0a - CAS operation and candidate-certificate boundaries

Read cas.py lines 1286 through end and output block parser lines 691-734. Three bounded injected-runner controls verify one positive certificate and exact rejection of two malformed-transcript candidates. No live CAS or graph recording was attempted.

Membership and unit-ideal producers first ask for reduction/basis, then request lift only on a positive answer. Their attached certificates are candidates: no local arithmetic replay is performed in these producer functions.

Three injected transcript controls verify a valid membership certificate and two malformed matrices. Missing first row is padded with zero; duplicate first row uses its first value. Both malformed cases return is_member true and attach a false candidate identity; the independent exact checker rejects both. Test backends cannot record verdicts. No native bypass or actual Singular defect is claimed.

The older cofactor expansion helpers still execute Singular for arithmetic; avoiding Buchberger does not by itself remove the backend from their trusted computation. Consumers with native exact replay have a stronger boundary.

Membership canonicalizes sparse/infix polynomials before emitting CAS text; several older unit/witness/substitution helpers construct text directly under CASProgram validation. Shared total arithmetic budgets and one overall deadline are not established across these multi-call routines.

Ideal generator and decomposition parsers remain permissive about row labels. Decomposition rejects missing/empty components but its output is not an independently checked cover proof. The docstring claim that it carries its own exhaustiveness proof overstates the returned data.

Partition coverage implements radical containment using branch-ideal intersection and Rabinowitsch unit tests. The algebraic-closure argument is sound conditional on correct backend results and appropriate branch/model hypotheses, but yields no replayable intersection or radical certificates. It also omits open guards and selected embeddings, as already demonstrated in Batches 28-31.

classify_identity tests equality in the coordinate ring, not merely pointwise vanishing on the reduced locus. Witness evaluation demands constant complete coordinates but its statement that no field subtlety exists is too broad; field and embedding handling live in higher-level verification.

non_integral_denominators and foreign_symbols are syntactic reporting helpers, not complete definedness or coefficient-domain proofs. Their comments explicitly limit their role.

Proposed fixes: strict indexed matrix parsing, explicit candidate status until exact replay, and accurate documentation of backend-dependent coverage evidence. No frozen source or expected verdict changed. All 352 corpus cases validate; coverage remains 135 partial / 233 unreviewed. Phase 0 remains active.
