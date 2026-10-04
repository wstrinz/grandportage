# Phase 0a — diagnostic IR projection and state identity

Fully read project_v2.py, test_project_v2.py and IRChecks.lean. Read project_ir_corpus.py lines 1–140 only, including complete pinned-fixture discovery, wrappers and run path. Five focused tests pass; the separately executed repository fixture corpus test also passes. It reads GP-owned fixtures only, disables native binary rechecks and retains historical-load limitations. No campaign sweep or Lean compile occurred.

Four controls verify expression and state boundaries. A real offline SOS receipt is recorded; removing loaded authority_receipts makes its binding noncurrent but preserves state_fingerprint because that map is absent from the snapshot. This is a direct loaded-state mutation diagnostic, not a persisted event or cryptographic collision. Proposed fix: distinguish structural content identity from evaluated observation identity, or include all consulted authority state.

Expression conversion rejects characteristic-zero rational coefficients as a named gap, maps 1/2 to 2 in characteristic three, and distinguishes x^3 from x as polynomials. Characteristic must remain attached to interpreted expressions. Unary constructor cost is bounded at 128; adapter refusal does not establish false mathematics. Parser normalization is trusted Python work, not a verified Lean codec.

PROJECTABLE is expressly a diagnostic skeleton. Predicate candidates retain condition fingerprints rather than interpreted proofs; steps retain unknown discharge and unprojected justification; every receipt retains an actual requirement-discharge gap. Lean dictionary and callable-gate checks establish synchronization only. The full private campaign corpus/intake path remains to be reviewed, and no external sources were read.

All 352 cases and fixed expectations validate unchanged. No frozen source, replay adapter, live CAS, Lean implementation or publication changed. Phase 0 remains active.
