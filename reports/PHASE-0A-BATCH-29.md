# Phase 0a — portable open-guard partition cases

GP-X269–272 encode four exact rational one-variable loci: closed branches covering A1; two D(x) branches incorrectly claimed to cover A1; D(x) branches covering a D(x) parent; and one D(x) branch plus one unrestricted branch covering A1. The latter two are positive controls against a future indiscriminate rejection of all open covers.

The adapter reads neutral equations and nonzero conditions, constructs a native graph and calls the actual partition verifier. Its bounded backend accepts only zero-ideal questions and returns exact algebraic answers. It does not inspect expected verdicts or manufacture a false algebraic result. Returned origin membership makes the GP-X270 counterexample explicit: zero belongs to the parent and neither branch.

GP-X270 stays expected REFUSE, observed ACCEPT, classified partition_branch_open_guards_omitted. This is verifier loss of locus information, distinct from the synthetic producer-trust diagnostics. No live Singular process or persisted verdict is claimed. Proposed fixes remain documented in Batch 28; frozen code unchanged.

Full replay: 313 cases, 300 agreements, ten known differences, one diagnostic observation, one pending and one unsupported. Expected counts 92 ACCEPT / 221 REFUSE. No ERROR or REVIEW_REQUIRED. All 309 prior case files are byte-identical and runner/route/adapter/case hashes match the final artifact.

Replay: oracle-runs/20260928T134033509436Z.json. Phase 0 active; source coverage remains 57 partial / 311 unreviewed. Campaign manifest and later Lean prerequisites remain outstanding.
