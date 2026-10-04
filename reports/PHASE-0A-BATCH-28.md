# Phase 0a — partition open-guard omission

Read partition_exhaustiveness and the ideal-only partition_covers backend implementation, plus selected historical scope and vacuity tests. Four offline point-universe tests passed: algebraic-closure hole is refutation, base-field hole remains debt, mismatched branch universe stops before backend use, and point universe changes the fingerprint. The live cubic-hole and unit-parent tests were not run.

A distinct coverage defect is reproduced. Parent is A1 over Q with no equations. Two distinct branch models also have no equations. The closed positive control covers the parent. Adding open_conditions=[x] to each branch removes zero from both branches, so their union is D(x), not A1. Native Graph.validate accepts both setups, and the actual partition verifier returns VERIFIED for both.

The verifier asks identical backend questions in both controls: whether 1 belongs to (0), then whether two zero branch ideals cover the zero parent ideal. The bounded backend stub asserts all inputs and returns exact answers (false membership; true closed-ideal cover). It does not invent a false algebraic result. The omission occurs before that interface: branch guards are never conveyed. The explicit counterexample x=0 belongs to the parent and neither open branch.

This is stronger than the preceding synthetic-positive-verdict diagnostics: the verifier itself returns the overstrong coverage result from correct answers to its truncated question. No live Singular process or persisted verdict was used, so neither is claimed. The tests establish the missing information at the verifier/backend boundary, not full release behavior.

Proposed containment: refuse guarded branches until verification handles their constructible loci or replays a localization-aware coverage certificate. Preserve ordinary closed covers. Longer-term certificates must bind guards and all point context, not just ideal generators. Frozen source unchanged; no successor policy beyond the approved soundness/replay requirements is silently adopted.

Evidence: PARTITION-OPEN-GUARD-BOUNDARY.json, tools/audit-partition-open-guards.py and oracle-partition-scope-review.xml. Corpus validation passed. The 309-case corpus remains unchanged pending neutral extraction. Source coverage remains 57 partial / 311 unreviewed; Phase 0 active.
