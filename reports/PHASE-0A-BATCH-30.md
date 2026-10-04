# Phase 0a — selected-root partition context

Read point_scope, partition declaration checks and model point-universe requirements, with the selected-embedding test helpers as schema references. The partition verifier compares about, coefficient domain and point universe, but that tuple excludes selected embedding. Model validation accepts each individual selection; partition declaration does not check compatibility of those selections.

Two native graph controls use Q[x]/(x²−2), REAL_CLOSURE, with a real root isolated in (1,2) for the parent. The matched positive control selects that same root in both branches. The negative control selects the root in (−2,−1) in both branches. Both graphs validate and receive VERIFIED from partition_exhaustiveness.

The bounded backend stub checks every argument and supplies exact answers: the ideal (x²−2) is proper, and two copies of that closed ideal cover the same closed ideal. Both controls generate identical backend questions. Those answers cannot decide coverage of the selected point sets. The positive real root exists in (1,2), while neither negative branch contains it; the negative cover claim is false.

This is a loss of selected-locus information, distinct from nonvanishing guards and from fabricated producer-verdict admission. No live CAS, persistent verdict or malformed model is used. Actual model/partition validation and verifier dispatch run, with exact responses to their ideal-only queries.

Proposed repair consideration: include selected-point context in partition compatibility and coverage evidence. Unequal selections require an explicit checked relation or locus coverage argument; equal ideals alone are insufficient. Do not infer a new coordinate map from a partition declaration. Frozen code remains untouched.

Evidence: PARTITION-EMBEDDING-BOUNDARY.json and tools/audit-partition-embeddings.py with source/script hashes. Corpus validation passed; no new corpus cases or full replay claimed. The 313-case corpus remains unchanged pending minimal extraction. Phase 0 remains active; source counts stay 57 partial / 311 unreviewed and campaign/Lean prerequisites remain outstanding.
