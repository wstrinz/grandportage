# Phase 0a — subject replay and section custody

The complete store._apply_verdict method (lines 707–1426, with surrounding context through 1435) has now been text-read. Source-specific completeness remains partial. Arithmetic replay is not uniform: the section branch validates envelope shape, exact endpoint/input binding and fixed-coordinate images but does not independently expand section row cofactors. Operation-output representation validation checks closed list fields. These must be considered alongside provenance and producer checks rather than assumed equivalent to the stronger exact-replay subjects.

Three offline section controls use a native format-8 graph, the actual provenance.current_verdict and Graph.apply, without patching freshness. The valid section of (yx-1,y²-x) into (x³-1), y→x², becomes current. Changing its first cofactor to zero while retaining its fingerprint is stale and projects nothing. Reissuing that invalid row through the producer event builder creates matching input metadata and still projects VERIFIED_SECTION. Independently calling the exact membership checker accepts the original row and rejects both altered copies.

The execution descriptor is fabricated from the frozen artifact test fixture; no Singular process, binary probe or persistent graph was used. This measures reliance on a trusted producer, not control of an authentic producer or a demonstrated live calculation defect. Under the approved replay-only 0.50 policy, fingerprints are insufficient: admission must recompute substitution and cofactor identities, with explicit ring/characteristic/partition binding. No successor implementation or exception is adopted here.

An initial harness attempt reused an unversioned test graph, and correctly received epoch-0 history-only status. It was replaced by a native graph built with the frozen meta-event constructor before measuring current evidence. This setup failure is not an oracle discrepancy.

Evidence: SECTION-REPLAY-BOUNDARY.json and tools/audit-section-replay.py, including source/script hashes and observed outcomes. Corpus validation passed; the corpus and its fixed expected verdicts remain unchanged. These diagnostic controls still need portable case extraction, along with other trusted-producer subjects. No full replay or source-test rerun claimed.

Phase 0 remains active, with campaign manifest and Lean-spike prerequisites unchanged. Source counts remain 57 partial / 311 unreviewed; reading another method is not full-file semantic completion.
