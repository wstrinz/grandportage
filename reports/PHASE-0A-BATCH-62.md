# Phase 0a — release and publication consumers

Fully text-read release.py, publication.py, both test modules, both design documents and the synthetic release manifest. Complete CLI release/publication handlers also read. Twenty tests pass, including actual execution of archived synthetic checkers; materialization tests mock clean Git identity and do not establish real checkout freshness.

Release planning adds unconditional clean-source and canonical-source coverage checks to dossier profile evaluation. Selected bytes and resource digests are audited; lane commands must match declared replay commands, receipts must name typed resources, and unreferenced/colliding resources refuse. This checks packaging consistency, not replay execution. NOT_APPLICABLE is an explicit replay-debt exception, not evidence of a theorem. Publication preserves declared grades and labels itself editorial.

Generated artifacts satisfy only matching missing PUBLICATION presence contracts. Replay-kit readiness intentionally permits missing publication deliverables while preserving selected payload/resource checks. Existing tests distinguish these paths and recheck changed source/resource bytes before materialization.

Correction: Batch 61 called the source-directory synthetic verifier failure a packaging defect. The release manifest deliberately relocates it into replay/ alongside authority/ and receipts/. Both full-release and replay-kit tests execute it successfully. Withdraw the proposed path rewrite, which would damage the intended layout. Preserve raw source-directory failure and the independent CRLF digest inconsistency. The correction is explicit in the dossier manifest and Batch 61 report.

Remaining review questions: the materializer trusts a mutable evaluated plan/readiness flag without recomputing its fingerprint; the CLI builds that plan directly, so no external bypass is established. Hash checks precede copyfile and are not a source snapshot or post-copy verification. Adversarial direct-API and concurrent-source controls remain open. Shared output-writer claims need complete caller/dependency review. Historical companion paragraphs were read as source statements, not verified campaign facts.

All 352 corpus cases and fixed expectations remain unchanged; validator passes. No frozen-source changes, live CAS, campaign harvest, Lean work or publication. Phase 0 remains active.
