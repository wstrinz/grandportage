# Phase 0a - hook and baseline custody

Hook full source read; reviewed boundary-test slices 334-447, 492-702 and 1024-end. Seventeen selected offline tests pass; 38 others deselected. This does not complete the boundary test file.

Baseline acceptance suppresses operational blocking only; it does not mint a mathematical warrant. Fingerprintless legacy entries are stale, despite an older save_baseline comment saying they are grandfathered.

Valid JSON arrays for baseline or hook payload raise AttributeError rather than producing a structured refusal. Graph load exceptions themselves are caught and block; baseline and payload shape errors lie outside that protection. Host handling of the uncaught process error was not tested.

Repeat suppression keys on finding IDs, not content fingerprints or full graph-error text. Two distinct malformed JSON graph errors produce different evaluate messages, but the second main call says still refused, unchanged. Exit 2 remains blocking; the defect hides changed explanation, not the block.

Initial repeat diagnostic used two different strings causing the same JSON decoder error, so its distinct-message assertion failed. Revised inputs cause distinct decoder errors and verify the intended control; no earlier failed assertion is counted as evidence.

Read-only tool names skip evaluation by design. Missing graphs pass; malformed graphs block. PostToolUse reporting occurs after the triggering action and is not rollback or pre-execution containment.

Baseline save rewrites the JSON file directly without atomic replace or concurrency locking. merge=False can intentionally replace all entries; preservation promises are scoped to default merge behavior. Broader concurrent-update behavior remains untested.

Runtime protocol routing is inferred from hook_event_name plus model key. This review verifies local legacy hook logic only, not current Codex/Claude installation or supported host protocols.

Proposed fixes: closed shape validation, content-aware repeat detection and atomic baseline writes. No installed hook configuration or frozen source changed. All 352 corpus cases validate unchanged. Phase 0 remains active.
