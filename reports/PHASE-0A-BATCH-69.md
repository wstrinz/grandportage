# Phase 0a — predecessor corpus intake and runner

Completed project_ir_corpus.py after the prior bounded slice; fully read corpus_check.py and its tests. Four tests and three wholly synthetic controls pass. No actual campaign directory was read or copied.

READY is a retention/shape check: manifest hashes, field paths, format-8 labels and retained verdict-event presence. The retained synthetic test itself is not a valid native graph. Loading it through the campaign runner raises GraphError before any corpus-report.json is written. This is correct native refusal but incomplete reporting. Proposed fix: distinct retention/native-load/authority statuses and per-campaign load-error records, without relaxing eligibility or backfilling source data.

A source containing export-manifest.json is copied verbatim initially, then that file is overwritten by generated export metadata. Export returns success; its validator subsequently reports SHA mismatch for the reserved file. Proposed fix: preflight reserved-name collisions before output creation, or put metadata outside the verbatim payload namespace. Preserve the new-destination and source-stability checks. Current failures can leave incomplete exports; no atomic snapshot claim is justified.

Hashes establish integrity, not authentication; no_backfill is declared metadata. Existing intake pins correctly survive detected changes. The runner combines clean transport inferences with active receipt leaves, then separately counts complete explanations; licensed_conclusions alone must not be read as earned theorem count. Recommendation remains None and does not evaluate 0.50 G0. Its three hardcoded predecessor campaigns do not define this project's approved sweep scope.

Corpus expectations and all 352 cases validate unchanged. No frozen source, adapter, live CAS, Lean work, campaign harvest or publication changed. Phase 0 remains active.
