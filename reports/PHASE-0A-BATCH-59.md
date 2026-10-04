# Phase 0a — operational work ledger

Fully read work.py and test_work_accounting.py, plus the complete CLI work handler and check's work-log loading/error branch. All thirteen tests pass. WORK-LEDGER-REVIEW.json records source hashes, definition intervals and bounded evidence. No new diagnostic was needed to restate behavior already covered by those tests.

Work records are operational attempts with TIMEOUT/CAP/BUDGET reasons, not graph claims. Resolving one records a rationale and removes it from the unresolved list; it neither proves a retry succeeded nor creates mathematical authority. The graph bytes stay unchanged in the source regression. Budget values are validated finite nonnegative numbers but do not enforce execution limits.

Closed schemas, duplicate IDs, existing family references and prior unresolved targets are checked. Append checks that the family is live in the supplied graph. The exclusive work-log lock prevents concurrent work writers from passing duplicate/resolution checks together, but does not lock or refresh the graph snapshot. Do not overstate it as a transaction across graph and work files. Stale-lock recovery remains explicitly required; no recovery policy is silently selected.

Combined unresolved reporting folds each log separately, so a resolution in one file cannot discharge another file's attempt. This is distinct from the mathematical graph's proposed merge semantics and needs separate operational-policy disposition. Tests cover distinct custom graph paths, malformed logs, lock refusal, no-final-newline repair and unchanged bytes on rejected writes; they do not test process crash or concurrent graph mutation.

Unchecked accounting suppresses clean-inference claims and refuses comparison against full-check receipts in the tested paths. That is a presentation/evidence boundary, not a new proof rule. Corpus remains 352 with unchanged expectations and replay outcomes. No campaign harvest, CAS, Lean spike, oracle edits or publication. Phase 0 remains active.
