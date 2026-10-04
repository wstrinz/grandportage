# Phase 0a — frontier bundle consistency and output custody

Fully text-read frontier_bundle.py, both retained bundle test files and the three synthetic frontier fixture files; read the complete CLI handler. Fifteen tests pass. Five targeted synthetic controls are retained with exact source pin and diagnostic script hash.

Aggregation binds receipt bytes and requires explicit agreement/supersession for every repeated semantic item. It validates scope-label equality, declared status/state, receipt membership and replacement provenance. It does not execute mathematical evidence or establish semantic equality of underlying scopes. The history fingerprint on each receipt is format-checked, not independently reconstructed. CLOSED remains a derived observation.

Reproduced gaps: duplicate open_items entries pass set equality and inflate per-receipt open_count while the aggregate count remains unique; the stable-ID regex admits a final newline; lone closed observations accept absent replacement_ids whereas explicit supersession checks replacement existence. Proposed fixes: strict list/type/uniqueness checks, fullmatch IDs and a consistent reference-existence policy. None constitutes a false theorem admission.

Actual CLI --emit-review overwrites either its own manifest or a bound receipt when that input is selected as output. Controls touch scratch files only. The mkstemp writer owns its temporary file correctly, unlike the shared PID writer, but performs no protected-input check. Proposed fix: protect all bound input identities with filesystem alias handling, and specify deliberate existing-output replacement policy. Atomic replacement does not itself protect custody.

The compact review receipt omits item observations and has a different projection schema; it should not be mistaken for a reusable frontier/v1 receipt or sufficient standalone reconstruction of the full bundle. Replacement-cycle and concurrent-read behavior remain open. Broader semantic overlap detection remains an unsettled 0.50 design question.

All 352 corpus cases and fixed expectations remain unchanged; validator passes. No frozen-code mutation, campaign harvest, live CAS, Lean work or publication. Phase 0 remains active.
