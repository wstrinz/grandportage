# Working instructions

Read STATUS.md, LIMITS.md, docs/GP-0.50-POST-G2-HANDOFF.md, docs/GP-0.50-POST-G2-ADDENDUM-A.md, DECISIONS.md and SPEC-CORE.md before substantive work. Addendum A (Lean-first, on the Hex substrate) wins over the post-G2 handoff where they conflict. The post-G2 handoff (2026-10-02) authorizes Phase 2.5 and Phase 3a and wins over earlier packets and handoffs where they conflict. Will's 2026-09-30 Phase 2 handoff closes G1 by an explicit coverage exception and authorizes implementation; it supersedes conflicting revision 3 text. Will ratified G2 on 2026-10-02 (all 79 kernel cases execute); Phase 3 follows the handoff's §5. Deferred Phase 2 items are listed in reports/PHASE-2-CLOSEOUT.md. Retained packets and historical reports preserve their original wording.

Use $WORKSPACE explicitly for commands. Keep practical writes, builds, downloads, caches and scratch on F:. $DEV/grand-portage and confirmed campaign sources remain read-only.

STATUS.md is the single current human status, with a top summary of at most 300 words. Standing limits live in LIMITS.md. Phase reports cap at 800 words, slice report at 500, decision entries at 150. New Phase 2 Markdown targets 10,000 words; stop at 15,000. Preserve required verbatim source records and count them conservatively.

The hash-bound layer registry covers all 459 cases; do not alter case bytes, expectations, source pins or replay history. Ambiguous layers require Will's judgment. The Mathlib-free kernel, slice, least-fixpoint completeness and soundness are implemented and proved; receipts bind tests and harness bytes, so changing an executed harness or test requires re-execution. Event-set semantics use explicit versions and targeted retractions. Will confirmed complete held closure with proved-overlap conflicts freezing release separately.

New 0.50 tests are named `tests/test_gp50_*.py` so the v0.37 suite on workspace `master` can exclude them by glob; every new tracked path also needs a `public-snapshot-v1.json` classification on `master`.

Logic/decoder/statement targets are 500/400/80 lines; stop at 750/600/120. Only standard propext, Quot.sound and Classical.choice are allowed; no sorry, native_decide or custom kernel axioms. Checker admission requires soundness arguments and adversarial controls. Receipts are default; bound Lean proofs are upgrades. Native LRAT is a candidate, not admitted.

Since 2026-10-01 GPC both coordinates and builds; the GPB Builder chat (01a0eeca-572e-7202-a708-c730d410b901) is retired. GPC writes code directly and raises genuine unknowns to Will with a recommendation. Workers remain authorized for finite code/proof/test assignments with separate outputs. Reading-only assignments need Will's approval. No new corpus cases, general predecessor audits, package adoption, further profiles or surfaces beyond why-not/earned in Phase 2.

The review shadow is https://github.com/wstrinz/grand-portage-workspace.git; use the wstrinz account, preserve predecessor branches and history, never force-push. Work lands on codex/phase-0; on 2026-10-02 Will authorized pushing it and merging it into the shadow's master, which keeps the v0.37 history (unrelated-history merge). The handoff separately authorized only the prepared freeze patch to wstrinz/grandportage. No other public action is authorized. Private verbatim harvests, source checkouts, caches and scratch remain ignored.

Heartbeats remain PAUSED; permission to use workers/heartbeats does not request restart. Do not recreate the cleared goal.
