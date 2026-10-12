# Release plan: Grand Portage v0.50.0 (stable)

Adopted 2026-10-12 (Will; DECISIONS "v0.50.0 stable scope"). The base is master after `v0.50.0-alpha.2` (public `aaa0727`).

**Goal:** a credible stable 0.50 that others can apply to their own problems. Every sentence GP prints must be no stronger than what the Kernel established. The documentation states exactly what is guaranteed, under which assumptions.

**Ownership:** Will moved every item to the builder (Claude, GPC) on 2026-10-12, working with workers.

**Status, 2026-10-12: every item is done.** A1/A3 `dc5288f`, A2 `45ce867`, B1–B6 `e0f520c`, C1/C2 `c97a40f` and `67e56f6`, D2 `2b80dfb`, D1 `eb22adb` (57 of 62 EMPTY claims; 5 refused by size). Additions beyond the plan: a CI axiom audit (`48ef999`) and CLI hardening (`665d842`). **Published 2026-10-12** as `v0.50.0` ([receipt](../reports/STABLE-PUBLICATION.json)).

## A. Claim authority (builder; must)

| # | Item | Acceptance |
|---|---|---|
| A1 | **Campaign statement binding.** Each command verifies that `campaign.json`'s SHA-256 equals the one bound at `init`. A deliberate change is an explicit `gp restate` event: a versioned ledger record carrying the old and new hashes. | An edited statement is refused with a clear message, and `restate` makes it current. Tests cover: edit then refuse; restate then accept; a merge across a restate. |
| A2 | **Kernel-held goal statement.** The DECIDE goal becomes a profile statement kind, with admitted *realize* and *spine* rules proved sound in the binding (from `realize_sound`, `spine_sound`, `udg_frame_iff`). The cover becomes a held, premise-carrying claim. **A design note comes first, for Will's review.** | `status` and `frontier` read the goal verdict from the fold. The Python join leaves `TCB.md`. Every existing goal test and control still passes, plus new ones: a wrong graph, wrong (n, m), a tampered frame, and a cover without a completeness warrant. |
| A3 | **Content-hash freshness.** A runner is fresh only if a stamp recording its source-tree hash and toolchain identity matches the current tree. | A source edit with an older modification time is detected; a touched but unchanged file is not. |

## B. Honest documentation (Codex; must)

| # | Item | Acceptance |
|---|---|---|
| B1 | **`GUARANTEES.md`**, the front page of what 0.50 guarantees: Kernel soundness and completeness; profile soundness against Mathlib; what "held" means; the TCB on one screen; what is *not* claimed. That includes "no published result independently re-established outright", unless that becomes untrue. Linked from README. | ≤ 800 words. Every guarantee cites a theorem name or a test. |
| B2 | **`LIMITS.md` brought current.** Predecessor-era text ("test stub", "workspace public") moves to `HISTORY/`. | No stale statements; a reviewer can read it as current. |
| B3 | **`TCB.md`:** a current one-page summary at the top, with the historical sections kept below a clear divider. | The summary matches the code after A2. |
| B4 | **Coverage by kind of conclusion** in the Track E report and README: positive/point, map, bridge, EMPTY/negative, each with the trust boundary it crosses. | The 62 deferred EMPTY claims are a visible row, not averaged in. |
| B5 | **Manifests stop naming withheld paths.** The snapshot classifier lets the longest matching prefix win, so the manifest can say "campaigns/ except the public ones" without naming private directories. | Snapshot tests pass. The public manifest contains no withheld campaign or packet names. |
| B6 | **Reproduction instructions pinned to the release commit and tag,** not "the tag plus a later fix". | README, the release notes and REVIEW all name the same commit. |

## C. Outside usability (Codex; must)

| # | Item | Acceptance |
|---|---|---|
| C1 | **`docs/USING-GP.md`:** install (elan, Python), build the runners, start a campaign in any directory, then the full loop: claim, submit, status, frontier, explain, receipts, merge, emit. Also how to build a rope from `ROPE-CHECKLIST.md`. One small worked example, end to end. | A fresh agent, given only USING-GP.md, completes the example. Record the time and every gap. |
| C2 | **Stability promise.** `gp --version`, recorded in the `init` record (done by the builder, `c97a40f`). A written compatibility statement for `gp-ledger/v1`: what may change, and how old ledgers keep folding. A test runs a campaign in a temp directory outside the repo. | The tests pass, and the statement sits in USING-GP.md. |

## D. Evidence quality (Codex; should)

| # | Item | Acceptance |
|---|---|---|
| D1 | **One EMPTY 3P exclusion as a Comparator challenge in Mathlib vocabulary** ("no field of characteristic p realizes M"). It needs frame normalization: every realization moves to the framed one. | Stock Comparator accepts; the controls (sorry, weakened, redefined) are refused with their expected reasons. The emitter's EMPTY class covers at least this claim. |
| D2 | **Public exact gadget embeddings in R1a.** Existence witnesses for each of the six TU gadgets, exact in ℚ(√3), as Lean theorems. Then the fidelity note's non-vacuity no longer rests on private records. | Comparator accepts; FIDELITY and README are updated; `REPRODUCE` passes. |

## Release gate
1. A, B and C are done; D1 and D2 are done, or explicitly deferred by Will.
2. Workspace CI is green; then audit the public snapshot (same procedure as alpha.2). The public CI is green on the tagged commit itself.
3. Will signs off. Tag `v0.50.0`, publish, and write the receipt.

## After stable
The first external applications, run as matched direct-vs-GP assays, measure valid work preserved and repair cost, not refusals:
1. **Larson's rank-9 exchange cut.** The baseline is the reviewer's exact reproduction: 2,784 states, components of 864 and 1,920.
2. **The hyperbolicity determinant-factor transport:** factorization alone must not license full cone equality.

## For the Codex pool: start here

Read `AGENTS.md`, this plan and `docs/private/HANDOFF-2026-10-11.md`.

**Take B1–B6, C1, C2 (docs and the outside-the-repo test), D1 and D2.**

**Coordinate on these files:**
- **`tools/gp.py`, `profile/GPProfile/Real/` and `binding/GPBinding/UDG/`** are being changed by the builder for A2. Avoid them, or send a patch to the builder.
- **D1** lives in `tools/comparator-emit.py`, the prelude and the binding's Matroid frame lemmas.
- **D2** lives in `ropes/r1a/`.

**Campaign step:** a campaign whose `campaign.json` was edited after `init` refuses every command until its owner records the change with `gp restate --reason ...` (A1).
