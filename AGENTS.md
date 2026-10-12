# Working instructions

## Read first
Before substantive work, read:
- `STATUS.md`, the single current human status (top summary ≤ 300 words);
- `docs/HANDOFF-2026-10-11.md`, the current state of every track and where to start;
- `DECISIONS.md`, the binding rulings, newest last, and `DECISIONS-PRIVATE.md`, the campaign-sensitive entries withheld from public releases;
- `LIMITS.md` and `SPEC-CORE.md`.

**Authority, newest wins where they conflict:**
1. Will's decisions in `DECISIONS.md`.
2. `docs/GP-0.50-FIXED-ROPES-HANDOFF.md` (ropes are the deliverable; GP is the belay) and `docs/ROPE-CHECKLIST.md`.
3. Campaign packets in `docs/` (withheld from public releases until their gates and outreach).
4. `docs/GP-0.50-POST-G4-HANDOFF.md`.
5. The post-G3a and post-G2 handoffs and Addendum A.

Retained packets and historical reports keep their original wording.

## Roles
- **Builder.** Owns GP code: `tools/gp.py`, `profile/`, `binding/`, `census/`, `phase2/`, the emitters and CI. Writes code directly and raises genuine unknowns to Will with a recommendation. Workers may take finite code, proof or test assignments in their own worktrees and hand back patches. The builder integrates them.
- **Campaign agents.** Use GP; never modify it. Each writes only in its campaign directory (`campaigns/<id>/`) and its rope directory (`ropes/<id>/`).
- **Independent reviewers.** Read-only, unless Will hands them a bounded implementation, as with the frontier fix. Their patches are integrated by the builder.

## Repository and custody
- **The workspace** (`wstrinz/grand-portage-workspace`) is **PRIVATE** as of 2026-10-10. Work lands directly on `master`; former branches are `archive/*` tags. Never force-push; pull with `--rebase` if a push is rejected. `wstrinz/grandportage` is public: nothing goes there, and nothing is sent to anyone outside, without Will's explicit OK.
- **Outreach** is drafted by agents and sent only by Will.
- **New tracked paths** need a classification in `public-snapshot-v2.json` (the test reads v2), and should be mirrored in v1. Campaign directories are private until their gates.
- **Kernel and corpus.** The Mathlib-free Kernel is pinned by `KERNEL-PIN.json`; changes go only through PROMOTIONS with Will's approval. Do not alter corpus case bytes, expectations, source pins or replay history. Receipts bind test and harness bytes, so changing an executed harness requires re-execution.

## Engineering rules
- **Proofs.** Only `propext`, `Quot.sound` and `Classical.choice`. No `sorry`, `native_decide`, `Lean.ofReduceBool` or custom axioms. Never run `decide +kernel` over Hex-based checkers: kernel replay has wedged this machine. Kernel-checked data uses small plain-list checkers in memory-capped shards.
- **Speedups.** Profile speedups must be proved equal to the code they replace (`@[csimp]` or `_eq`), with byte-identical outputs. There is no cross-run result cache: every fold replays every receipt.
- **Checker admission** needs a soundness proof and adversarial controls. A negative control must show its expected refusal reason.
- **Line endings.** The tree is `* -text`: keep each file's line endings, and count CR bytes with Python, not Git-Bash grep.
- **Size limits.** Lean files target 500 lines, stop at 750. Phase reports ≤ 800 words, rope READMEs ≤ 600, decision entries ≤ 150.
- **Host.**
  - Keep writes, builds and caches on F: (WSL Lean builds may use WSL's own disk).
  - Run heavy jobs at BelowNormal priority, one Lean build at a time.
  - Run WSL commands via script files with `MSYS_NO_PATHCONV=1`.
  - Before removing a worktree, delete its `.lake/packages` junctions with `cmd /c rmdir` only.
  - Never permanently delete user data; hand Will the command.
- **Tests.** New 0.50 tests are named `tests/test_gp50_*.py`. CI (`.github/workflows/ci.yml`, plus the Comparator and rope workflows) runs only on dispatch.

Heartbeats remain PAUSED. Do not recreate the cleared goal.
