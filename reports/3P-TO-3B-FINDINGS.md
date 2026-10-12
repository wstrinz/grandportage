# 3P findings for Phase 3b

2026-10-07. The one-page note that post-G3a §6 requires before any 3b code, updated for the post-G4 handoff. Sources: [PHASE-3P-REPORT.md](../campaigns/3p-matroids/PHASE-3P-REPORT.md), [F2-REPORT.md](../campaigns/3p-matroids/F2-REPORT.md), [PHASE-4-REPORT.md](PHASE-4-REPORT.md) and DECISIONS 2026-10-05 to 2026-10-07.

## What 3P showed

- **Correctness held at volume.** 1,891 claims and 493 matroids, with no false ACCEPT and no false refusal in F2. The Kernel was unchanged throughout. 3b does not need new trust machinery for the moves 3P used.
- **A fresh agent onboarded from the docs alone.** `GP-CLI.md` plus the F0 agent's tutorial was enough for the F2 agent. 3b's surfaces should keep that bar: every new move is documented where `GP-CLI.md` documents today's.

## What changes 3b

1. **Fold cost before features.** One fold of the 3P ledger takes 272 s, and `status` takes 228 s. The time goes to commit guards (96 s), the cubic Kernel `closure` (73 s, twice), checks (26 s, twice) and reporting (20 s). A u(22) ledger would be unusable. Track K fixes this before any 3b code (gate GK).
2. **Every checker ships with its emitter path.** Coverage fell from 77% to 31% because the campaign leaned on map rules, which had no emitter. In 3b, a checker or rule without a Comparator-shaped warrant path, or a written reason why it has none, is not done.
3. **Encodings come with a Lean encoder and a frame theorem.** ENCODING-FRAME was discharged by `frame_iff`, plus a check that each filed system equals the Lean encoder's output. u(22)'s realization encodings should follow the same pattern from the start, not carry an OPEN premise into the cold read.
4. **Kinds must say what they mean in the user's words.** The agent's first confusion was NONEMPTY at p (a point over the prime field) versus NOT_IN_IDEAL(1) (geometric). 3b's ordered statements (ℝ, square classes) need the context-truth decision first (M1; post-G3a §6). Their views should print the meaning, as `MEANING` does for 3P kinds.
5. **Visible premises are cheap and worth it.** CATALOG-COMPLETE, the F1-isomorph transport and CELL-COMPLETE stayed visible without slowing the work. 3b's square-class independence (the Kummer split) can start as an OPEN premise if its checker path is not ready (post-G4 §7).
6. **Refusals that name the failing item.** The 3P surface fixes (the failing item, missing files, decimals) cut friction to zero in F2. 3b's checkers should report the failing obligation in the same shape from day one.
7. **Batch filing is the normal path.** `submit-batch` turned about 25 hours of submits into 29 minutes. 3b moves that are filed in bulk (u(22) cases) should go through it, with new source systems submitted singly first.

## What does not change

- The algebraic profile's statement kinds and the Kernel. 3b adds regimes within the post-G2 §5 design. A new statement kind or a Kernel change is a stop-and-ask.
- Builder and campaign separation: the builder never authors or edits campaign claims.
