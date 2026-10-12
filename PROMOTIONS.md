# Kernel promotions

`KERNEL-PIN.json` was written at G2.5 (Lean `v4.34.0-rc2`, 22 modules). After G2.5, every change to a pinned Kernel file is logged here with its date, files, reason and re-check evidence, and the pin is rewritten in the same commit. Changes that are not logged bug fixes stop the phase (post-G2 §8).

## 2026-10-07: compiled `closure` stops at its fixpoint (post-G4 Track K)

- **File:** `phase2/lean/GP50/Closure.lean`, appended only; no existing line changed.
- **Change:** adds `roundsUntil`, `closureFast`, `rounds_stable`, `roundsUntil_rounds` and `@[csimp] closure_eq_closureFast`. `closure` keeps its definition, so every proof about it stands unchanged. Compiled code runs `closureFast`, which stops once a round adds nothing: dependency depth + 1 rounds instead of `nodes.length`. The `csimp` lemma is a kernel-checked equality, so no trust is added.
- **Reason:** GK. At 1,891 claims the closure took 73 s twice per fold.
- **Authority:** post-G4 handoff, Track K; Will approved the Kernel change and re-pin on 2026-10-07.
- **Re-check:**
  - `lake build` of the Kernel package passes (135 jobs).
  - `tools/check-kernel-axioms.py`: leanchecker replays all 22 modules with exit 0; 1,074 constants audited, no nonstandard axioms.
  - All nine Kernel test executables pass. `gp_completeness_tests` runs 13,122 finite graphs through the compiled closure.
  - The profile, binding and census rebuild.
  - The 3P (1,891 claims) and 620-claim fold outputs are byte-identical to the pre-change runner.
  - The DK V4 differentials and the gp50 suite pass.

## 2026-10-07: hash-indexed fold twins (post-G4 Track K, batch K1–K6)

- **Files:** `phase2/lean/GP50/Closure.lean`, `Events.lean`, `Runtime.lean`. Insertions only (`git diff` has no removed lines). `Events.lean` gains `import GP50.Closure`.
- **Change:** `@[csimp]` twins, each proved equal to the definition it shadows. They are `eraseDupsHash` (equal to core's `eraseDupsBy.loop`), `advance`, `canonicalIds` and `resolve` (whole `Except String Snapshot`, checks in the same order), plus `supportNodes` and `eligibleIds` (a snapshot index built once) and `projectClaims`. Definitions and theorems are unchanged; compiled code reads hash sets and maps instead of rescanning lists, which turns the fold's O(n²) scans linear.
- **Reason:** GK. These scans made the fold quadratic: at 10,000 claims, `projectClaims`, `live`, `currentFor`/`warrantFor` and `eraseDups` took about half of each fold.
- **Authority:** Will approved this Kernel batch and its re-pin on 2026-10-07.
- **Re-check:**
  - `lake build` of the Kernel package passes (135 jobs).
  - `tools/check-kernel-axioms.py`: leanchecker replays all 22 modules with exit 0; 1,190 constants audited, no nonstandard axioms.
  - All nine Kernel test executables pass.
  - The profile, binding and census rebuild.
  - The 3P and 620-claim fold outputs are byte-identical.
  - DK difftest19 (300 structures) and difftest23 (32,226 pairs) show 0 mismatches.
  - The gp50 suite passes (75 tests, 611 subtests).
  - A native benchmark of the compiled fold: `resolve` 182 ms → 4 ms and `evaluate` 150 ms → 2 ms at 2,000 claims; at 32,000 claims, 90 ms and 51 ms.
