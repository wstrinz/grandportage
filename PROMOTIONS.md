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

## 2026-10-13: Lean `v4.35.0-rc3` for Hex v0.9.0 (toolchain only)

- **Kernel files:** none. `phase2/lean/lean-toolchain` moves from `v4.34.0-rc2` to `v4.35.0-rc3`; `KERNEL-PIN.json` is rewritten with only its `toolchain` (and parent `commit`) changed. All 22 file hashes are unchanged.
- **Outside the Kernel:**
  - the `lean-toolchain` files of `profile/`, `binding/`, `census/` and `vendor/lrat-catcher/`, and `binding/environment.sh`;
  - Hex `v0.6.0` → `v0.9.0` (profile, binding) and HexGraphIso `v0.4.0` → `v0.9.0` (census); manifests regenerated with `lake update` on those packages. `HexModArith` and `HexArith` v0.9.0 join the profile as `HexMvPoly` dependencies; their C code is built by `cc`, a shim to the toolchain's own clang (DECISIONS.md, 2026-10-13);
  - Mathlib `85e3a25e` → `6b7abb3c`, the Hex v0.9.0 pin. Mathlib's transitive pins in `binding/lake-manifest.json` are set to Mathlib's own manifest (`lake update` had taken them from AutoGeneralization's). AutoGeneralization stays at `07ed6f9`, its only revision; it builds at rc3;
  - `LEAN4EXPORT_REV` in `comparator.yml` → `66f1fb4b` (tag `v4.35.0-rc3`);
  - `tests/test_gp50_profile_layout.py` expects `v0.9.0`.
- **Source changes forced by the new Mathlib** (`MvPolynomial` is now a structure-backed `AddMonoidAlgebra`; `coeff p m` replaces `coeff m p`): `binding/GPBinding/Admission/Good.lean` (three `coeff` terms), `Admission/Sound.lean` (`congrArg` on `coeff`; `coeff_zero` → `AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply`) and `Warrants/Generic.lean` (statement of `coeff_elabK`; `coeff_add` → `AddMonoidAlgebra.coeff_add, Finsupp.add_apply`). No theorem statement changes meaning.
- **LRAT-Catcher:** rc3 makes `Std.Sat.CNF.Clause` a packed structure and rewrites core's LRAT checker. Native mode is ported (`CNF.Clause.ofLiterals`); kernel mode and streaming import, which cloned the deleted checker internals, are removed. GP uses neither ([PROVENANCE.md](vendor/lrat-catcher/PROVENANCE.md)).
- **Reason:** Hex v0.9.0 and its Mathlib pin are on rc3; packet §4, R2 ([request](docs/research/PIN-PROMOTION-REQUEST-HEX09.md)).
- **Authority:** Will approved the promotion on 2026-10-13 (DECISIONS.md). The LRAT-Catcher mode removal is for Will to confirm.
- **Re-check** (scratch build, detached worktree at `7138a10`):
  - `lake build` of the Kernel package passes with unchanged sources (135 jobs).
  - `tools/check-kernel-axioms.py`: leanchecker replays all 22 modules with exit 0; 1,190 constants audited, no nonstandard axioms. `kernel-pin.py verify` passes after `write`. All twelve Kernel test executables pass.
  - The profile (328 jobs), binding (2,995) and census (2,231) build; the profile runners link the Hex FFI.
  - Fold outputs are byte-identical to the rc2 runners: 3P (1,891 claims), the 620-claim prefix, the two 3b campaign ledgers, and the 3a corpus and safety replays. The 3b corpus replay differs from the installed rc2 `gp_corpus_3b` in one refusal message only; that runner predates `ba3ff0c`, which changed the message, and `test_gp50_corpus_3b` passes. DK difftest19 (300 structures) shows 0 mismatches; difftest23 (32,226 pairs) shows 0 mismatches.
  - Binder records re-exported (`reports/PHASE-3A-BINDER.json`): the nine records are unchanged; only the environment block moves. The 3P warrant file from `gp emit-lean --all` (593 theorems) compiles under the memory guard: 5,431 s on a contended host, 6.9 GB peak.
  - The gp50 suite: 233 passed, 1 skipped (no oracle checkout), 1 failed: `test_gp50_local_paths` flags a local path in `docs/research/HEX-ADOPTION-MAP.md`, already present at `7138a10` and not touched here.
