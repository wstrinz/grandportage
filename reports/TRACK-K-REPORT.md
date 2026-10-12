# Track K report: fold performance (gate GK)

Builder, 2026-10-08. Authority: [post-G4 handoff §5](../docs/GP-0.50-POST-G4-HANDOFF.md). The GK decision is Will's.

## Result

Every GK criterion is met on the committed state (`e927dc2`). Measured in WSL on an idle host. Synthetic ledgers are the 3P ledger replicated with shifted keys.

| Criterion | Budget | Measured | At `3bd0bf0` |
| --- | --- | --- | --- |
| 3P full fold (1,891 claims) | ≤ 30 s | 8.2 s | 216 s |
| 3P `gp status` | ≤ 20 s | 11.4 s | 228 s |
| 10,000-claim fold | ≤ 120 s | 44.7 s | 495 s (first measured on 2026-10-07) |
| 10,000-claim `gp status` | ≤ 60 s | 51.9 s | about 360 s |
| Growth (fold, 1k / 2k / 5k / 10k / 20k) | ≲ n log n | 4.2 / 8.9 / 23.0 / 44.7 / 98.3 s | roughly n² |
| Kernel on standard axioms; leanchecker | pass | pass (22 modules, 1,190 constants) | pass |

Peak memory is linear: 0.49 GB on 3P and 4.4 GB at 20k.

## Differentials

Fold output is byte-identical to the pre-Track-K runner on the 3P ledger and the 620-claim snapshot. `gp status` output is byte-identical at every size. The DK slice matches: difftest19 shows 0 mismatches across 300 structures, and difftest23 shows 0 across 32,226 pairs. The gp50 suite passes (75 tests, 615 subtests). It includes the 3a corpus run, which reproduces its committed receipt with every case agreeing, and the 242-case global safety check (no false ACCEPT). Both run through the changed frontend and fold.

## What changed

Every change is proved equal to the code it replaces, or is a parallel map covered by `parMap_eq`. No trust is added.

**Kernel, two promotions** ([PROMOTIONS.md](../PROMOTIONS.md); Will approved both on 2026-10-07). Both use the same pattern: an `@[csimp]` twin, with the definitions and theorems unchanged.
- **`closure` stops at its fixpoint** (`closure_eq_closureFast`). The full set of rounds was cubic.
- **Hash-indexed twins** for `advance`, `canonicalIds`, `resolve`, `supportNodes`, `eligibleIds` and `projectClaims`. Each fold rescanned lists per warrant, which was quadratic.

**Profile.**
- Filing runs one guard per filing (`fileAllFast_eq`, `widenLoop_eq`) and appends each list once (`fileRawAll_eq`).
- Admission tables are built once per admission, in parallel. They read clauses, receipts and rules through key indexes (`Index.lean`: `bucket_getD`, `any_bucket`, `find?_bucket`, `nodupB_eq`; `admissionWithRules_eq` still holds).
- `held` lookups use a hash set. The refuter search uses an index (`refuter_find_eq`).
- `itemJson`, `frameChecks` and the widening pass run in parallel.
- **Elaboration.** `canonP` no longer canonicalises twice (`canonical_parse`). Surface claims elaborate in parallel (`surfaceFamily_eq`). One step, from the old inline fold to `surfaceFamilySeq`, is a code move checked with 24 error-path mutants, not a Lean proof.

**`gp.py`.** `status` and the other views cache frame results, refusals and claim lookups.

**Line limit.** `Families.lean` (834 lines, over the 750 stop) is split into `Families/{Base,Core,Extension,Surface}.lean` plus a dispatch module. All are under 300 lines. `Rules.lean` is 567 lines, over the 500 target, and was left as is.

## Where the time goes now (10,000 claims)

| Phase | Time |
| --- | --- |
| Parse, elaborate | 0.9 s, 2.4 s |
| Filing (with guard) | 4.7 s |
| Fold, ×2 (almost all certificate checks) | 10.8 s each |
| Widening (certificate re-replays at wider reach) | 7.3 s |
| `itemJson` (re-checks each receipt for display) | 8.4 s |
| `frameChecks` | 6.5 s |

The Kernel fold itself takes milliseconds: `resolve` 9 ms, `closure` 3 ms.

## Recommended next steps (not done; Will's call)

1. **P1: check each certificate once per run.** Fold 2 and `itemJson` replay the checks fold 1 already ran, about 18 s of the 45 at 10k. A validated memo is the proposal: reuse a stored result only when the stored inputs (statement, scope, certificate) equal the current ones. Correctness then does not depend on where the memo came from. The cost is a variant of `admissionWithRules` and its soundness rewrite in the binding. I held this back from an unsupervised overnight change.
2. **P3: mint theorem warrants under one guard.** Not in GK's path today, since `gp_ledger` passes no binder records, but quadratic once records exist.
3. **Ledger size.** The u(22) size is still unknown. `status` runs at about 5.2 ms per claim, so the 60 s budget allows roughly 11,500 claims. P1 would bring it to about 3.4 ms per claim, or roughly 17,000.

## Not changed

No new statement kind and no profile semantics change. The 3P ledger replays unchanged. No public action was taken.
