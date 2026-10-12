# GK re-measure at u(22) shape

Builder, 2026-10-09 (measured by a worker at `87949db`). Authority: post-G4 handoff §8: "If `gp status` exceeds 60 s there, report it prominently."

## Result: GK does not hold for 3b claims on the current code

**`gp status` exceeds 60 s from about 2,000 claims.** 3a claims are unaffected. The cause is that 3b has none of Track K's fast paths yet.

| | Budget | 1k | 2k | 5k | 10k |
|---|---|---|---|---|---|
| 3b fold (`gp_ledger3`) | ≤ 120 s at 10k | 37 s | 70 s | 542 s | not run (about 2,200 s projected) |
| 3a fold (`gp_ledger`) | — | 1.2 s | 2.9 s | 8.1 s | — |
| `gp status` | ≤ 60 s at 10k | 32.6 s | **85.5 s** | **442 s** | not run |
| Peak memory | — | 1.3 GB | 2.6 GB | 6.1–6.4 GB | about 13 GB projected |

Growth is about n^2.2. 10k was not run because it would exceed the WSL memory free at the time. The host was busy (load 2–3, nice 10).

**Ledger mix.** Synthetic ledgers are copies, with vertices relabelled, of a seed campaign built through the real CLI. Per 200 claims:
- 159 candidate systems (44 variables, 61 edges plus gauge, EMPTY over ℝ): half refused, half open, every other one under an AMP premise;
- 32 held K4 exclusions in the 44-variable shape (sos, characteristic-0 ideal with `k1a`, narrowing);
- 8 small K4 claims;
- 1 held realization under KUMMER.

## Checker costs (exact certificates, all held)

- **Realize.** 22 points with 60 unit distances, exact in ℚ(√3, √11). It is filed with 60 edge equations and 171 distinctness guards, and certified by `real_point` with w = √3+√11 and m = w⁴ − 28w² + 64. Each check takes about 0.3 s, and `status` currently pays it twice.
- **Exclusion.** K4 with a pinned edge, embedded in the full 44-variable, 65-equation system: about 17 ms per four claims. The unused equations cost little.

## Where the time goes (2k run, 59 s)

| Phase | Share | Cause |
|---|---|---|
| Elaboration | 37% | each claim is parsed twice through Hex MvPoly; both copies are held in memory at once |
| Guarded filing | 24%, quadratic | the whole log is resolved on every append (Track K's single-guard filing was not ported) |
| Status reporting | 17% | every receipt is checked again; the refuter search and `held` lookups are linear scans |
| Fold checks | 14% | mostly `real_point` |

Also, Kernel narrowing deduplicates every clause key on each call. That was found by reading the code and was not timed.

## Fast-path plan (profile only; each proved equal, Track K style)

1. Single-guard filing for 3b (`fileAllFast3`). About 80 lines.
2. Parse once, in parallel (`item3With`, `parMap_eq`). About 70 lines.
3. A hash set and refuter index in `itemJson3`. About 50 lines.
4. A validated check memo for 3b receipts (`CheckMemo` pattern). About 100 lines.
5. Narrowing with keys computed once. About 30 lines.
6. Evaluate `real_point` fields once. About 60 lines.

Expected outcome:
- Items 1–4 should bring `status` at 10k to roughly 30–60 s, which is borderline.
- Peak memory, about 6.5 GB at 10k, remains a risk; a compact exponent form would be larger work.

## Reporting defects found (no soundness impact)

- A held `real_point` claim with no sign conditions gets a "no admission" diagnosis.
- A held 3a receipt shown by the 3b runner says "reach does not cover the requested scope".

Both are diagnosis text only; held/refused decisions are unaffected.
