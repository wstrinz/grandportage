# Phase 3P, stage F2: simple rank-3 matroids on 3 to 9 elements

2026-10-06, branch `campaign/3p-f2`. Will authorized n = 9 after n ≤ 8.

**Catalog premise.** `catalog/generate.py` is **trusted**, and **catalog completeness is OPEN** (`CATALOG-COMPLETE`). Everything below is modulo that premise. Nothing here is a COUNT claim.

## Catalog

- **Counts for n = 3…9:** 1, 2, 4, 9, 23, 68, 383. They match Table 2 (rank 3) of Mayhew–Royle, *Matroids with nine elements* (arXiv:math/0702316).
- **Cross-check:** `catalog/check.py` passes for every n, including 50,166,353 labelled matroids at n = 9. It is not a proof: a direct labelled count equals Σ n!/|Aut|.
- **F1 isomorphs:**
  - C6-01 ≅ U36, C6-09 ≅ MK4;
  - C7-22 ≅ F7⁻, C7-23 ≅ F7;
  - C8-68 ≅ AG23-e;
  - C9-355 ≅ NonPappus, C9-368 ≅ Pappus, C9-383 ≅ AG23.

  They reuse their F1 claims; `check.py` verifies the maps.

## Held

**All 482 other entries have χ(M) fully held in `gp status`.** The table is `catalog/chi-table.md`.

| χ(M) | n ≤ 8 | n = 9 |
|---|---|---|
| every characteristic | 96 | 331 |
| all except 2 | 4 | 33 |
| all except 3 | – | 2 |
| all except {2, 3} | – | 2 |
| {2} | 2 | 8 |
| {3} | – | 1 |
| ∅ | – | 3 |

- **Routes.** Most entries use a ℚ point, then points over F_q at its bad primes. Exceptional primes use EMPTY mod p (Singular). Seven n = 9 entries are realizable in characteristic 0 only over ℚ(ω), ℚ(i) or ℚ(φ), by a map from a held source system.
- **Consistency.**
  - Every row satisfies Rado–Vámos.
  - Restriction monotonicity, χ(M) ⊆ χ(M∖e), holds on all 4,228 single-deletion pairs.
  - Most "except 2" rows contain F7⁻, most {2} rows contain F7, and the "except 3" and {3} rows contain AG(2,3)∖e.
- **No suspected false ACCEPT.**
- **ENCODING-FRAME** is discharged on every held matroid claim.

## Open items

- **`CATALOG-COMPLETE`** and the isomorphism transport are *closable in principle*.
- **The counts** are cited to Mayhew–Royle, Table 2 (rank 3); the F1 Oxley citations remain `[VERIFY]`.

## Cost

- **Ledger:** 1,891 claims in all; F2 added 1,847, including 4 new source systems.
- **n ≤ 8:** 11.7 h of single submits, before the builder's fixes.
- **n = 9:**
  - search: 2.6 h, on 6 BelowNormal workers;
  - Singular: about 25 min;
  - filing: about 2 h single, then 1,249 items in 9 batches taking 29 min.
- **Tokens:** unavailable.
- **One machine reset.** Ten normal-priority workers froze the box. Nothing was lost, and the restart used 6 BelowNormal workers.

## Friction

- **Refusals: 0** in all of F2.
- **One logged item, ergonomic: fold cost.** It was 500 s per submit before the fold speedup. After it, cost was linear per submit. After `submit-batch`, a fold of about 110–260 s covers 250 items.

## `emit-lean` coverage

F2: 563 of 1,847 (30%); whole ledger: 593 of 1,887. The 1,284 uncovered F2 claims are 1,241 map-rule claims and 43 mod-p ideal certificates. It is not compiled; the gaps are listed in `warrants/coverage-all.txt`.

---

*Builder note, 2026-10-07 (post-G4 handoff §3; appended by the builder, not campaign text):*

- **Custody share for the F2 window**, from the F2 handoff (`16f98d7`) to the replay record (`4374a68`): 0 of 4 builder commits were custody-only (0%). 2 were governance (the handoff and the replay record), and 2 were work (the fold fixes). Rule (agreed 2026-10-07; `tools/custody-share.py`): the builder's non-merge commits only, campaign-agent commits excluded. A commit is custody-only when every path it changes is CI, a snapshot or publication manifest, a pin or a custody receipt. It is governance when every path is a record (decisions, status, TCB, docs, reports) or custody. Anything touching code, proofs, tests or tools is work.
- **Catalog counts:** 1, 2, 4, 9, 23, 68 and 383 for n = 3…9 match Table 2 (rank 3) of Mayhew–Royle, *Matroids with nine elements* (arXiv:math/0702316). The campaign agent re-cites them and drops `[VERIFY]` from the counts; the F1 Oxley citations stay `[VERIFY]`.
