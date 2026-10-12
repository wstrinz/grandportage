# F2 catalog: simple rank-3 matroids on 3 to 9 elements

- `generate.py` is the catalog generator. It is **trusted**: GP does not check it. It extends every class on n points, and the line U(2,n), by one point, then deduplicates by a canonical form. `python generate.py 9 --write` rewrites `catalog.json` and `matroids/C<n>-<i>.json`.
- **Catalog completeness is an OPEN premise (CATALOG-COMPLETE).** Every use of the catalog is modulo it.
- `check.py` is an independent cross-check, not a proof. It checks:
  - each entry is simple and of rank 3, and no two entries are isomorphic;
  - a direct count of labelled linear spaces on [n] equals Σ n!/|Aut(M)|, with |Aut| computed by exhaustive backtracking over bijections;
  - each isomorphism record onto an F1 matroid.
- **Counts for n = 3…9:** 1, 2, 4, 9, 23, 68, 383. They match Table 2 (rank 3) of Mayhew–Royle, *Matroids with nine elements* (arXiv:math/0702316). `check.log` has the n = 9 run (50,166,353 labelled matroids).
- **F1 isomorphs:** C6-01 = U36, C6-09 = MK4, C7-22 = F7⁻, C7-23 = F7, C8-68 = AG23-e, C9-355 = NonPappus, C9-368 = Pappus, C9-383 = AG23. Their χ is the F1 claims' χ, transported by the recorded isomorphism. GP does not check that transport. `check.py` verifies the maps.
