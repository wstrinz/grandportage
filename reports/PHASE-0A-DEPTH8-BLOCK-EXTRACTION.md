# Phase 0a: depth-eight block contract extraction

Eight new cases, GP-X324 through GP-X331, cover one intact positive block and seven distinct refusals from the eight-parameter historical test. The eighth mutation, changing first_open_obligation to CLOSED, is already covered at the same logical conclusion by GP-X37: a completion label cannot supply the specifically missing checked artifact. The new cases use the hash-bound retained fixture and the pinned historical depth-eight block adapter at 7991c9052f13e8dcaa78b5eae36f31663e080c1e. Their attempted conclusions and expectations were written before probe wiring.

## Exact gates and conclusions

| Parameter | Case | Observed gate | Bound conclusion |
|---|---|---|---|
| Intact block | GP-X324 | ACCEPT | Necessary rank-two affine block and symbolic compatibility only; residual not exported, graph effect NONE |
| Changed raw coefficient | GP-X325 | A2 | Native raw-column SHA-256 commitment no longer matches |
| Changed transported 3x2 block | GP-X326 | A4 | Native block SHA-256 commitment no longer matches |
| POINT_INCLUSION graph effect | GP-X327 | M1 | Necessary-block projection cannot mint point inclusion |
| Changed D7 derivative transport sign | GP-X328 | M1 | Projection text no longer binds the checked pivot-absorbed transport |
| Residual status EXPORTED | GP-X329 | M1 | The missing r8 polynomial is not supplied by a status label |
| EQUIVALENT_ACTUAL_SOURCE_FIBER semantic layer | GP-X330 | M1 | Necessary extension block cannot become actual-source equivalence by relabelling |
| first_open_obligation CLOSED | GP-X37 | Existing refusal | Completion label does not supply the missing checked artifact |
| Remove R from never_inverted | GP-X331 | A11 | The no-inversion ledger boundary cannot be erased without a unit warrant |

A2 and A4 are native commitment mismatches; the historical adapter refuses before proving a changed matrix mathematically false. The four M1 cases are exact projection-contract comparisons performed before the arithmetic checker. GP-X328 therefore records a D7 binding refusal, not an independent derivative theorem. GP-X329 does not normalize a missing residual into a named certificate. A11 compares the explicit inverted, derived-unit, and never-inverted ledger after the earlier block checks; deletion of R is not proof that R is a nonunit or an actual cancellation counterexample. GP-X124 remains the separate cancellation counterexample. All eight new observations retain graph effect NONE and no source-equivalence authority.

## Replay and preservation

tools/check-corpus.py validated all 372 cases, source anchors, and the pinned oracle. The full offline replay at reports/oracle-runs/20260928T201826560097Z.json has 357 AGREES, 12 KNOWN_DIFFERENCE, 1 DIAGNOSTIC_OBSERVED, 1 PENDING, and 1 UNSUPPORTED. All eight new cases AGREE. Compared with reports/oracle-runs/20260928T200343664378Z.json, every one of the 364 prior case files has the same SHA-256, and its expectation, observed verdict, status, route, and layer are unchanged. GP-X236/X237 only regenerated per-run completion markers in diagnostic reason text; normalized reasons match. Previous immutable runs were not edited.

Structured observations and hashes: reports/PHASE-0A-DEPTH8-BLOCK-EVIDENCE.json. This extraction does not change global coverage totals or close a Phase 0 gate.
