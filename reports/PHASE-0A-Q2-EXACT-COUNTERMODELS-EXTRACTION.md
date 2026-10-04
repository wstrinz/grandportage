# Phase 0a Q2 exact arithmetic and formal countermodels

This coordinated batch screens five mechanisms against actual pinned source hypotheses. The dispositions below are **proposals for parent adjudication**. Rows 73.3 and 75.3 were already closed and were not re-extracted.

| Mechanism | New cases | Observation | Reuse distinction |
| --- | --- | --- | --- |
| 70.2, cubic witness family | GP-X347–X350 | Root and inverse ACCEPT; vanishing guard and reducible cubic REFUSE | GP-X22–X24 cover quadratic, not cubic, field and guard controls. |
| 71.2a, exact selected-root sign | GP-X351–X354 | Repeated interior and endpoint sign, common-factor zero ACCEPT; false sign receipt REFUSE | GP-X273/X274 concern selected-root branch cover. |
| 81.5, unit nontriviality | GP-X355 | REFUSE without `1 ≠ 0` | GP-X133 uses a nonzero polynomial ring; the one-element algebra admits a point despite the unit expression. |
| 82.5, cancellation | GP-X356 | REFUSE without no-zero-divisors | Fin4 has `2·2=0` with both factors nonzero; GP-X120/X124 test other premises. |
| OperationContract:664, saturation semantics | GP-X357 | REFUSE exactness despite both local checks | GP-X141 lacks source containment; the unchanged `(6)` output satisfies it and still misses `3`. |

## Observation layers

GP-X347–X350 call pinned `number_field.check_extension_witness` on exact degree-three data. The accepted root and inverse each produce a witness receipt. The rejected cases exercise a vanishing open guard and a reducible declared cubic. These checks do not pick an ordered embedding or certify broader parser/resource soundness.

GP-X351–X354 call pinned selected-real sign production and independent receipt replay. They distinguish repeated-root positive sign, common-factor zero, repeated endpoint sign, and a tampered negative sign on an actually positive root. They share parsing and mathematical Sturm assumptions, and no live CAS was run.

GP-X355–X357 are **reference countermodels to formal premises**, not native GP field verdicts or fresh Lean results. In the one-element algebra, `1=0` and both `x` and `1-x` vanish at its point; over integers they cannot both vanish. In Fin4, nonzero `2·2=0`; exhaustive Fin2 multiplication supplies a no-zero-divisors contrast. For saturation, `I=J=(6)` has source containment, recorded generator `6` has witness `1`, and `3` has saturation witness `2·3=6` while `3∉J`. The exact saturation is `(3)`, as `2g` is divisible by 6 exactly when `g` is divisible by 3. No Lean compilation or native saturation-verifier verdict is claimed.

## Replay and preservation

The immutable baseline had 387 cases. The new immutable run has 398: **381 AGREES, 14 KNOWN_DIFFERENCE, 1 DIAGNOSTIC_OBSERVED, 1 PENDING, 1 UNSUPPORTED**. All eleven new cases agree. All 387 prior case SHA-256 values, expected and observed verdicts, statuses, layers, and routes are unchanged. GP-X236/X237 reason strings differ only in regenerated completion markers; normalized reasons match.

- Baseline: `reports/oracle-runs/20260929T003257767801Z.json`.
- New run: `reports/oracle-runs/20260929T012356934782Z.json`.
- Machine-readable row dispositions, observations and hashes: `reports/PHASE-0A-Q2-EXACT-COUNTERMODELS-EVIDENCE.json`.
