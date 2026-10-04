# Phase 0a zero-regime minimality extraction

The deleted coordinator delta (`9715cf9f6353e5ba528ffc88f1e84fb8d9e6622d`, lines 30-43) records an overstatement: calling `S-1` minimal in every padded regime. The pinned recurrence adapter declares R5 at depth 14 and open ended R6 from depth 15 with no columns or matrix entries, and its padding yields zero for all depths from 14. The adapter also explicitly excludes blanket per-regime minimality from its authority.

| Case | Local observation | Expected / observed | Authority |
| --- | --- | --- | --- |
| GP-X339 | The nonzero unit `1` annihilates each zero regime | `ACCEPT` / `ACCEPT` | Exact reference identity `1 * 0 = 0` |
| GP-X340 | `S-1` cannot be shift-degree minimal on either zero regime | `REFUSE` / `REFUSE` | Unit degree 0 is below `S-1` degree 1 |

`S-1` still annihilates a zero sequence; the refusal concerns **minimality**. The observations are arithmetic controls against the pinned zero-regime structure. There is no native predecessor verifier for this per-regime minimality proposition, and no predecessor false-held verdict is attributed to it.

## Source and reuse screen

- Historical overstatement: `experiments/jc_h3_adjoint_recurrence/JC-COORDINATOR-DELTA.md`, deleted blob `9715cf9f6353e5ba528ffc88f1e84fb8d9e6622d`, lines 30-43, reviewed at `reports/PHASE-0A-SIX-DELETED-NOTES-REVIEW.json#/records/1/incidents/0`.
- Pinned retained implementation: history commit `7991c9052f13e8dcaa78b5eae36f31663e080c1e`, `experiments/jc_h3_adjoint_recurrence/adapter.py:52-53,186-198,257-264,327-333`.
- GP-X118 already accepts the **separate global unilateral** `(S^8)` result from the nonzero depth-13 endpoint on `d >= 6`. GP-X318 mutates that global endpoint; GP-X321 mutates the jump schedule. None tests the local unit counterexample, so the new pair does not duplicate them.

The probe validates the pinned fixture and digest, checks the empty R5/R6 structure and padded zero values, then evaluates the explicit operator identity and shift-degree comparison. It records `native_per_regime_minimality_verdict: null`. The fixture's global endpoint and S8 premises remain intact. No Lean compilation, external checker, graph claim, or wider campaign source is involved.

## Replay and preservation

The immutable baseline had 379 cases. The new immutable run has 381: **366 AGREES, 12 KNOWN_DIFFERENCE, 1 DIAGNOSTIC_OBSERVED, 1 PENDING, 1 UNSUPPORTED**. Both new cases agree. All 379 prior case SHA-256 values, expected and observed verdicts, statuses, layers, and routes are unchanged. GP-X236 and GP-X237 differ only in regenerated completion markers in their reason strings; normalized reasons match.

- Baseline: `reports/oracle-runs/20260928T211311262604Z.json`.
- New run: `reports/oracle-runs/20260928T220044757918Z.json`.
- Machine-readable observations and hashes: `reports/PHASE-0A-ZERO-REGIME-MINIMALITY-EVIDENCE.json`.
