# Phase 0a structural eligibility and fallback extraction

The retained depth-six full-template test pairs an intact selected face with one sparse coefficient mutation. The pinned v0.37 implementation first checks whether every selected generator occurs literally among source generators. When that check succeeds, `V.containment` returns `VERIFIED` through the unit-cofactor shortcut. When it fails, the verifier calls the backend identity classifier.

This extraction records those two **operational dispatch observations** with neutral one-variable graphs. The case fixtures use the same sparse polynomial schema, necessary-condition edge, and identity map as the retained test. They are small projections of the pinned code branches, not a replay of the historical full template.

| Case | Selected generator | Eligibility | Native containment result | Injected backend calls | Corpus observation |
| --- | --- | --- | --- | ---: | --- |
| GP-X337 | `x` with source `(x)` | true | `VERIFIED` | 0 | `ACCEPT`, structural shortcut |
| GP-X338 | `999*x` with source `(x)` | false | none | 1 | `ACCEPT`, backend fallback observed |

The `ACCEPT` labels mean the requested dispatch observation was reproduced. They are not mathematical containment verdicts. In GP-X338 the backend is an injected stub that raises after recording its call; no native result is returned. An independent exact membership check returns `REFERENCE_CHECKED` for `999*x` in `(x)`, confirming that a failed literal shortcut does not imply failed ideal containment.

## Source and method

- Historical pair: `gp-history` `7991c9052f13e8dcaa78b5eae36f31663e080c1e`, `tests/test_jc_source_depth6_full_template.py:53,64`.
- Frozen implementation: `gp-v037` `ac4155787207e2847d248cffed7be871d5dcd577`, `grandportage/provenance.py:318-351` and `grandportage/verify.py:208-236`.
- Adapter: `tools/structural_dispatch_probes.py`, invoked only for the two `structural_dispatch` routes. It builds the source and selected graph, checks eligibility, and runs `V.containment` with a forbidden backend stub. GP-X338 additionally runs the separate exact membership control.

The historical test's full 78-variable, 147-source, 25-selected fixture was read but not executed for this extraction. These cases establish the same pinned branch behavior at the dispatch boundary. They do not establish behavior of a live external CAS or a mathematical noncontainment result.

## Replay and preservation

The baseline immutable run had 377 cases. The new immutable run has 379: **364 AGREES, 12 KNOWN_DIFFERENCE, 1 DIAGNOSTIC_OBSERVED, 1 PENDING, 1 UNSUPPORTED**. GP-X337 and GP-X338 both `AGREES`. All 377 earlier case files retain identical SHA-256 bytes, and all earlier expected values, observed verdicts, statuses, layers, and routes are unchanged. GP-X236 and GP-X237 have reason-string changes limited to regenerated completion markers; their normalized reasons are identical.

- Baseline: `reports/oracle-runs/20260928T203130963441Z.json`.
- New run: `reports/oracle-runs/20260928T211311262604Z.json`.
- Machine-readable observations and file hashes: `reports/PHASE-0A-STRUCTURAL-DISPATCH-EVIDENCE.json`.
