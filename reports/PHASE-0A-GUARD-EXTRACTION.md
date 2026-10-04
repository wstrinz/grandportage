# Phase 0a frozen guard extraction

Status: candidate material for parent integration, not a Phase 0a closure decision.

Five neutral candidates are prepared in `reports/guard-case-candidates/`:

| Candidate | Frozen observation | Expected result | Gate actually reached |
| --- | --- | --- | --- |
| GP-X399 | A family `PREDICATE` claim is supplied directly to an inference. | REFUSE | Family-premise `DISCHARGE` gate; no checked `family_bridge`. |
| GP-X400 | A `PREDICATE` carries `COUNT`-only disposition fields. | REFUSE | Declaration shape gate rejecting `COUNT` fields on `PREDICATE`. |
| GP-X401 | The same declaration is correctly typed as `COUNT`, settling one of 42 members. | ACCEPT | Declaration loads, but `FAMILY:C-SPLIT` remains live for the 41-member debt. |
| GP-X402 | `INF-X8` omits E5 census completeness. | REFUSE | Explicit `required_kind` open-premise slot reported by `C.R_TRANSPORT`. |
| GP-X403 | `INF-X10` omits the E5 actual-source/parent-cover bridge. | REFUSE | Explicit `required_kind` open-premise slot reported by `C.R_TRANSPORT`. |

The standalone [`guard_snapshot_probes.py`](../tools/guard_snapshot_probes.py) verifies the four LF-normalized fixture hashes before it imports the pinned loader/checker or folds any fixture. Its `run()` function returns the report for a parent runner; the command-line wrapper writes [`PHASE-0A-GUARD-EXTRACTION.json`](PHASE-0A-GUARD-EXTRACTION.json). The focused run passed: all five candidate schemas validate against `corpus/case.schema.json`, their `gp-v037` source records use commit `ac4155787207e2847d248cffed7be871d5dcd577`, and each test anchor occurs at its declared line in the pinned checkout.

`INF-X9` is recorded only as a limited contrast: it is clean in this frozen graph because `CL-E5-DECLARED` is supplied at declared, unproved authority. It does not establish family-bridge, census-completeness, actual-source, or parent-cover positive authority. The probe uses only the frozen Python loader/checker, invokes no CAS, and writes nothing in the oracle checkout.
