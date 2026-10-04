# Phase 0a nine-row mapping adjudication

Reviewed exactly the nine original unresolved mapping rows against pinned tests, the narrow adapter gates they reach, and the full existing corpus.

| Disposition | Count |
|---|---:|
| covered | 5 |
| partially_covered | 2 |
| unresolved | 2 |

Genuinely missing mechanisms:
- `test_changed_jump_schedule_is_refused`: Minimal negative: retain the correct unilateral domain, zero tail, and nonzero endpoint, alter one declared jump index, and refuse the recurrence certificate. Positive control: the same intact schedule is accepted (X118).
- `test_zeroed_omega_comb_is_refused`: Minimal negative: an exact witness with the required omega-like value set to zero must be refused by a nonzero-premise replay. Positive control: the same witness with a checked nonzero value is accepted. The existing non-promotion cases do not reach this arithmetic gate.
- `test_checked_in_authority_fixture_is_exact_adapter_output`: Shared metadata-only positive control for both authority-spec adapters: encode the same frozen specification twice and require byte equality with the checked-in canonical artifact; paired negative: a changed semantic field or noncanonical encoding is rejected (X215 already supplies the latter).

The two deterministic authority-artifact rows share one metadata-only positive-control gap; neither is evidence for the localized-unit mathematics. No corpus, adapter, or oracle content was changed.
