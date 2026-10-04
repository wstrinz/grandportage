# Phase 0a deleted IR snapshot review

Reviewed exactly 14 pinned deleted `review/ir-v2-projection/` blobs. Every blob declares `DERIVED_READ_MODEL_ONLY` and `graph_effect: NONE`; generated projections and source/report hashes therefore do not establish semantic coverage.

| Disposition | Count |
|---|---:|
| `covered_by_existing_case` | 1 |
| `metadata_only_no_neutral_case_obligation` | 7 |
| `metadata_only_positive_replay_no_neutral_case_obligation` | 2 |
| `partially_covered_with_unresolved_transport_gate` | 1 |
| `unresolved_minimal_mechanism` | 3 |

One direct neutral-case match is atlas's unverified certificate (`GP-X65`). The unresolved mechanisms are the D1 family-bridge gate, the D3 PREDICATE/COUNT schema pair, and the X8/X10 transport-completeness/source-binding gate. D2's 96- and 97-variable fixtures are both retained positive `check_witness` assertions; the filename `fail-97vars` is not a refusal.

Source pointers and each blob SHA are recorded in the JSON review. The review uses only pinned predecessor blobs, retained review documents, and bounded retained guard-source slices.
