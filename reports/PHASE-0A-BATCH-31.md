# Phase 0a — selected-root cover cases

GP-X273–274 represent the matched-root positive control and disjoint-root negative control from Batch 30. Inputs contain exact rational polynomial models and isolating intervals, without legacy graph events. Parent selects the positive root of x²−2; branches select either that root or the negative root. The latter fail to cover the parent despite equal ideals.

The adapter invokes actual native model/partition validation and partition verification. A bounded backend stub checks its inputs and gives exact answers about the proper ideal (x²−2) and identical ideal covers. No CAS or persisted verdict is used. GP-X274 retains expected REFUSE and observed ACCEPT, classified partition_selected_embedding_omitted.

Total 315 cases: 93 expected ACCEPT and 222 REFUSE. Full replay: 301 agreements, eleven known differences, one diagnostic observation, one pending and one unsupported. No ERROR or REVIEW_REQUIRED. All 313 prior case files are byte-identical, and runner/routes/adapter/case hashes match the report.

Replay: oracle-runs/20260928T134501652085Z.json. Frozen source and previous expectations unchanged. Phase 0 remains active; source coverage is still 57 partial / 311 unreviewed, with full source/history and campaign/Lean prerequisites outstanding.
