# Phase 0a — MCP regression coverage and mutation wrappers

Completed all 771 lines of test_mcp.py and ran its full 42 tests successfully. Read complete baseline-accept, receipt/export-tail, merge-assay and all four verification wrapper definitions. Definition intervals and source/test hashes are retained in MCP-BOUNDARY-REVIEW.json. The whole MCP implementation remains partially read.

Tests establish selected transactional declaration refusals, root selection, baseline visibility, nonmutating merge assay, multi-premise and missing-slot rendering, protocol responses and verifier argument forwarding. Producing tests inject backend transcripts; elimination wrapper tests inject verifier functions. These do not establish live backend behavior, arbitrary protocol totality or arithmetic soundness. Existing malformed-array and post-append diagnostic failures remain documented despite the green full test file.

COMPOSES from merge assay means structural graphs compose, with actionable findings counted separately; it does not assert a clean graph or mathematical entailment. Baseline acceptance selects current finding IDs and stores a rationale, which is accounting, not earned proof authority. Verification wrappers forward record/dry-run and certificate parameters; a response suffix cannot replace checking what was durably recorded.

A retained show-test comment says missing-slot declaration crashes _first_refusal. The current helper uses graph.edges.get and the show test bypasses declaration; the comment is historical, not current failure evidence. The test's valid claim is that the absent premise is rendered visibly. Proposed documentation cleanup: date historical failure comments or state the current assertion so reviewers do not mistake them for live defects.

No new cases or replay changes. All 352 source anchors and fixed expectations validate. No campaign harvest, live CAS, Lean spike, frozen-source mutation or publication. Phase 0 remains active.
