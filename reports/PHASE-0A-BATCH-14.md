# Phase 0a — durable artifact integrity

Eleven cases GP-X211–221 add two acceptance controls and nine refusals. Total: 262 cases (74 ACCEPT, 188 REFUSE). Full replay: 255 agreements, four known conservative differences, one diagnostic observation, one pending case and one unsupported case. All 251 earlier cases remain byte-identical.

The new cases cover deduplicating roundtrip, preserving a corrupt object instead of silently healing it, inner-output hash mismatch, rehashed content still failing the retained address, noncanonical encoding, missing and swapped references, protocol mismatch, path-like references, immutable-link failure with no target object, and ordered batch persistence. Every filesystem mutation is confined to disposable F scratch storage. No actual retained evidence was damaged, no external process ran and no graph authority was minted.

The final immutable replay is oracle-runs/20260928T124442499612Z.json. It includes the new adapter hash and the exact frozen source fixture-helper hash. Specific checks confirm corrupt bytes remain, failed publication leaves no target, inner hash and content-address refusals are distinct, and successful batch order is preserved.

Three composition controls in ARTIFACT-MANIFEST-BOUNDARY.json show why a quiet helper is not broad validation: audit_manifest checks referenced artifact projections and backend fields, so an unrelated bad aggregate digest or extra top-level field is outside its check. decode_backend_provenance refuses those malformed descriptors, and audit_graph_report reports them. The normal control passes all layers. This is a documented division of responsibility, not a reproduced end-to-end bypass.

The existing thirteen artifact source regressions passed in the preceding checkpoint and their source bytes remain unchanged; they were not redundantly rerun. The new neutral extraction and three composition controls execute the affected functions directly. The entire artifacts.py source is now text-read. Complete envelope type validation, concurrent publication behavior, note references and Groebner final-proof binding remain to be dispositioned. Graph fold versus unavailable artifacts, exact replay availability and historical-readable provenance still need neutral cases.

Proposed rework treatment: expose whole-manifest validity, object availability, exact replay, and current authority as distinct results; do not label a successful projection audit as proof admission. No new schema or policy is adopted here.

Current source coverage: 45 partial / 323 unreviewed, zero claimed fully semantically reviewed. The active Phase 0 goal, pending campaign manifest and deferred Lean spike remain unchanged.
