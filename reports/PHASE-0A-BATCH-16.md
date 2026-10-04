# Phase 0a — launch guards and recording

Ten cases GP-X230–239 add two acceptance controls and eight refusals. Total: 280 cases (81 ACCEPT, 199 REFUSE). Full replay: 273 agreements, four known conservative differences, one diagnostic observation, one pending case and one unsupported case. All 270 earlier cases remain byte-identical. Replay: oracle-runs/20260928T125417944786Z.json.

Missing declaration, unknown relation, unexplained UNTYPED and raw program text refuse before the injected runner is called, with identical graph bytes and no artifact file. Explained UNTYPED and a typed declaration can record a completed operation; neither establishes verified relation semantics or a theorem. Reported solver errors at exit zero and other nonzero exits refuse without changing the graph. Abort records only a provenance note and raw artifact, with no produced model or semantic edge.

## Late source-reference validation

GP-X239 calls the runner once and persists one raw artifact before discovering that the named source model does not exist. The graph append refuses transactionally and its bytes remain unchanged. This is not an invalid graph or false-authority reproduction. It is unnecessary work and an unreferenced artifact, and it narrows the meaning of declaration-before-execution: relation syntax is checked early, source existence is not.

Proposed fix for consideration: preflight current source/target references before expensive work, then revalidate transactionally when appending because state can change concurrently. Preserve attempts and avoid mistaking a preflight pass for mathematical authority. No legacy code or 0.50 core policy was changed. Exact subobservations are in LAUNCH-RECORDING-BOUNDARY.json.

Seventeen selected source regressions pass (oracle-launch-boundary.xml). Every new case uses a counted injected runner and an isolated F scratch graph. No Singular process ran. Reading the actual subprocess implementation identifies remaining work on WSL child deadlines, process-tree termination, bounded output draining and pipe/thread cleanup; this slice does not claim to verify those mechanisms.

Program-field injection paths through declaration expressions, types and body statements were read as follow-up source material; existing identifier cases alone do not disposition all these paths. Continue those controls, actual process custody, artifact note/Groebner binding and broader authority review.

Current source coverage: 48 partial / 320 unreviewed, zero claimed fully semantically reviewed. Private freeze preparation remains verified; campaign manifest is still pending and the Lean spike is deferred. Phase 0 remains active.
