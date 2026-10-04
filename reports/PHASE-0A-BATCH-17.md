# Phase 0a — compiler slots and bounded process controls

Fifteen cases GP-X240–254 add three acceptance expectations and twelve refusals. Total: 295 cases (84 ACCEPT, 211 REFUSE). Final replay: 287 agreements, five known conservative differences, one diagnostic observation, one pending case and one unsupported case. All 280 prior case files remain byte-identical. Final replay: oracle-runs/20260928T125957587639Z.json.

The cases cover an unshadowed variable, a harmless comment/assignment, hidden declarations in body/expression/type slots, execute/kill/setring/LIB bypasses, comment-prefixed variants, and injected ring variable/name fields. They construct program text only; none executes its strings. GP-X254 independently checks a comment-free assignment.

## Newly reproduced conservative refusal

GP-X241 expects a harmless comment and assignment to remain legal. The statement guard accepts them after comment stripping. The later scalar-division guard instead sees raw `//`, parses it as Python syntax and raises CASError. Initial replay recorded ERROR because the new adapter did not yet catch that documented exception type; that raw run is retained. The adapter now records the actual refusal and the route classifies a known conservative difference. Neither the input nor expected ACCEPT was changed.

COMMENT-DIVISION-AUDIT.json isolates four controls: assignment alone passes; comment alone and comment plus assignment refuse; actual nonconstant division still refuses. This is a usability/conservatism defect, not a false-authority result. Proposed correction: shared lexical analysis or a typed syntax representation that distinguishes comments and strings from arithmetic before division checks. Preserve the existing identifier/division controls; naive text stripping is not a general grammar proof. The frozen source remains unchanged.

## Process evidence

Fifteen selected source test instances pass: twelve compiler-guard instances and three process controls. The latter test WSL inner-timeout argument construction, stdout overflow with a 128-byte budget, and a child that does not read a one-megabyte stdin payload under a 0.2-second timeout (the test requires return within four seconds). Two use real small Python children on Windows; none runs Singular. Details and timings are in PROCESS-CUSTODY-SLICE.json and oracle-compiler-process.xml.

This evidence does not prove arbitrary descendant termination, real WSL execution, all stream races or full compiler grammar safety. The source itself calls its statement guard a denylist for recorded defects, and that limitation remains explicit.

Current source coverage: 48 partial / 320 unreviewed, zero claimed fully semantically reviewed. Private freeze preparation remains verified; campaign manifest and later spike prerequisites are outstanding. Phase 0 remains active.
