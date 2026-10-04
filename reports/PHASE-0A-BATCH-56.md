# Phase 0a — MCP request and commit boundaries

Read complete declaration/check handlers, dispatcher, response constructors, stream loop and main entry, plus test_mcp.py lines 1–240. Neither MCP nor its test file is claimed fully read. Six selected existing protocol/shape tests pass, with 36 deselected. Five new bounded controls record behavior in MCP-REQUEST-COMMIT-BOUNDARY.json.

Malformed JSON syntax produces a parse-error response and the next ping succeeds. A syntactically valid JSON array reaches request.get before the handler exception guard and raises AttributeError, ending this serve invocation before the next ping. Proposed fix: validate request/params/arguments shapes and contain per-message failures before calling handlers. No external service was contacted; the control uses StringIO.

Three temporary graph declarations distinguish outcomes. A valid model is saved successfully. An invalid event returns an error with unchanged bytes. A valid model followed by an injected C.run reporting exception is durably saved, yet dispatch returns isError with a traceback. This is a simulated post-commit reporting failure, not an observed production outage. The response does not falsely say unchanged in this path, but an error alone cannot tell the caller whether retrying duplicates an already committed action. Proposed fix: expose commit status/receipt separately from rendering errors and define retry behavior explicitly.

The declaration handler's unchanged wording covers exceptions from append; this slice does not establish append's behavior under every I/O failure. Per-call root arguments make selection explicit, not an access-control boundary. Findings are interface/custody diagnostics, not new mathematical corpus verdicts.

All 352 cases still validate, expectations and adapter bytes are unchanged, and no redundant full replay was needed. No campaign reads, live CAS, Lean spike, oracle changes or publication. Source coverage remains 83 partial / 285 unreviewed; Phase 0 stays active.
