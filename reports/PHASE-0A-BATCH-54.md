# Phase 0a — implementation identity limits

Fully text-read identity.py and the identity-surface and in-band-identity tests. Twelve offline tests pass; one live backend test is deselected. The surface tests compare shared representations, use mocked doctor health/version probes, and exercise distinct temporary MCP roots. In-band tests inject transcripts and verify identity/nonce refusal; no actual backend execution or binary authenticity is established.

Three bounded controls clarify metadata and error contracts. Git revision and dirty status are cached per process; mocked checkout changes remain invisible until cache clearing. This matches the implementation but limits claims of exact executing-code identity: it is a cached repository observation, not a loaded-code digest. Missing Git context yields (None, None) and explicit unavailable/unknown text, not a fabricated clean revision.

A numeric source_commit in otherwise valid current metadata raises TypeError from regex matching, outside the normal GraphError validation contract. The malformed input is not accepted. Proposed fix: type-check commit values before matching and normalize errors at the documented boundary. Keep this robustness diagnostic distinct from a normal corpus refusal or false-proof admission.

Proposed documentation clarification: label identity as source metadata and distinguish consistent self-reporting from reproducible build/content attestation. Stronger executable identity is an open design requirement, not a silently selected implementation policy. The diagnostic clears caches after its mocks and never changes oracle files.

Corpus remains 352 with unchanged expected/observed outcomes. No campaign harvest, live CAS, Lean spike or publication. Phase 0 remains active; passing these tests does not complete diagnostic/schema source review.
