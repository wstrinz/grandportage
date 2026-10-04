# Phase 0a — campaign packet and attempt identity

Fully read campaign.py, test_campaign.py, PORTAGE-COMMAND-V0.md and complete CLI packet/ledger handlers. Thirteen source tests pass. Three controls use only copied GP-owned pinned fixtures; no external campaign directories were read.

Packets bind source bytes, bundle/catalog digests and explicit frontier fields. Their acceptance commands, evidence contract IDs and source commit labels remain descriptive; attempts store returned artifact digest strings and authored replay/mutation results. Neither packet compilation nor ledger compilation executes mathematical verification or grants graph authority.

With packet ID unchanged, alter its proposition and explicitly refresh catalog/packet/ledger manifest hashes. Recompiling unchanged accepted-attempt input assigns the new packet fingerprint and preserves ACCEPTED_ARTIFACT. This is not a hash bypass: the caller has supplied newly matching bindings. An explicit prior ledger correctly refuses because the normalized attempt fingerprint changed. A direct overlay of the old ledger with the new packet set succeeds because it checks IDs but not content identity. Normal CLI rebuilds both inputs; an actual concurrent CLI race was not tested.

Proposed fixes: require exact packet fingerprints in attempt inputs, compare them during normalization, and validate both packet-set and per-attempt identity in overlay construction. Keep recorded PASS separate from executed, artifact-bound replay. Prior-ledger comparison establishes preservation by ID only when requested; sorted IDs do not establish chronological prefix order. Verification debt is a count of pending outcomes, not mathematical completeness.

Documentation's conditional prior-binding description is accurate; general immutable/append-only wording needs that condition. The example's agent-output command does not filter lifecycle to ACTIVE; the fixture test says active count zero. Frontier-bundle internals remain a dependency review task.

Corpus expectations, adapters, replay and frozen code remain unchanged. The 352-case validator passes. No live CAS, campaign harvest, Lean work or publication. Phase 0 remains active.
