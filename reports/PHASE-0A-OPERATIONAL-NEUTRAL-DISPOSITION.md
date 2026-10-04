# Phase 0a operational neutral-coverage disposition

This is a proposed mapping of the 29 operational incidents into neutral coverage, using only the existing corpus, retained audits, and the accepted 76.7 generator-identity contrast. It preserves the incidents even though most are operational diagnostics rather than false-held mathematical claims. No case, adapter, replay, expectation, or policy changed.

**Disposition:** No exact existing neutral case tests one of these 29 attempted operational conclusions. Twenty-seven rows already have concrete retained input, source, contract and observation and need only schema transcription if strict corpus coverage is selected. Two source-only rows need one specific behavioral control each before such transcription. The prior near cases remain contrasts, not exact duplicates.

## Finite group conversion list

| Mechanism | Retained records ready for schema conversion | Specific control gap |
| --- | --- | --- |
| Source header and schema | 53.2, 54.3, 55.2a, 55.2b | — |
| Health, request, and commit response | 55.3, 56.2, 56.3 | — |
| Handoff and advertised inputs | 58.2 | 58.3a |
| Digest and filesystem custody | 61.3, 63.2, 63.3, 63.4, 65.4, 69.3 | — |
| Packet and attempt identity | 64.3b | — |
| Frontier counts and status | 65.3a, 65.3b, 66.2 | — |
| Corpus intake reporting | 69.2 | — |
| Transcript and post-validation identity | 74.3, 74.5, 76.2 | — |
| Lexical validators | 74.4 | 76.8b |
| CAS declaration identity | 76.3, 76.7 | — |
| Hook errors and explanation changes | 77.3, 77.4 | — |

This is eleven bounded transcription groups, with row-specific controls kept distinct. It is a disposition list, not an instruction to add 27 new executable cases. The companion JSON retains each row’s concrete input, attempted conclusion, expected contract, observed behavior, source pin, exact audit pointers, screened near cases, and smallest action.

## Distinguishing evidence by row

### Source header and schema

- **53.2 — Retained record → schema.** Format-6 missing identity refuses, format-8/epoch-11 missing identity passes dry run, valid epoch-11 header passes; source bytes stay fixed. Evidence: `reports/MIGRATION-CUSTODY-BOUNDARY.json#/controls/0`, `reports/MIGRATION-CUSTODY-BOUNDARY.json#/controls/1`, `reports/MIGRATION-CUSTODY-BOUNDARY.json#/controls/2`.
- **54.3 — Retained record → schema.** Numeric source_commit raises TypeError outside GraphError; valid-string positive is requested but not needed to distinguish this malformed-input error shape. Evidence: `reports/IMPLEMENTATION-IDENTITY-BOUNDARY.json#/controls/2`.
- **55.2a — Retained record → schema.** The same string integral=false passes exported schema and fails native Boolean shape validation. Evidence: `reports/SCHEMA-HEALTH-BOUNDARY.json#/controls/0`.
- **55.2b — Retained record → schema.** The same sparse retraction passes native shape and fails the exported authoring schema; this paired validator disagreement is the incident. Evidence: `reports/SCHEMA-HEALTH-BOUNDARY.json#/controls/1`.

### Health, request, and commit response

- **55.3 — Retained record → schema.** Expected mocked two-generator basis yields healthy true; unexpected one-generator basis warns but also yields healthy true and exit zero. Evidence: `reports/SCHEMA-HEALTH-BOUNDARY.json#/controls/2`, `reports/SCHEMA-HEALTH-BOUNDARY.json#/controls/3`.
- **56.2 — Retained record → schema.** Malformed JSON syntax returns parse error then ping succeeds; valid JSON array raises AttributeError before next ping. Evidence: `reports/MCP-REQUEST-COMMIT-BOUNDARY.json#/controls/0`, `reports/MCP-REQUEST-COMMIT-BOUNDARY.json#/controls/1`.
- **56.3 — Retained record → schema.** Valid append succeeds, pre-append invalid event preserves bytes, and post-append injected render error returns isError after durable model save. Evidence: `reports/MCP-REQUEST-COMMIT-BOUNDARY.json#/controls/2`, `reports/MCP-REQUEST-COMMIT-BOUNDARY.json#/controls/3`, `reports/MCP-REQUEST-COMMIT-BOUNDARY.json#/controls/4`.

### Handoff and advertised inputs

- **58.2 — Retained record → schema.** BASE and ALGEBRAIC_CLOSURE models retain different stored point scopes but identical compact handoff text. Evidence: `reports/MCP-HANDOFF-CONTEXT-BOUNDARY.json#/controls/0`, `reports/MCP-HANDOFF-CONTEXT-BOUNDARY.json#/controls/1`.
- **58.3a — Specific control missing.** Missing paired same-graph requests with distinct valid floor values and a finding whose severity lies between those floors. Evidence: source and batch report only.

### Digest and filesystem custody

- **61.3 — Retained record → schema.** The same committed CRLF fixture is CURRENT_CLEAN in checkout mode and STALE in pinned-ref mode despite a shared LF-normalized digest label. Evidence: `reports/DOSSIER-BOUNDARIES-AUDIT.json#/controls/2`, `reports/DOSSIER-BOUNDARIES-AUDIT.json#/controls/3`.
- **63.2 — Retained record → schema.** Identical protected path refuses while a Windows case alias with force replaces protected input bytes. Evidence: `reports/MATERIALIZATION-BOUNDARY-AUDIT.json#/controls/3`, `reports/MATERIALIZATION-BOUNDARY-AUDIT.json#/controls/5`.
- **63.3 — Retained record → schema.** A preexisting output.PID.tmp triggers FileExistsError and is nevertheless removed by cleanup; normal output refusal is a separate retained control. Evidence: `reports/MATERIALIZATION-BOUNDARY-AUDIT.json#/controls/2`, `reports/MATERIALIZATION-BOUNDARY-AUDIT.json#/controls/4`.
- **63.4 — Retained record → schema.** Injected source change between digest check and copy yields successful archive whose digest differs from the bound digest. Evidence: `reports/MATERIALIZATION-BOUNDARY-AUDIT.json#/controls/0`.
- **65.4 — Retained record → schema.** Actual --emit-review overwrites a bound manifest and, separately, a bound receipt; a separate-path positive is not recorded. Evidence: `reports/FRONTIER-BUNDLE-BOUNDARIES.json#/controls/3`, `reports/FRONTIER-BUNDLE-BOUNDARIES.json#/controls/4`.
- **69.3 — Retained record → schema.** A source export-manifest.json is copied then overwritten by generated metadata; export succeeds and validation reports its SHA mismatch. Evidence: `reports/CORPUS-INTAKE-BOUNDARIES.json#/controls/2`.

### Packet and attempt identity

- **64.3b — Retained record → schema.** Old ledger plus changed same-ID packet is accepted by direct overlay, while explicit prior-ledger binding refuses the changed attempt fingerprint. Evidence: `reports/PACKET-ATTEMPT-BINDING-AUDIT.json#/controls/0`, `reports/PACKET-ATTEMPT-BINDING-AUDIT.json#/controls/1`, `reports/PACKET-ATTEMPT-BINDING-AUDIT.json#/controls/2`.

### Frontier counts and status

- **65.3a — Retained record → schema.** Duplicate open_items yields per-receipt open_count 2 and unique aggregate count 1. Evidence: `reports/FRONTIER-BUNDLE-BOUNDARIES.json#/controls/0`.
- **65.3b — Retained record → schema.** Stable semantic ID with terminal newline is accepted by the retained validator control. Evidence: `reports/FRONTIER-BUNDLE-BOUNDARIES.json#/controls/1`.
- **66.2 — Retained record → schema.** Unknown FAILED status becomes CLOSED by default, whereas explicit frontier_state OPEN remains OPEN. Evidence: `reports/FRONTIER-PROJECTION-BOUNDARIES.json#/controls/0`, `reports/FRONTIER-PROJECTION-BOUNDARIES.json#/controls/1`.

### Corpus intake reporting

- **69.2 — Retained record → schema.** Retention READY accepts a synthetic graph; native load raises GraphError before corpus-report.json is written. Evidence: `reports/CORPUS-INTAKE-BOUNDARIES.json#/controls/0`, `reports/CORPUS-INTAKE-BOUNDARIES.json#/controls/1`.

### Transcript and post-validation identity

- **74.3 — Retained record → schema.** Two actual subprocess raw stdout byte streams differ but decode to the same text and text digest under errors=ignore. Evidence: `reports/BACKEND-TRANSCRIPT-BOUNDARY.json#/observations/0`, `reports/BACKEND-TRANSCRIPT-BOUNDARY.json#/observations/1`.
- **74.5 — Retained record → schema.** Direct injected mutable abort_reason changes artifact fingerprint after construction while validator still accepts. Evidence: `reports/BACKEND-TRANSCRIPT-BOUNDARY.json#/observations/3`.
- **76.2 — Retained record → schema.** Constructor rejects a shadowing statement, but mutation after validation reaches injected runner and mock transcript parsing. Evidence: `reports/CAS-PROGRAM-CUSTODY.json#/observations/0`, `reports/CAS-PROGRAM-CUSTODY.json#/observations/1`.

### Lexical validators

- **74.4 — Retained record → schema.** Bare 64-hex digest and terminal-newline variant both pass valid_fingerprint in the retained observation. Evidence: `reports/BACKEND-TRANSCRIPT-BOUNDARY.json#/observations/2`.
- **76.8b — Specific control missing.** Missing direct assert_is_identifier comparison for bare x and x followed by terminal newline; source regex behavior alone is retained. Evidence: source and batch report only.

### CAS declaration identity

- **76.3 — Retained record → schema.** Parsed output GP_I[1]=x is paired with caller generators [1]; resulting model stores [1], not parsed x. Evidence: `reports/CAS-PROGRAM-CUSTODY.json#/observations/2`.
- **76.7 — Retained record → schema.** Accepted contrast holds rendered template and parsed GP_I[1]=x fixed, changes caller generators [x] to [1], and observes equal semantic-input fingerprint but distinct persisted model generators. Evidence: `reports/PHASE-0A-GENERATOR-IDENTITY-CONTRAST.json#/observations/0`, `reports/PHASE-0A-GENERATOR-IDENTITY-CONTRAST.json#/observations/1`.

### Hook errors and explanation changes

- **77.3 — Retained record → schema.** Valid JSON array baseline and hook payload each escape as AttributeError; valid-object processing is not separately retained in this audit. Evidence: `reports/HOOK-BOUNDARY-AUDIT.json#/observations/0`, `reports/HOOK-BOUNDARY-AUDIT.json#/observations/1`.
- **77.4 — Retained record → schema.** Two distinct malformed graph JSON errors have different evaluation text, but repeat suppression labels the second unchanged while exit remains blocking. Evidence: `reports/HOOK-BOUNDARY-AUDIT.json#/observations/2`.

## Two specific gaps

- **58.3a:** The source handler does not read the advertised `floor` argument, but the record has no paired request outputs. A same-graph comparison with a `DEBT` finding and valid floors `DEBT` and `UNSOUND_CONCLUSION` would bind the behavioral difference. The source-level incident remains preserved meanwhile.
- **76.8b:** The source identifier matcher uses a dollar anchor, but the record has no direct validator result for `x` versus `x` plus a terminal newline. That one direct validator pair would bind the lexical behavior without a CAS run. The source-level incident remains preserved meanwhile.

The accepted [76.7 contrast](PHASE-0A-GENERATOR-IDENTITY-CONTRAST.md) closes the register’s earlier changed-generator evidence gap: equal rendered template and semantic-input fingerprint coexist with different persisted model generators. It belongs in the retained-record conversion set at its injected persistence layer. No further reproduction is requested for it.

## Policy choices kept separate

- **55.2b:** Whether the exported authoring schema promises all native sparse retractions or is explicitly a narrower approximation.
- **56.3:** What durable commit status and retry semantics the response should expose after post-commit rendering failure.
- **58.3a:** Whether the advertised floor is enforced or the tool description narrowed.
- **66.2:** Whether an unknown status refuses input or leaves an obligation open; silent CLOSED is the observed defect.
- **76.3:** Whether caller/output generator mismatch is refused or represented with distinct provenance.

These choices affect how a future schema case would phrase its expected operational response. The recorded mismatches do not depend on selecting a remedy now. Missing positive-control pointers are not silently filled; a recorded paired mismatch is enough to preserve its bounded incident where the comparison itself distinguishes the mechanism.

## Limits

- Report evidence is not yet a strict neutral case-schema entry. This disposition does not close a corpus gate.
- Prior near cases test different attempted conclusions; their IDs and distinctions are listed per row in the JSON.
- Injected runners, direct API calls, scratch files, and source-only readings retain their original layers. No operational incident here is promoted to a mathematical held-claim failure by this report.
- No broad source sweep, new execution, tests, corpus edits, replay, or commits were performed.
