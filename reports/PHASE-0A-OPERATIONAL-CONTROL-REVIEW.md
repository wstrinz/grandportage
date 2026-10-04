# Phase 0a operational positive-control review

**Status:** finite parent review of the 15 candidates previously marked `positive_control.not_retained`. No new control was run.

A missing positive-control pointer is not automatically a reproduction gap. The retained incident counterexample is enough to document an operational mismatch when the asserted overclaim is narrow. Frozen tests below are cited as existing assertions, not as fresh oracle observations.

| Candidate | Row | Disposition | Evidence |
| --- | --- | --- | --- |
| GP-X371 | 54.3 | shared_test_sufficient_for_incident | `reports/IMPLEMENTATION-IDENTITY-BOUNDARY.json#/controls/2`; `oracle/checkout/tests/test_format_epoch.py#L27-L46`; `oracle/checkout/tests/test_format_epoch.py#L605-L611` |
| GP-X372 | 55.2a | finite_control_only_if_admitting_exact_validator_pair | `reports/SCHEMA-HEALTH-BOUNDARY.json#/controls/0`; `oracle/checkout/tests/test_adversarial.py#L3901-L3911`; `tools/audit-schema-health.py#L8-L12` |
| GP-X373 | 55.2b | policy_decision_first | `reports/SCHEMA-HEALTH-BOUNDARY.json#/controls/1`; `oracle/checkout/tests/test_format_epoch.py#L70-L91` |
| GP-X377 | 58.2 | retained_pair_sufficient | `reports/MCP-HANDOFF-CONTEXT-BOUNDARY.json#/controls/0`; `reports/MCP-HANDOFF-CONTEXT-BOUNDARY.json#/controls/1` |
| GP-X382 | 63.4 | shared_test_sufficient_for_incident | `reports/MATERIALIZATION-BOUNDARY-AUDIT.json#/controls/0`; `oracle/checkout/tests/test_release.py#L48-L76`; `oracle/checkout/tests/test_release.py#L99-L114` |
| GP-X383 | 65.4 | shared_test_sufficient_for_incident | `reports/FRONTIER-BUNDLE-BOUNDARIES.json#/controls/3`; `reports/FRONTIER-BUNDLE-BOUNDARIES.json#/controls/4`; `oracle/checkout/tests/test_frontier_bundle.py#L185-L200` |
| GP-X384 | 69.3 | shared_test_sufficient_for_incident | `reports/CORPUS-INTAKE-BOUNDARIES.json#/controls/2`; `oracle/checkout/tests/test_corpus_check.py#L10-L19` |
| GP-X386 | 65.3a | shared_test_sufficient_for_incident | `reports/FRONTIER-BUNDLE-BOUNDARIES.json#/controls/0`; `oracle/checkout/tests/test_frontier_bundle.py#L67-L80`; `oracle/checkout/tests/test_frontier_bundle.py#L237-L245` |
| GP-X387 | 65.3b | shared_test_sufficient_for_incident | `reports/FRONTIER-BUNDLE-BOUNDARIES.json#/controls/1`; `oracle/checkout/tests/test_frontier.py#L121-L130` |
| GP-X389 | 69.2 | finite_control_conditional_on_reporting_policy | `reports/CORPUS-INTAKE-BOUNDARIES.json#/controls/0`; `reports/CORPUS-INTAKE-BOUNDARIES.json#/controls/1`; `oracle/checkout/tests/test_corpus_check.py#L10-L19` |
| GP-X391 | 74.5 | shared_test_sufficient_for_incident | `reports/BACKEND-TRANSCRIPT-BOUNDARY.json#/observations/3`; `oracle/checkout/tests/test_artifacts.py#L21-L70`; `oracle/checkout/tests/test_backend.py#L98-L132` |
| GP-X393 | 74.4 | retained_pair_sufficient | `reports/BACKEND-TRANSCRIPT-BOUNDARY.json#/observations/2` |
| GP-X395 | 76.3 | shared_retained_contrast_sufficient_for_incident | `reports/CAS-PROGRAM-CUSTODY.json#/observations/2`; `reports/PHASE-0A-GENERATOR-IDENTITY-CONTRAST.json#/observations/0`; `reports/PHASE-0A-GENERATOR-IDENTITY-CONTRAST.json#/observations/1` |
| GP-X397 | 77.3 | shared_retained_harness_sufficient_for_incident | `reports/HOOK-BOUNDARY-AUDIT.json#/observations/0`; `reports/HOOK-BOUNDARY-AUDIT.json#/observations/1`; `reports/HOOK-BOUNDARY-AUDIT.json#/observations/2`; `tools/audit-hook-boundaries.py#L14-L25` |
| GP-X398 | 77.4 | incident_contrast_complete_without_separate_positive | `reports/HOOK-BOUNDARY-AUDIT.json#/observations/2` |

## Assessment by candidate

### GP-X371 · 54.3

**Assessment:** Valid string metadata has a frozen successful path. The numeric-field diagnostic itself is retained. A new valid-string execution would not change the candidate claim.

### GP-X372 · 55.2a

**Assessment:** The mismatch is complete for incident documentation. No retained control applies the same typed-Boolean claim to both exported schema and native validator. The native graph assertion is a partial shared control.

**Finite control, unrun:** Use the same minimal claim event as the retained string control, replacing integral with JSON boolean false; call the exported event schema and native validate_native_event once each offline. Record both outcomes; do not alter a graph. Trigger: only if parent wants an admitted two-sided validator route

### GP-X373 · 55.2b

**Assessment:** The current two-validator contrast is the incident. There cannot be a successful same-input agreement for this sparse tombstone under the present exported schema. A repair test depends on whether the schema is a complete native contract or a narrower authoring contract.

**Parent decision:** Choose whether the exported schema must admit native sparse retractions or explicitly remain a narrower authoring schema before requiring an agreement control.

### GP-X377 · 58.2

**Assessment:** Each side is a successful handoff rendering. The point-scope values differ while rendered text matches. A third positive case adds no mechanism distinction.

### GP-X382 · 63.4

**Assessment:** The frozen success and earlier-change refusal cover the ordinary path; the retained injection isolates the later check-to-copy window. Exact archive-byte equality is not separately asserted in the success test, so do not describe that test as a proof of the failing window.

### GP-X383 · 65.4

**Assessment:** The separate-path CLI success is a genuine shared operational control. That frozen test does not record before/after hashes of bound inputs; the overwrite incident is supported by the retained controls themselves.

### GP-X384 · 69.3

**Assessment:** The no-collision frozen test supplies the requested successful export contrast. READY here is structural retention, not native graph authority.

### GP-X386 · 65.3a

**Assessment:** The unique-item success is already represented in frozen tests; duplicate-list mismatch is retained. No new control is needed for the incident.

### GP-X387 · 65.3b

**Assessment:** Bare A has a frozen successful build, and the retained control records acceptance of A with a terminal newline. A separate direct bare-ID call is unnecessary for incident documentation.

### GP-X389 · 69.2

**Assessment:** The READY-versus-native-load distinction is fully documented. No cited retained control demonstrates that a valid native graph produces this reporter output. The candidate reason also asks for a per-campaign load-error report, which is a reporting contract choice.

**Finite control, unrun:** In an isolated offline reporter root, provide one native-loadable graph and the existing malformed kernel_epoch-null campaign; invoke the reporter once and record the valid campaign report, malformed campaign error entry, output file, and overall status. No corpus admission. Trigger: if parent keeps a per-campaign report guarantee in the candidate contract

**Parent decision:** Decide whether the contract requires a per-campaign error report after native load refusal, or only refuses to equate structural READY with native report readiness.

### GP-X391 · 74.5

**Assessment:** Stable null abort_reason is covered by a frozen successful artifact path. The mutable-object case is limited to the direct injected adapter; no persisted-object bypass is claimed.

### GP-X393 · 74.4

**Assessment:** This row was marked not_retained only because the positive result is co-located with the negative result. Bare 64-hex acceptance is already recorded exactly.

### GP-X395 · 76.3

**Assessment:** The previously accepted generator contrast supplies the exact matching positive side. It remains injected-runner metadata persistence, not a proof or CAS truth verdict.

**Parent decision:** For repair or checker admission, choose whether mismatch must refuse or may persist with explicit caller-versus-output provenance; the current candidate can refuse the stronger parsed-output-origin claim without choosing.

### GP-X397 · 77.3

**Assessment:** The same retained harness contains the successful object-shape parsing side, although it is embedded in the malformed-graph block control. The raw array exceptions show the structured-response gap. Host handling after an uncaught hook exception was not tested.

**Parent decision:** Decide whether candidate wording includes next host event survival. That would require a separate host-protocol observation; the current direct-call evidence supports only the structured-response shape defect.

### GP-X398 · 77.4

**Assessment:** The two-error retained pair is the relevant contrast and keeps the blocking exit. A same-error repetition would document intended suppression but is not needed to establish that different causes are hidden.

## Parent decisions and execution limit

Two exact behavioral controls remain conditional: the typed-Boolean paired validator check for GP-X372 if an exact two-sided route is sought, and a valid-plus-malformed native reporter check for GP-X389 if per-campaign reporting is required. Neither was executed. GP-X373 needs a schema-scope choice before a sparse-retraction success criterion is set; GP-X395 needs a generator-mismatch repair choice. GP-X397 needs a scope decision if the candidate is meant to cover host next-event behavior.

The retained fingerprint record already contains the bare 64-hex positive result for GP-X393, and the accepted 76.7 contrast supplies the matching-generator positive side for GP-X395. No files outside this report pair were edited.
