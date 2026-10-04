# Phase 0a operational case candidate conversion

**Status:** parent review candidates; no corpus admission or replay.

Converted 29 incident rows into `GP-X370` through `GP-X398` under `reports/operational-case-candidates/`. All 29 validate against `corpus/case.schema.json`; every source anchor and primary frozen source SHA-256 matches. The 27 previously retained observations were referenced without re-execution. Two missing controls were run offline in scratch.

## Bounded controls

- **58.3a — floor:** One graph with untyped edge E produced `DEBT UNTYPED-EDGE:E` for `floor=DEBT` and `floor=UNSOUND_CONCLUSION`. The full responses were equal, and the graph SHA-256 remained `a2da8ba7a7f9f4e3f22b2c08094715e46044a8898ee1bd67ab25bdb1311c87c9` before and after. This is direct handler behavior, not a new oracle verdict.
- **76.8b — identifier:** Direct `cas.assert_is_identifier(cas.SINGULAR, value, "ring variable")` returned `True` for both `x` and `x\n`. Bare `x` is the positive control; the newline case exposes the lexical mismatch. No CAS process ran.
- **76.7 — prior accepted contrast:** The candidate references the existing injected-runner persistence contrast. The rendered program, parsed output, and semantic program fingerprint match across caller generators `[x]` and `[1]`, while persisted model declarations differ. No new run was made.

## Candidate inventory

| Candidate | Row | Mechanism | Observation layer | Positive control |
| --- | --- | --- | --- | --- |
| [GP-X370](operational-case-candidates/GP-X370.json) | 53.2 | source_format_schema | retained_bounded_diagnostic | recorded |
| [GP-X371](operational-case-candidates/GP-X371.json) | 54.3 | source_format_schema | retained_bounded_diagnostic | not_retained |
| [GP-X372](operational-case-candidates/GP-X372.json) | 55.2a | source_format_schema | retained_bounded_diagnostic | not_retained |
| [GP-X373](operational-case-candidates/GP-X373.json) | 55.2b | source_format_schema | retained_bounded_diagnostic | not_retained |
| [GP-X374](operational-case-candidates/GP-X374.json) | 55.3 | health_request_commit | retained_bounded_diagnostic | recorded |
| [GP-X375](operational-case-candidates/GP-X375.json) | 56.2 | health_request_commit | retained_bounded_diagnostic | recorded |
| [GP-X376](operational-case-candidates/GP-X376.json) | 56.3 | health_request_commit | retained_bounded_diagnostic | recorded |
| [GP-X377](operational-case-candidates/GP-X377.json) | 58.2 | handoff_api_contract | retained_bounded_diagnostic | not_retained |
| [GP-X378](operational-case-candidates/GP-X378.json) | 58.3a | handoff_api_contract | offline_direct_bounded_control | recorded |
| [GP-X379](operational-case-candidates/GP-X379.json) | 61.3 | digest_filesystem_custody | retained_bounded_diagnostic | recorded |
| [GP-X380](operational-case-candidates/GP-X380.json) | 63.2 | digest_filesystem_custody | retained_bounded_diagnostic | recorded |
| [GP-X381](operational-case-candidates/GP-X381.json) | 63.3 | digest_filesystem_custody | retained_bounded_diagnostic | recorded |
| [GP-X382](operational-case-candidates/GP-X382.json) | 63.4 | digest_filesystem_custody | retained_bounded_diagnostic | not_retained |
| [GP-X383](operational-case-candidates/GP-X383.json) | 65.4 | digest_filesystem_custody | retained_bounded_diagnostic | not_retained |
| [GP-X384](operational-case-candidates/GP-X384.json) | 69.3 | digest_filesystem_custody | retained_bounded_diagnostic | not_retained |
| [GP-X385](operational-case-candidates/GP-X385.json) | 64.3b | packet_attempt_binding | retained_bounded_diagnostic | recorded |
| [GP-X386](operational-case-candidates/GP-X386.json) | 65.3a | frontier_count_status | retained_bounded_diagnostic | not_retained |
| [GP-X387](operational-case-candidates/GP-X387.json) | 65.3b | frontier_count_status | retained_bounded_diagnostic | not_retained |
| [GP-X388](operational-case-candidates/GP-X388.json) | 66.2 | frontier_count_status | retained_bounded_diagnostic | recorded |
| [GP-X389](operational-case-candidates/GP-X389.json) | 69.2 | corpus_reporting | retained_bounded_diagnostic | not_retained |
| [GP-X390](operational-case-candidates/GP-X390.json) | 74.3 | transcript_postvalidation | retained_bounded_diagnostic | recorded |
| [GP-X391](operational-case-candidates/GP-X391.json) | 74.5 | transcript_postvalidation | retained_bounded_diagnostic | not_retained |
| [GP-X392](operational-case-candidates/GP-X392.json) | 76.2 | transcript_postvalidation | retained_bounded_diagnostic | recorded |
| [GP-X393](operational-case-candidates/GP-X393.json) | 74.4 | lexical_validation | retained_bounded_diagnostic | not_retained |
| [GP-X394](operational-case-candidates/GP-X394.json) | 76.8b | lexical_validation | offline_direct_bounded_control | recorded |
| [GP-X395](operational-case-candidates/GP-X395.json) | 76.3 | cas_declaration_identity | retained_bounded_diagnostic | not_retained |
| [GP-X396](operational-case-candidates/GP-X396.json) | 76.7 | cas_declaration_identity | accepted_injected_persistence_contrast | recorded |
| [GP-X397](operational-case-candidates/GP-X397.json) | 77.3 | hook_error_reporting | retained_bounded_diagnostic | not_retained |
| [GP-X398](operational-case-candidates/GP-X398.json) | 77.4 | hook_error_reporting | retained_bounded_diagnostic | not_retained |

Positive controls are explicitly recorded for 14 rows. The other 15 rows retain the prior requested control description and are marked `not_retained`; no control is inferred. Those candidates can document the observed counterexample but should not be treated as admission-ready coverage until the parent adjudicates whether a separate positive control is needed.

## Proposed observation route

A `retained_observation_only` route could resolve the cited immutable report pointers and frozen source pins, compare the recorded diagnostic with the attempted operational conclusion, and return an `OBSERVED` or `EVIDENCE_STALE` diagnostic. Its native oracle verdict would remain null. This route must not synthesize a current native ACCEPT/REFUSE, replace replay, or write to `oracle/ROUTES.json` without a separate parent decision.

## Contract and policy limits

Every candidate expects `REFUSE` of a stated operational overclaim. That field is a proposed contract, not a claim that the current oracle emitted REFUSE. In particular, the observed diagnostics do not establish a false-held mathematical verdict. Repair choices remain open for rows 55.2b (schema scope), 56.3 (post-commit retry), 66.2 (unknown status), and 76.3 (caller/output generator provenance). The candidate contracts only reject the observed overclaim and do not choose among those repairs.

The JSON manifest records each source pin, evidence pointer, actual observation layer, requested and retained positive controls, and bounded control results. No oracle route, corpus file, replay output, tracker, decision file, or live CAS state was changed.
