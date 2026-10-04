# Phase 0a Q3 map and localization boundaries

This bounded batch proposes dispositions for five finding rows. Rows 79.8 and 82.4 share one source theorem and one case family. The other three mechanisms are distinct. Parent adjudication remains pending; this report closes the assigned extraction only.

| Finding row | Cases | Proposed boundary |
| --- | --- | --- |
| 79.8 and 82.4 | GP-X358–X360 | Integer-to-Gaussian operation preservation carries roots forward and EMPTY backward; source EMPTY does not move forward without an additional premise. |
| 85.5 | GP-X361–X363 | Multiplier 2 proves 3 locally belongs to (6) at 2, while ambient membership fails; direct source-ideal cofactor for 6 succeeds. |
| 85.7a | GP-X364–X365 | Translation 0 to 1 rewrites source predicates through the backward map; forward-oriented substitution gives the wrong predicate. |
| 85.7b | GP-X366–X367 | Identity equivalence has separately checked literal inclusion; a two-point swap has mapped equivalence with neither literal inclusion. |

## Exact source scope and reuse

ExpressionTransport.lean assumes an `OperationMap` preserving zero, one, add, multiply and negation. It proves root transport and target-EMPTY pullback without surjectivity. Its integer-to-Gaussian counterexample makes source-EMPTY forward transport false. The same witness resolves the proposed 79.8 and 82.4 extraction obligation; GP-A10-C and GP-X07 test different reach and image-closure premises.

Localization.lean defines local membership by a permitted power multiplier. Its `2*3=6` witness and `3 not in (6)` theorem separate local from ambient membership. GP-X17/X18 stay within a localization, A23 concerns open versus parent EMPTY, and X357 concerns exact saturation output. None tests the attempted ambient return here.

MappedEquivalence.lean uses global forward and backward inverse laws plus maps of solution sets. Its translation shows that `rewriteAlong` substitutes the backward point map. Its two-point swap supplies an equivalence without literal `Refines` in either direction. The identity-map GP-X20 and ring-isomorphism boundary A12 do not exercise those conclusions.

## Observation and limits

All ten new probes are exact **reference** arithmetic or finite predicate checks with source anchors. They record `native_lean_verdict: null` and `external_execution: false`. They do not compile Lean, invoke a native operation-map verifier, prove general parser soundness, or admit a GP 0.50 checker. In particular, the formal mapped-equivalence interface has global inverses; this batch does not equate it with runtime inverse identities modulo ideals.

The immutable baseline contains 398 cases. The new replay contains 408: **391 AGREES, 14 KNOWN_DIFFERENCE, 1 DIAGNOSTIC_OBSERVED, 1 PENDING, 1 UNSUPPORTED**. All ten new cases agree. Every prior case hash, expected and observed verdict, status, layer, and route is unchanged. The machine-readable evidence gives each row's exact premises, attempted conclusion, reuse distinction, case observations, and hashes.

- Baseline: `reports/oracle-runs/20260929T012356934782Z.json`.
- New run: `reports/oracle-runs/20260929T013956101499Z.json`.
- Evidence: `reports/PHASE-0A-Q3-MAP-LOCALIZATION-EVIDENCE.json`.

Extraction stops here under the approved narrowed closure triage plan.
