# Phase 0a reconciliation notes

Status: evidence reconciliation proposal at private branch codex/phase-0. No existing case, adapter, ledger, gate, oracle, source manifest or public repository was changed. The [matrix](PHASE-0A-CLOSURE-MATRIX.json) is the line-item record; the [queue](PHASE-0A-REMAINING-QUEUE.md) is the action list.

## Method and boundary

- Compared the exact git ls-tree path set at ac4155787207e2847d248cffed7be871d5dcd577 with SOURCE-INVENTORY: both have 368 paths with no set difference.
- Compared git rev-list over all parents of the pin with HISTORY: both contain the same 244 commits. First-parent has 224; all refs have 247, leaving three commits on other refs outside this boundary. Index completeness as a list does not establish incident review.
- Enumerated unique paths deleted in pinned reachable history with git log --diff-filter=D: 185, including exactly the 29 deleted test paths in the prior review and 156 other paths. Those 156 have not been silently credited.
- Matched case source pointers and structured review records to inventory paths using exact JSON pointers. Direct source links are not proof that every incident in a file was extracted. Each Batch 51–85 paragraph is retained with its reported observation, route and execution limit. No source reread or broad test was performed.
- Copied all 352 existing expectations and actual oracle observations into matrix oracle_cases. Reading, incident extraction and execution have separate fields. This package did not run the oracle.

## Reconciled counts

| Item | Count | Interpretation |
|---|---:|---|
| Direct pinned-tree case source links | 288 links on 39 paths, naming 267 unique case IDs | Covered occurrences only, not full source review. |
| Deleted-test explicit extracted mappings | 67 functions | These prior rows name case IDs; neutral equivalence and scope still need review. |
| Deleted-test alleged duplicates lacking IDs | 42 functions | Unresolved mappings; the old covered-by-existing label cannot stand without exact case IDs and equivalence arguments. |
| Deleted-test other exception dispositions | 117 functions | 83 diagnostic-only, 28 blocked and 6 display-only; each has an exact audit row. |
| Batch 51–85 | 245 rows | 46 proposed new-case candidates, 2 proposed existing-case mappings, 38 bounded non-incidents, 81 later-design routes, 16 repairs, 3 corrections, 1 unresolved formal-source reading item and 58 reading/execution extent records. |
| Named remaining work | 113 entries | All classified in the matrix; 11 old reading requests have later reading evidence, without complete extraction credit. |

## Proposed duplicate equivalence and limits

- **Batch 73.4 → GP-X258 and GP-X260.** The materializer's output-membership decision attempts to admit output evidence from the source ideal. The essential premise is exact generator membership; invalid arithmetic with fresh producer metadata is the failure mechanism in GP-X260, and valid membership is the positive control GP-X258. This is a proposed mapping for the no-invention direction only. The separate completeness direction is queued as P0A-N031.
- **Batch 75.7 → GP-X269, GP-X270, GP-X273 and GP-X274.** The attempted conclusion is exhaustive parent coverage by declared branches. The essential premises are the actual branch loci, including open guards or selected embeddings. Ideal-only radical containment omits those conditions; the cited cases contain positive and negative controls for the two mechanisms. Backend evidence itself remains separately unverified.
- Batch 51 ordered transport is queued distinctly: A01 concerns nonsquare-field scope, so topic overlap does not prove equivalent premises or failure mechanism. Batch 78's declared-certificate-kind control likewise lacks an earned receipt and is separately queued.
- Batch 52 demonstrates a legacy partition consumer accepting ordered-only C branch evidence under a supplied true cover and accepting R composition without receipts. Current epoch-1 schema rejects via_partition. This bounds the finding; it does not establish a current admitted false-held graph.
- Batch 75 malformed cofactor matrices yield false positive **candidate** certificates; the independent exact checker refuses them. The producer parser needs its own operational candidate. GP-X260 shows exact false-membership refusal and cannot be cited as proof that the parser is sound.
- The 42 deleted-test covered-by-existing labels have no case IDs. Their notes may suggest similar mechanisms, but this package treats all 42 as unresolved rather than inventing duplicate mappings.

## Corrections and contradictions

- REVIEW-COVERAGE and older next-pass prose include stale exception counts. The latest immutable oracle result is 337 AGREES, 12 KNOWN_DIFFERENCE, 1 DIAGNOSTIC_OBSERVED, 1 PENDING and 1 UNSUPPORTED. Six known differences are ACCEPT→REFUSE and six are REFUSE→ACCEPT; they are not all conservative refusals.
- Batch 58 claimed MCP already had partial inventory credit. Batch 60 documented that MCP and CLI still had unreviewed labels and corrected both to partial. Use current 171 partial / 197 unreviewed counts.
- Batch 61 called a source-directory synthetic verifier failure a packaging defect. Batch 62 executed the verifier in the intended archive layout and withdrew that diagnosis. The CRLF digest inconsistency remains.
- The history index marks all 244 commits unreviewed although selected diff and release reviews exist. Keep metadata status separate from later content-review pointers; neither blanket conclusion is justified.
- The deleted-test review says all 226 functions received first-pass dispositions, but 42 claimed existing-case duplicates lack IDs. This is a traceability gap in prior evidence, not a modification of that ledger.
- A03a remains DIAGNOSTIC_OBSERVED and is not an end-to-end false-held demonstration. A24 remains PENDING for a concrete authorized model/source. X53 remains UNSUPPORTED because no dimension-credit claim kind exists. Their REFUSE expectations stay fixed.

## Confidence and ownership

Boundary set comparisons and copied oracle outcomes are high confidence. Incident completeness is low where only inventory or commit-index metadata exists. Batch routes are bounded, medium-confidence proposals tied to their reported diagnostics. Named follow-up classifications are provisional where a later batch may have satisfied reading but not extraction. The originating thread retains final duplicate, mathematical, scope-exception and completion decisions.

