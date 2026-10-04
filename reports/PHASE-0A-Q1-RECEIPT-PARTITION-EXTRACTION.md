# Phase 0a Q1 receipt and partition controls

This batch resolves the **reuse screen** for five Q1 finding obligations. The row dispositions are proposals for parent adjudication. New cases cover distinct operational observations; existing cases remain cited where the source adds a pointer or advice wording rather than a new authority mechanism.

| Obligation | Proposed disposition | Case evidence | Key distinction |
| --- | --- | --- | --- |
| 51.3 | New control | GP-X343, REFUSE/REFUSE | Zero-step route audit returns `(True, [])` without a receipt; exact SOS replay separately earns ORDERED reach. |
| 52.2a | New paired legacy controls | GP-X344, ACCEPT/ACCEPT; GP-X345, REFUSE/ACCEPT known difference | Correct ordered R composition versus ordered-only premises consumed over C. |
| 52.2b | New legacy control | GP-X346, REFUSE/ACCEPT known difference | True cover and both named R branch claims are present, but no branch receipts are recorded. |
| 58.3b | Proposed mechanism reuse | GP-X65/X66 | Producer advice overstates certificate-kind attachment; the known-name/no-current-verdict boundary already has a negative and positive control. |
| 78.4 | Proposed mechanism reuse with limit | GP-X65/X66 and GP-C01 | The retained hook test classifies a generic declared unit certificate without a receipt. Classification is not earned leaf authority. Generic and localized certificate handling are not identical. |

The exact source pointers and assertion-level comparison for each row are in `reports/PHASE-0A-Q1-RECEIPT-PARTITION-EVIDENCE.json`. In particular, GP-X181/X182 concern explicit missing premise slots, not an empty route; A16/X183/X184 concern absent cover or branches or assume branch authority, not ordered applicability or receipt presence. GP-A10-R/C isolate ordered reach outside partition composition. GP-A26 uses an unknown name, whereas GP-X65 uses a known certificate name without a current verdict.

## Oracle boundary

GP-X343 uses a current typed graph. Its route audit is true before and after receipt recording; the claim has no certificate verdict or reach before exact ordered SOS replay and gains ORDERED reach after it. The case's REFUSE observation states the no-receipt authority boundary, **not** a native held-claim verdict.

GP-X344–X346 use the retained **legacy partition consumer** with a supplied true cover: parent and branches have identical `x^2+1` loci. Exact SOS identities replay for X344/X345. The legacy consumer accepts the R-with-receipts positive, the C-with-ordered-receipts negative, and the R-without-receipts negative. In C, `i` solves `x^2+1=0`; ORDERED branch evidence cannot establish complex emptiness. The latter two are recorded as known differences between fixed expected REFUSE and observed legacy ACCEPT. A separate native epoch-1 control rejects `via_partition` as an unknown field. No admitted epoch-1 inference, durable cover receipt, published claim, or complete graph acceptance is asserted.

## Replay and preservation

The immutable baseline had 383 cases. The new immutable run has 387: **370 AGREES, 14 KNOWN_DIFFERENCE, 1 DIAGNOSTIC_OBSERVED, 1 PENDING, 1 UNSUPPORTED**. All 383 prior case SHA-256 values, expected and observed verdicts, statuses, layers, and routes are unchanged. GP-X236/X237 reason strings differ only in regenerated completion markers; normalized reasons match.

- Baseline: `reports/oracle-runs/20260928T224802105393Z.json`.
- New run: `reports/oracle-runs/20260929T003257767801Z.json`.
- Machine-readable row dispositions, observations and file hashes: `reports/PHASE-0A-Q1-RECEIPT-PARTITION-EVIDENCE.json`.
