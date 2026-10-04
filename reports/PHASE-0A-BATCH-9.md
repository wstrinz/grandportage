# Phase 0a - lifecycle, merge and receipt survival

Added 35 cases, GP-X142-176: 14 acceptance controls and 21 refusals. The corpus now contains 217 cases (63 ACCEPT, 154 REFUSE expected). Final replay: 210 agreements, four known conservative differences, one diagnostic observation, one pending case and one unsupported case. All 182 earlier case files and expectations remain byte-identical. Phase 0 and G0 are not complete.

## What was covered

- X142-146 cover shared declarations, conflicting redeclarations and both branch orders for claim, edge and inference supersession. The order probes compare folded records and successor links, beyond identifier counts.
- X147-151 distinguish retracted inferences, separate surviving inferences, edge tombstones, live traffic over withdrawn edges and retirement of the rider too. A surviving clean inference is a lifecycle observation, not newly checked mathematical evidence.
- X152-159 cover contradictory withdrawal/replacement, self and dangling references, cycles that retire nothing, typed and still-untyped replacements, finite chains and unrelated parallel edges.
- X160-163 retain stale model consumers, all split successors, and the distinction between a citation amendment and a licensing change hidden as AMEND.
- X164-172 cover current, changed and legacy receipt bindings, verifier identity/version, kernel epoch, backend, semantic inputs and stale/current arrival orders. These use fabricated historical execution descriptors and do not claim that Singular ran.
- X173-176 replay section proof objects, preserve a valid section after a rejected alternative, and refuse rejected, mutated or missing proof objects.

All 93 selected regression instances pass: the complete test_store, test_supersession_noise, test_merge_assay and test_verdict_provenance files, plus five selected adversarial functions (including three parametrized supersession-order instances). No live CAS was executed. These counts overlap earlier batches and are not a whole-release test count.

The first corpus draft put the legacy receipt into a native-format graph, causing X170 to error before reaching the intended historical receipt policy. The adapter now reconstructs the original epoch-0 graph. The fixed case expectation is unchanged, and both immutable replay reports are retained.

## Important unresolved finding

The new retry audit reaches a gap that the passing stale/current merge test does not cover. Two branches carrying current identity results merge without conflict and retain both receipts, but VERIFIED_DERIVED followed by UNVERIFIED projects UNVERIFIED, while reversed order projects VERIFIED_DERIVED. This is a projection-order dependency, not evidence that the valid receipt was deleted or mathematically refuted.

Rejected section proposals have a subject-specific exception: both orders preserve the prior positive section. Four diagnostic order controls reproduce these two identity and two section outcomes. The old vocabulary does not offer generic verdict supersession. Selective warrant retraction and alternative supporting routes therefore remain design work; no expected verdict was invented to close that gap.

See RETRY-MERGE-AUDIT.json, tools/audit-retry-merge.py and LIFECYCLE-DESIGN-FINDINGS.md. The latter recommends separating attempt history from active warrants and computing support independently of arrival order, but it does not amend approved decisions or implement kernel code.

## Coverage and next work

LIFECYCLE-REVIEW.json records the extracted cases, execution names and open semantics. Current-tree inventory is 29 partial files and 339 unreviewed files, with zero claimed fully reviewed. Reading selected code, passing whole test files and source citations do not establish a complete implementation audit.

Next review: transitive support with jointly required versus alternative premises, conflicting current evidence, and the documentation/theory requirements for a total fold. Campaign harvesting still waits for the completed manifest; A24 remains pending and X53 unsupported. No original source checkout, public repository or kernel implementation was changed.
