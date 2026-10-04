# Phase 0a: candidate matrix rows and one-way contraction

Six neutral cases, GP-X312 through GP-X317, extract the two authorized families. All use the pinned ac4155787207e2847d248cffed7be871d5dcd577 oracle through a narrow offline adapter. The cases are at candidate/exact-checker and inclusion/reverse-identity layers. They do not assert a live Singular failure, materializer admission, graph bypass, or GP 0.50 held claim.

## Candidate matrix rows (Batch 75.3)

GP-X312 is the positive control: complete indexed rows yield cofactors [1,0], and exact expansion checks x = 1*x + 0*y. GP-X313 omits row 1; GP-X314 duplicates it with conflicting values. The frozen producer reports is_member=true and attaches a candidate in all three. Its missing-row zero fill and first-duplicate selection yield [0,0] in X313/X314. Independent check_membership_identity refuses both because the expansion differs from x by -x. The injected backend has can_record_verdicts=false; these probes make no native graph admission claim. Existing GP-X258/X260 cover valid/false output membership at a different persisted-graph layer, so they do not reproduce malformed producer transcript parsing.

## One-way contraction (Batch 73.3)

GP-X315 checks only the completeness inclusion I intersect Q[x] subseteq J for I=(x) and the strict upper target J=(1); the frozen elimination checker accepts that valid conclusion. GP-X316 asks for exact contraction using the same certificate; the independent reverse identity 1 in (x) fails exact expansion, so equality is refused. GP-X317 supplies the positive equality control I=J=(x) and verifies both directions. The forward certificate itself is not a false mathematical acceptance. Batch 73 materialization has a separate no-invention check and is not exercised here. GP-X141 concerns the opposite one-sided saturation gap and does not cover this elimination-certificate conclusion.

## Corpus and replay

tools/check-corpus.py validated all 358 cases and pinned source anchors. The full offline replay at reports/oracle-runs/20260928T192507564841Z.json has 343 AGREES, 12 KNOWN_DIFFERENCE, 1 DIAGNOSTIC_OBSERVED, 1 PENDING, and 1 UNSUPPORTED. All six new cases AGREE. Compared with the prior immutable reports/oracle-runs/20260928T145035306827Z.json, every one of the 352 old case files has the same SHA-256; expected verdicts, observed verdicts, statuses, routes, and layers are unchanged. GP-X236/X237 diagnostic reason text only regenerated per-run completion markers; after marker normalization the reasons match. Prior run history was not modified.

## Screen correction

The earlier kind_without_receipt adjudication screen omitted GP-X65. That existing case explicitly refuses authority from a certificate name without a current checked verdict. This extraction adds no case for that family; any transport-specific residual distinction needs a separate stated mechanism and review.

Structured observations and comparison hashes: reports/PHASE-0A-MEMBERSHIP-CONTRACTION-EVIDENCE.json. Phase 0 remains active; this extraction does not close G0 or update global coverage totals.
