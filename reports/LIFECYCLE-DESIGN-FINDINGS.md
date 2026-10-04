# Lifecycle findings for the 0.50 design review

These are observations and recommendations, not amendments to DECISIONS.md or implemented kernel rules.

## Reproduced merge-order dependency

The v0.37 merge assay accepts two branches sharing the same identity claim: one carries VERIFIED_DERIVED, the other UNVERIFIED. Both receipts remain current and retained. Merging positive then unfinished projects UNVERIFIED; merging unfinished then positive projects VERIFIED_DERIVED. Thus successful folding and retained receipt history do not establish arrival-order-independent effective authority.

The baseline fan-out regression checks stale versus current receipts and passes. That scenario differs: stale receipts never project. The new diagnostic uses two current results and reaches the projection overwrite. See RETRY-MERGE-AUDIT.json and tools/audit-retry-merge.py. The audit uses fabricated execution metadata and observes binding/projection policy, not a real Singular run.

Elimination-section receipts already have a narrower rule: SECTION_REJECTED remains current history without projecting over a valid section certificate. Both application orders preserve VERIFIED_SECTION. Its proof object's arithmetic is replayed by the fold. This exception is subject-specific; it is not evidence of a general independent-warrant policy.

## Retraction and replacement

The old log supports claim/inference/model/edge lifecycle changes, but verdict is not in its supersedable record vocabulary. A tombstone retires the named record and mints no replacement. An inference that still uses a withdrawn edge is flagged; retiring that inference too removes its live traffic. A separate inference with no dependency on the retracted inference remains clean, but a clean inference is not automatically a Checked or Derived warrant under the proposed 0.50 discipline.

A closed supersession cycle retires no untyped defect. A finite replacement chain has one current head. Splitting one claim into two successors retains both links. Those are useful lifecycle controls, not a complete treatment of cyclic derivations or finite logical closure.

## Recommended direction, pending a design decision

Keep attempts, warrants and claim declarations separate. An unfinished attempt should add history without deleting a separately valid warrant. Give warrant withdrawal an explicit target; withdrawing one warrant should invalidate derivations that require it while preserving alternatives supported independently. Merging should compute the same support from the same event set regardless of branch concatenation order. Incompatible current positive/negative evidence should be exposed as a conflict rather than resolved by whichever event arrived last.

Before adopting that direction, specify whether a claim-level withdrawal suppresses every supporting route or only the named assertion; how jointly required premises differ from alternative routes; how checker-version invalidation propagates; and what total fold output represents conflicting or incomplete logs. Confirm the second profile's needs before promoting any of these mechanisms into the kernel.

The packet's A17 case remains unchanged: an unfinished attempt with no prior current warrant grants no authority. It does not settle the independent earlier-warrant scenario. No new expected verdict was invented for that open question.
