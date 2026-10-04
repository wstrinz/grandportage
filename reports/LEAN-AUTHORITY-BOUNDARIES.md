# Lean authority boundaries — Phase 0a review

The frozen shadow explicitly does not authorize runtime claims. This review found important limits to preserve, not a reproduced false runtime licence.

## Evidence inspected

- All 317 lines of lean/README.md and all 164 lines of lean/THEORY.md, with contiguous section dispositions in corpus/DOCUMENT-REVIEW.json.
- IR.lean lines 89–138 and 231–269: Covered/lost, NonlocalReady, and soundness induction. This is a partial source read.
- Complete SemanticLoss.lean and TargetDischarge.lean source. Their imported proofs and runtime adapters are not fully reviewed.

The associated source hashes and oracle commit are retained in LEAN-BOUNDARY-SOURCES.json. No Lean rebuild, axiom audit, new kernel implementation, or campaign read was performed in this slice.

## Findings and proposed treatment

1. **Conditional induction is not end-to-end verification.** IR.sound requires leafSound, stepSound, partitionSound and familySound. Receipt validity, freshness and binding predicates are parameters; NonlocalReady requires every premise to have a current binding. For 0.50, record each checker's semantic theorem and executable discharge obligations separately. A declaration name, matching tag, or successful read-only projection must not discharge those obligations.
2. **Two meanings of loss must stay separate.** IR.lost is an expressible claim kind without a covered transport profile. SemanticLoss.Collapsed is a pair distinguished by the source observer but identified after the map. The integer-to-Gaussian exact-value theorem proves no such collision. An unavailable ordering certificate cannot establish a collision. Retain separate diagnostic fields if both notions enter the new vocabulary; no schema decision is adopted here.
3. **Field names do not instantiate field interfaces.** TargetDischarge obtains nontriviality directly from FieldTarget and derives no zero divisors using its laws and inverse premise. modTwo supplies a concrete instance. ordered_target_O takes the ordering as input. These do not construct canonical Q/R/C interpretations or derive an order on arbitrary fields.
4. **Algebraic receipts and geometric consequences have different premises.** The overview explicitly leaves endpoint interpretation, equation vanishing, unit witnesses, parser correctness and model binding outside various semantic proofs. Exact elimination contraction alone does not establish point surjectivity; localized membership alone does not establish point authority; partial coefficient rows do not establish full polynomial vanishing. Existing corpus slices should be linked to exact countermodels as each module is reviewed.
5. **Trust claims need direct evidence.** README's no-sorry statement, axiom inventory and build-speed description were read, not independently verified here. The 139 atlas decisions and one serialized interpreter example have bounded coverage. No general proof of the Python implementation is claimed.

## Remaining work

Review module-level countermodels and their runtime tests; extract minimal premise-deletion cases where existing corpus coverage is missing; inspect SPEC and remaining release/history sources; verify the existing shadow build and theorem axioms only when that supports a concrete review claim. The new-kernel feasibility spike still waits for Phase 0a/0b and an agreed cap.

227 cases and their latest observed outcomes are unchanged. This documentation-only slice requires ledger integrity checks rather than another identical oracle replay. Phase 0a remains incomplete; the pending source manifest blocks only the campaign sweep.
