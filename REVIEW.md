# WIP review guide

2026-10-02. This checkpoint reviews Grand Portage 0.50 through Phase 2. Will closed G1 by a documented coverage exception and ratified G2 after all 79 kernel-tagged cases executed through the native Lean kernel; the executed slice, kernel proofs and TCB are the main new review targets. Read [STATUS.md](STATUS.md) for current progress. Review does not imply production soundness, checker admission or permission to change corpus expectations.

Review branch: [codex/phase-0](https://github.com/wstrinz/grand-portage-workspace/tree/codex/phase-0), merged into master in the approved review shadow repository. Master also carries the v0.37 package and history; its v0.37 review brief is [HISTORY/REVIEW-v0.37.md](HISTORY/REVIEW-v0.37.md). For Phase 2, start with [the executed slice](reports/PHASE-2-SLICE.md), [TCB.md](TCB.md), phase2/lean/GP50 and the [closeout](reports/PHASE-2-CLOSEOUT.md).

## Suggested reading order

1. [SPEC-CORE.md](SPEC-CORE.md): guarantee, statements/scopes/warrants, lifecycle and K1–K6.
2. [Phase 1 parent review](reports/PHASE-1-PAPER-PARENT-REVIEW.md): concrete expression proposals, exclusions, unknowns and G1 boundary.
3. [Contract checklist](reports/PHASE-1-CONTRACT-CHECKLIST.md): obligations that truth-of-held soundness alone does not establish.
4. [Typed soundness goal](phase1/lean/SoundnessStatement.lean) and [package README](phase1/lean/README.md): elaborated proposition, unimplemented runtime slot and the proved universal weakening lemma.
5. [Adoption proposals](reports/PHASE-1-ADOPTION-PROPOSAL.md), [scope map](reports/PHASE-1-SCOPE-MAP.md) and [PRIOR-ART.md](PRIOR-ART.md).
6. [TCB.md](TCB.md), [spike completion](reports/PHASE-0C-COMPLETION.md) and the two isolated packages under spikes/.

## Questions for review

- **Guarantee and size:** Is the abstract Mathlib-free kernel a useful boundary between evidence custody and domain semantics? Do its proposed guarantees justify a separate component?
- **Scope versus model:** Are ambient mathematical assumptions correctly separated from selected points, branches, finite universes and regions? All finite object/index/path quantifiers belong in statement/model predicates; K2 must not change a search region. Object-changing relations require separately sound rules.
- **Lifecycle:** Is support by specific immutable warrant IDs sufficient for retraction, staleness, failed retries and independent support? Can the actual total fold remain small and deterministic with event-set resolution with explicit numeric versions?
- **Earned closure:** Is a finite declared claim/rule-instance domain useful enough? What precise completeness property should accompany soundness, so an always-false held predicate cannot satisfy the product contract?
- **Bindings and admission:** What exact statement/model/hypothesis/receipt/byte/version checks are needed across the profile and proof-binding boundaries? A matching ID/hash, citation, tool label or theorem pointer is insufficient.
- **Conflict handling:** Is proved inhabited overlap plus contradictory statements the right basis for freezing new promotion? Unknown overlap must remain unresolved.
- **Interop:** Are the proposed two warrant forms, MathEvidence contract imitation and separate pinned Mathlib bindings the right choices? Which exact existing components meet a required contract?
- **G1 coverage:** Are the recorded limits acceptable for proceeding, or does one expose a structural flaw worth resolving first?

## Coverage and gate status

The existing inventory distinguishes 76 documented-incident/correction/group owners from 39 operational diagnostic/control/design owners. Excluding recorded MEANING entries yields 67 primary paper rows and 37 separately accounted rows. Children, repeated witnesses and cross-occurrences do not add samples. These are descriptive owners, not an independent empirical incident population.

Parent-reviewed primary expression proposals: **52 true, 8 outside, 7 unresolved**. Refusal assessments remain **19 conditional true, 11 false, 37 unknown**. Representation is not prevention, an implemented checker or proof that a historical result was wrong. The two original worker reviews and the parent qualifications are retained separately.

A strict 80% minimum would require 54/67 positives. Will accepted the 52/67 exception and authorized Phase 2; the strict numerical screen remains below 80%. The eight exclusions cover source interpretation/priority, external reviewer behavior and product availability. Seven composite owners remain unresolved. Known-high-cost stale-prose incident JC-B005 has a written exclusion reason; its cost/shipping are source-attributed. Cost-based Phase 0 pivot percentages remain indeterminate, as ratified at G0.

No checker or package is admitted. Ordinary theorem warrants would exclude generated native-result axioms by default under the ratified policy. A separate native checker may have explicit trust assumptions, subject to its own admission.

## What the Lean evidence establishes

The Mathlib-free feasibility package exercises toy exact binding, freshness, scope narrowing, process transport and rational cofactor replay. Its 459-case-sized workload uses trivial equalities; it is not semantic execution of the regression corpus.

The separate pinned Mathlib package proves the actual A08b/A05 mathematical obligations. It is not a generic statement translator or theorem-to-scope binder. Imported dependency caches were reused; timing varies with contention.

Native LRAT checking succeeded under its explicit generated Boolean-result axiom/compiler/runtime boundary. Bounded attempts at pure-kernel reduction failed at this pin; that is neither a global impossibility result nor an axiom-free replay claim.

The Phase 1 soundness proposition elaborates and weakening is proved without axioms. The production fold, held predicate, decoder, lifecycle properties and earned-closure completeness are still to be implemented/proved.

## Reproduction boundary

Tracked reports contain source hashes, observations, pins, scripts, proof sources and immutable replay files. The 89 private verbatim campaign harvests, predecessor checkout, dependency caches and build products are deliberately excluded. Many source paths refer to the original Windows workspace.

The local corpus and incident validators require those source/custody inputs. A fresh clone provides the review artifacts and standalone Lean sources, not all historical replay prerequisites. See each package README for build details; full source-cold dependency build timing was not measured. There is no newly executed oracle/campaign result in this publication checkpoint.

Please keep mathematical defects, missing contracts, intended-meaning problems, host/surface defects and reproduction limitations distinct when assessing coverage. All 459 existing case expectations and immutable observations remain fixed unless Will explicitly approves a semantic correction.
