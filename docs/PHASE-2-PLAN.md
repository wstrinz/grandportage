# Phase 2 plan — G1 ratified
2026-09-30. Authority: the retained Phase 2 handoff and DECISIONS.md. STATUS.md is the current human-readable record.

## Execution order

1. **Layer metadata first.** Keep all 459 case files and expectations byte-identical. Generate a separate, hash-bound layer registry and a validator/tests. Cases needing a judgment stay unresolved in a short list for Will; they are not silently excluded from G2. The worker owns this code and metadata lane.
2. **Deterministic snapshot.** Build the Mathlib-free typed event vocabulary and resolve the full event set before checking support. Current bindings use explicit numeric versions; retractions name warrant IDs. Exact duplicate events are idempotent. Conflicting ID contents or different bindings at the same highest version produce a named malformed/conflict result, never an arrival-order winner. Missing references remain inactive.
3. **Finite support closure.** Represent the declared claim keys, checker warrants, narrowing requests and rule instances as a finite support graph. Derived supports name particular premise-warrant IDs. Seed only active, current, successful checked evidence; iterate a monotone operator to saturation. Project reachable supports to held claims. Derive the iteration bound from domain size; no arbitrary fuel cap masquerading as completeness.
4. **Early vertical slice.** Translate approximately ten existing kernel-layer cases into the real Lean fold/held plus a narrowly specified exact Rat cofactor stub. Exercise stale/absent attempts, incomplete cover, independent support/retraction, failed retry, both merge orders, narrowing, earned consequence, conflict and a positive control. Additional program controls are tests, not new corpus cases. Publish executed results in PHASE-2-SLICE.md, at most 500 words.
5. **Proofs alongside code.** Prove truth of reached supports under the actual admitted contracts, finite reachability equivalence, and event-set order independence. Bind heldSoundStatement to the executable functions. Test/prove the lifecycle properties. Use only propext, Quot.sound and Classical.choice; no sorry, native_decide or custom kernel axioms.
6. **Finish queries and G2.** why-not reports missing current support/premises; earned reports held-but-unclaimed conclusions ranked by linked open obligations. Run every resolved kernel-tagged case. Review ambiguity eligibility before claiming 100%. Check code and documentation budgets, then have Will read STATUS.md cold.

**Conflict rule, directly confirmed by Will:** compute the complete checked held closure from the final event set. A proved inhabited-overlap conflict freezes release/promotion separately. Report conflicts and unknown overlaps; do not add an unrestricted contradiction/explosion rule. This removes arrival-history dependence without making the completeness statement conflict-filtered.

## Ownership and stops

Coordinator owns event semantics, Lean runtime/proofs, slice fidelity, public freeze application and integration. The existing Sol worker first owns layer-registry code, preservation/eligibility tests and the ambiguity list. Later worker tasks must produce a test, proof or code in separate files. No reading-only worker assignment or automatic heartbeat restart.

Logic target 500 lines, decoding 400, theorem statement/dependencies 80; stop at 750/600/120. Proofs are uncapped but must not hide executable helpers. New Markdown target 10,000 words, stop at 15,000; reports 800, slice 500, decision entries 150. Preserve the supplied handoff and its required verbatim decisions as source records. Count additions from a95fcee conservatively, including retained source Markdown.

## Review refinements

The institutions vocabulary is useful as reference semantics, not a new kernel framework. Profile currently supplies a fixed-signature sentence/model/satisfaction fragment. Means becomes theory consequence when a scope is actually the model class of that theory. contra_sound is a sufficient unsatisfiability test, not a complete decision procedure. Characteristic-changing transport cannot use generic scope inclusion, but an integral identity valid across characteristics can justify rechecking; no universal impossibility of semantic interpretation is asserted. References: [Goguen–Burstall, definition 1](https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf), [Meseguer, definitions 1 and 6](https://courses.grainger.illinois.edu/cs522/sp2016/GeneralLogics.pdf). M1 worked examples remain later work.

A08b's identity needs Ring; its emptiness consequence also needs Nontrivial. The measured Mathlib timings justify the ratified receipts-first policy but do not establish universal proof costs.

The existing supersession-order cases GP-X144/X145/X146 pass in both orders in the retained v0.37 replay. No separate failing merge-order counterexample is identified here. Use those cases plus event-permutation tests; do not claim a newly reproduced predecessor bug.

The exact public freeze patch is independently authorized. Apply only its three prepared documents in an isolated F: checkout, verify prepared content, declared LF normalization and public snapshot checks, preserve existing release tags, then fast-forward the public branch. No executable changes or new release/tag mechanics are included.
