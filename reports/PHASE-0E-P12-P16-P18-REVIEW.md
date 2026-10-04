# Phase 0e: P12/P16/P18 and parent review of the first worker slice

2026-09-29 local date. Public sources reviewed 2026-09-30 UTC. Recommendations are reading-stage proposals, not component adoption, checker admission or a completed Phase 0 gate. No software was installed, imported, cloned or executed.

## P12 and P16: LMFDB — imitate; consider a boundary adapter

[LMFDB's source/reliability/completeness overview](https://www.lmfdb.org/rcs) distinguishes computation provenance, conditional or heuristic reliability and coverage of finite families. These are useful human-facing categories; the reviewed sources do not establish a uniform machine receipt schema.

[Rational elliptic curve reliability](https://www.lmfdb.org/knowledge/show/rcs.rigor.ec.q) makes qualifications claim-specific: implementation correctness matters for completeness, optimal-curve choices are not always rigorous, and analytic-rank conclusions depend on rank/conductor conditions. A single label cannot replace a proposition's actual qualifications.

[Elliptic curves over number fields completeness](https://www.lmfdb.org/knowledge/show/rcs.cande.ec) describes field-dependent conductor bounds and distinguishes modular-curve completeness from completeness of all curves when modularity is unknown. Despite the URL's abbreviated title, this page concerns number fields, not merely curves over Q. A proposed GP export should bind the exact family, field, bound and assumptions; that export shape is our proposal, not an existing LMFDB standard.

[David Roe's June 29, 2026 slides](https://math.mit.edu/~roed/writings/talks/2026_06_29.pdf), read as a twelve-page presentation, describe nonuniform reliability knowls and future Lean proof downloads for selected claims, with completeness difficult. The talk title is “LMFDB: Past, Present and Future”; “Bridging Lean and the LMFDB” names the workshop. June plans do not establish September implementation status.

The [workshop page](https://multramate.github.io/lean-lmfdb/) identifies an actual June 29–July 3, 2026 workshop and links LeanBridge. Its Alain Chavarri Villarello abstract reports certification of hundreds of number-field entries with Anne Baanen and Sander Dahmen. This is a source-reported result, not an independent build. It prevents a blanket claim that formal data certificates are merely future plans.

The current [LeanBridge README](https://github.com/CBirkbeck/LeanBridge) describes a blueprint generated from LMFDB knowls, linking definitions through DEFINES and theorems through citations to Mathlib declarations. This offers a concrete integration convention; it does not itself establish GP's pre-formal multiworld custody and completeness guarantee. Mutable main was inspected, without an immutable revision or build check.

Proposed consumer: LMFDB/LeanBridge number-theory contributors. GP could offer exact statements/Mathlib declaration links, input and checker/version references, disclosed assumptions and a bounded completeness assertion with its receipt. A generated explanatory knowl is plausible; community acceptance of a payload or workflow remains unknown. Roe and Sutherland are documented bridge contacts, and Chavarri Villarello's collaboration is relevant to certificate formats. Will makes any contact; none occurred.

General source wording was accessible, but the section source knowl rcs.source.ec.q encountered an access challenge and was not bypassed. No uniform per-section implementation audit was attempted.

## P18: Formal Conjectures — imitate; selectively consume after meaning review

The [repository README](https://github.com/google-deepmind/formal-conjectures) separates evolving statements from immutable benchmark versions; corrected misformalizations enter later benchmarks. The [May 2026 paper abstract](https://arxiv.org/abs/2605.13171v1) describes a collaboratively audited statement benchmark, with AI proofs/disproofs helping expose incorrect formalizations. Only the abstract and identity were read for the paper, not its full twenty-one pages.

[Statement review guidance](https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/STATEMENTS.md) calls for comparing hypotheses, quantifiers, definitions and boundary cases. Successful elaboration does not establish that a goal expresses the intended campaign problem. [Proof review guidance](https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/PROOFS.md) requires checking the actual declaration and dependencies; a sorry-bearing scaffold is not a proof, and native_decide dependencies need disclosure. These are read policies, not an executed Lean audit.

[Contribution metadata](https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md) distinguishes formal_conjectures, lean4 and other_system proof locations. Such a pointer is candidate evidence, not a GP warrant. Follow the exact declaration/statement, pin the environment and inspect its axiom boundary under an admitted route. Other proof systems need a separate admission boundary. Some contribution prose mentions informal solutions while proof guidance requires formal proof; the stronger admission requirement must not be inferred from a label alone.

The Hadwiger–Nelson example is related to unit-distance problems, but no exact match to Will's campaign specifications was established. Whole repository campaign coverage was not searched. Repository guidance was mutable main retrieved during this session; the attempted current-commit API lookup was unavailable. Before package adoption, pin exact statements and dependencies. README licensing distinguishes software Apache-2.0 from other materials CC-BY-4.0 and potentially distinct third-party terms; no content/code was incorporated.

Proposal: selectively consume exact reviewed goals and proof references in the binding layer, and imitate immutable correction history for M5. Direct automatic conversion from a catalogue category into held authority is unsupported.

## Independent parent review of P1/P2/P17

Worker reports PHASE-0E-P1-P2-P17-REVIEW.md/json are accepted as bounded primary-source reading, with no execution or adoption claim. Their three local constraint hashes match current files. The full detailed capability catalogue remains worker static inspection; parent independently checked these consequential claims:

- P1 pinned Engine.lean declares Campaign and Episode. The packet's “no campaign state” description is contradicted by actual structures; this does not prove operational maturity or complete predicate binding.
- P1 pinned STATUS.md and rational_equality capability explicitly exclude rational equality theorem certification on the production Lean 4.14 path and describe the sorryAx problem. This is maintainer disclosure, not parent reproduction.
- P2 pinned evidence.py distinguishes conjunctive support within a path from alternative paths, retains diagnostics and ancestry ceilings, and ranks symbolic above interval_certified. The packet's simplified ladder description omits real claim structure. Ranking still cannot by itself specify semantic scope.
- Official Magma ClassGroup and PARI bnfinit/bnfcertify contracts independently confirm effective global bounds, GRH conditionality and partial versus full certification. This supports the approved A27 amendment, without changing any case or claiming a runtime receipt.

Parent fetched the four pinned P1/P2 files into memory after web cache misses; no source was saved/imported/executed. Exact byte hashes are recorded in the companion JSON. Other worker configuration, licence and detailed checker claims remain attributed source inspection pending any adoption-specific qualification.

## Scope and next boundary

Six of eighteen rows now have provisional verdicts, not six adopted packages. Territory claim 1 is partly covered by explicit conditional scopes and human reliability conventions. The combined territory claim 2 is not established by these sources; this is “not found in this bounded slice,” not a novelty proof. Final territory, all interop surfaces and three G1 recommendations require the remaining rows and 0c evidence where specified.

Parent reading began 00:49:02 UTC; uninterrupted timing includes prior-source orientation, tool latency, failed fetches, worker review and synthesis. The companion JSON records the conservative whole-session charge through artifact serialization. Worker actual charge is 14 minutes; neither charge resets the shared 120-minute budget.
