# Prior art — bounded Phase 0e review

2026-09-29. All eighteen reading-list rows are accounted for under the approved 120-minute shared cap. This completes the bounded 0e reading deliverable; it does not approve package adoption, admit a checker, establish global novelty, or close G0/G1. No software was installed, imported or executed. Exact charges, read extents, pins and unresolved questions are retained in the reports and completion tracker.

“Adopt” below recommends future reuse in the binding layer after qualification. “Ignore” for P15 means defer implementation and deep reading until M6 after G5.

| Row | Proposal | Reason and guarantee piece | Primary source |
|---|---|---|---|
| P1 MathEvidence | imitate | Exact candidate binding and narrow capability contracts; code adoption still needs corpus fit and compatibility. | [Pinned status](https://github.com/fraware/MathEvidence/blob/ea04be1a2935991758661f943a18d857ad16fafa/docs/STATUS.md) |
| P2 MathKernel | imitate | Per-claim conjunctive/alternative provenance; ordinal trust cannot authorize semantic reach. | [Evidence model](https://github.com/Staatsgeheim/MathKernel/blob/272a1644011b1a7f325f580fa96cbe3ef8fe27bb/src/mathkernel_artifacts/evidence.py) |
| P3 Dedukti/Logipedia | imitate | Track exact proof support and translation limits; filtered dependencies are not a complete axiom certificate. | [Pinned compiler](https://github.com/Deducteam/Logipedia/blob/9da47719a18e3d9995137939e789e7664c71c9e5/src/json/compile.ml) |
| P4 Trocq/Transfer | adopt | Existing Lean Relator lemmas; imitate separate coverage/preservation and domain obligations. | [Relator](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/Mathlib/Logic/Relator.lean) |
| P5 norm_cast | adopt | Proof-producing cast simplification with exact hypotheses, not generic domain widening. | [Lean implementation](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Lean/Elab/Tactic/NormCast.lean) |
| P6 Certificate tactics | imitate | Search/replay pattern and LRAT checking; unavailable polyrith and native-evaluation boundary require correction. | [polyrith](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/Mathlib/Tactic/Polyrith.lean), [native boundary](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Lean/Meta/Native.lean) |
| P7 Model theory | adopt | Fixed first-order ACF sentence transfer; no computed cutoff for a selected prime. | [ACF theorems](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/Mathlib/ModelTheory/Algebra/Field/IsAlgClosed.lean) |
| P8 Empty Hexagon | imitate | Prove counterexample-to-encoding reduction and split coverage; expose external UNSAT assumptions. | [Paper](https://arxiv.org/html/2403.17370), [historical main theorem](https://github.com/bsubercaseaux/EmptyHexagonLean/blob/d7f798ffc8deabc2f3ca1ae36e92e0250e57c205/Lean/Geo/Hexagon/TheMainTheorem.lean) |
| P9 Flyspeck | imitate | Separate search from replay and expose foreign-proof/dependency binding. | [Paper sections5–8](https://arxiv.org/html/1501.02155) |
| P10 Blueprint/Architect/Marathon | imitate | Share statement/proof graph metadata and source-first meaning review; readiness is not proof authority. | [Architect metadata](https://github.com/hanwenzhu/LeanArchitect/blob/f45833e26c68aa947044145184f8881a75392e30/Architect/Basic.lean), [review contract](https://github.com/YuanheZ/LeanMarathon/blob/e2febe2ce717ef5d8410909683f6f5b301bda4c2/agents/Target-Reviewer/docs/exec-phase/TASK.md) |
| P11 Equational Theories | imitate | Proven/conjectured and finite/general distinctions; finite implication closure and pooling. | [Evidence registration](https://github.com/teorth/equational_theories/blob/1aec8a7acf223b7c56e4830977b6e90d4ef1924b/equational_theories/EquationalResult.lean), [closure](https://github.com/teorth/equational_theories/blob/1aec8a7acf223b7c56e4830977b6e90d4ef1924b/equational_theories/Closure.lean) |
| P12 LMFDB reliability | imitate | Claim-specific hypotheses, implementation conditions and bounded coverage. | [Reliability](https://www.lmfdb.org/knowledge/show/rcs.rigor.ec.q) |
| P13 Hets | imitate | M1-only satisfaction-preserving statement/model translation. | [Primary definitions](https://kwarc.info/people/frabe/Research/CHKMRS_lfhets_11.pdf) |
| P14 AFP algebraic numbers | imitate | Exact selected-root invariants, interval semantics and guarded substitution. | [Theory](https://isa-afp.org/browser_info/current/AFP/Algebraic_Numbers/Real_Algebraic_Numbers.html) |
| P15 Numerical certification | ignore | Record alphaCertified/Interval for M6 afterG5; no deep dive now. | [alphaCertified abstract](https://arxiv.org/abs/1011.1091v2), [Interval overview](https://coqinterval.gitlabpages.inria.fr/) |
| P16 LMFDB bridge | imitate | Source/reliability/completeness and actual knowl/Mathlib links; payload acceptance unconfirmed. | [LeanBridge](https://github.com/CBirkbeck/LeanBridge) |
| P17 Magma/PARI | imitate | Effective assumptions, full/partial certification and exact input/configuration binding. | [Magma](https://magma.maths.usyd.edu.au/magma/handbook/text/416), [PARI](https://pari.math.u-bordeaux.fr/dochtml/html-stable/General_number_fields.html) |
| P18 Formal Conjectures | imitate | Reviewed goal/pointer adapters and immutable misformalization correction history. | [Statement guidance](https://github.com/google-deepmind/formal-conjectures/blob/main/STATEMENTS.md), [proof guidance](https://github.com/google-deepmind/formal-conjectures/blob/main/PROOFS.md) |

## Three G1 recommendations

1. **Both warrants, one explicit scope language.** Recommend Lean theorem evidence and separately admitted replay receipts sharing exact statement/hypothesis bindings. A theorem pointer, successful build or proof-mode label is insufficient. Formal Conjectures and CAS conditional contracts motivate this separation. Remaining evidence: corpus fit and 0c elaboration/replay cost. This is the 0e recommendation, not G1 sign-off.
2. **Reuse precise Lean tools; imitate MathEvidence first.** Evaluate linear_combination, LRAT checker functions and exact transfer lemmas for pinned binding-layer reuse. Keep external search untrusted. The inspected bv_decide replay uses nativeEqTrue, which adds an axiom: a pure kernel-reduction route or an explicitly admitted compiler/runtime boundary must be evaluated in0c. MathEvidence ideal/linear-algebra checkers remain candidates; experimental maturity, older toolchain, metadata discrepancies and compatibility preclude blanket adoption. Its rational equality theorem certification is explicitly disabled on the reviewed pin.
3. **Use Mathlib vocabulary where the mapping is sound.** Recommend pinned Mathlib definitions/typeclasses at mathematical boundaries, keeping the kernel independent. Retain explicit assumptions and bindings that are not captured by a class label: GRH, selected points, coverage, encodings and effective configuration. Cast and ACF examples show why naming a field is insufficient. Complete the corpus-to-scope mapping and account for exceptions before retiring requirement profiles; no universal clean mapping was demonstrated here.

Will signs off at G1 after the required0c/M2 evidence. Author willingness and compatibility remain unknown.

## Territory: covered components, qualified combined claim

**Claim1: covered at the semantic/theorem-component level.** Explicit theorem hypotheses and satisfaction-preserving maps already provide where a conclusion holds; LMFDB and CAS contracts disclose conditional reliability. GP should reuse that work. This conclusion does not imply those projects implement GP's entire receipt lifecycle. [Mathlib Relator](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/Mathlib/Logic/Relator.lean), [Hets](https://kwarc.info/people/frabe/Research/CHKMRS_lfhets_11.pdf).

**Claim2: partly covered; complete combination not found in this bounded review.** MathEvidence has Campaign/Episode structures, correcting the packet's absence claim. Hets provides multi-logic transport; ETP supplies campaign implication closure; LMFDB documents completeness and has formal certificate/bridge work. No reviewed source established the combined pre-formal multiworld receipt custody, admitted carrying, freshness and cover/completeness guarantee for GP's campaigns. This is a source-bounded finding, not proof of novelty. Both territory claims were not found fully covered as one system, so the whole-project pivot trigger is not met; overlapping components should still be reused.

Candidate communities: LMFDB/LeanBridge and formal number-field certificate contributors are the strongest concrete integration fit; MathEvidence maintainers are relevant for checker contracts. ETP/Lean campaign tooling and SAT/census contributors are plausible consumers of dependency/receipt exports, not confirmed demand. Roe/Sutherland, the Chavarri Villarello–Baanen–Dahmen collaboration and MathEvidence maintainers are potential contacts for Will; no contact occurred.

## Confirmed and corrected interoperability

Consume reviewed Lean/Mathlib statements and exact theorem references through pinned bindings. Consume Formal Conjectures goals only after meaning/hypothesis review; proof-location modes remain references to inspect. Consume MathEvidence candidates only after exact request/capability/version binding and separate admission.

Consume LRAT against its exact CNF through an admitted checker. DRAT may be accepted as an external input for untrusted elaboration to LRAT, followed by replay; it is not directly interchangeable with LRAT. [DRAT format](https://github.com/marijnheule/drat-trim/blob/master/README.md). Keep SAT encoding and split coverage as independent obligations.

Use graph6 for simple undirected graph interchange where appropriate. It encodes a vertex ordering, not a canonical isomorphism class or coverage proof; bind separate canonicalization/permutation evidence. [Official specification](https://users.cecs.anu.edu.au/~bdm/data/formats.txt).

Produce Lean statements and proofs where admitted; preserve externally produced LRAT and checking bindings for census negatives. Produce LMFDB-style source/reliability/completeness explanations with exact family, bounds, assumptions, TCB and receipt references. The reviewed LMFDB sources provide human conventions, not a uniform machine receipt schema. Align knowl/Mathlib links and blueprint statement/proof/declaration/dependency fields where sound. Add GP-specific scope/currentness/custody metadata beside those formats because they do not uniformly express those obligations; do not hide it in a ready/proved flag.

Foreign formats remain outside the kernel. No boundary implementation or community acceptance is established. Correct the packet's mandatory three-way LeanMarathon comparison: canonical source versus Lean is supported; an independent rendered-LaTeX comparison was not established.

## Stop and evidence limits

The finite review is complete; no default bibliography expansion is commissioned. Detailed reading, primary pins, independent checks and explicit unknowns are in:

- reports/PHASE-0E-P1-P2-P17-REVIEW.md/.json
- reports/PHASE-0E-P12-P16-P18-REVIEW.md/.json
- reports/PHASE-0E-TRANSFER-REVIEW.md/.json and TRANSFER-PARENT-REVIEW.json
- reports/PHASE-0E-CERTIFICATE-CAMPAIGN-REVIEW.md/.json
- reports/PHASE-0E-FINAL-PARENT-REVIEW.md/.json

The final parent record binds reviewed report hashes and actual shared charges. Historical source results are not fresh execution. Native trust, compatibility, actual costs, meaning mappings and full corpus expressiveness remain future gate evidence. The0a/0b decisions and capped0cspike still prevent Phase0/G0completion.

## Addendum A rows (2026-10-02)

Appended from docs/GP-0.50-POST-G2-ADDENDUM-A.md §8. Each row is UNCONFIRMED until the builder checks it against its primary source during admission. Confirmed so far: P19 (leanprover/hex v0.6.0 release, Lean v4.34.0-rc2, Mathlib 85e3a25e).

| Row | Proposal | Reason and guarantee piece |
|---|---|---|
| P19 Hex (`leanprover/hex` v0.6.0) | adopt | Verified computational algebra with Mathlib-free cores and Mathlib bridges; same layering as GP; substrate for 3a, 3b and census checkers |
| P20 LRAT-Catcher (`leansolving/lrat-catcher`) | adopt | LRAT into Lean theorems by native reflection; cube-and-conquer cover certificates; census negatives and coverage |
| P21 PBLean (arXiv 2602.08692) | adopt (evaluate in M4) | VeriPB certificates with verified encodings and certified symmetry breaking |
| P22 AutoGeneralization (`pelicanhere/AutoGeneralization`) | adopt (proposer, Lean warrants) | Proof-based widening of typeclass assumptions: the earned-but-unclaimed dual for theorem warrants |
| P23 Tau Ceti (`TauCetiProject`) | imitate | Human roadmaps, AI implementation, adversarial review against open rubrics; a model for GP's builder workflow; a possible downstream home for GP's admission theorems |
| P24 Albilich (arXiv 2607.27705) | differ | Agentic CAS harness whose verifier trusts transcripts without re-execution; the contrast case for GP's replay-only authority |
