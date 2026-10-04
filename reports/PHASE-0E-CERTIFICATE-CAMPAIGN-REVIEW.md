# Phase 0e bounded certificate and campaign primary-source review

provisional proposals; not adoption or gate completion.

This worker reviewed only P6, P8, P9, P10, and P11. These are proposed uses of prior art, not checker admission, implementation, current Grand Portage Lean compatibility, G1 choice, or phase 0e completion. P13–P15 and final synthesis remain parent-owned.

UTC start: 2026-09-30T01:25:54Z. Primary reading and drafting ended 2026-09-30T01:40:15Z. Charged 16 minutes conservatively, including tool latency, failures, file generation, and validation; prior actual 45 minutes, cumulative 61/120. Assigned cap: 25 minutes.

## P6: Proof-producing polynomial combinations and LRAT checking

**Proposal: imitate.** Guarantee piece: Certificate replay and soundness of a local checking step; search output and the problem-to-certificate encoding remain separate obligations.

- linear_combination constructs Lean proof terms from weighted equalities over CommRing, with ordered inequality variants and coefficient conditions. Its default normalizer closes polynomial residuals; an alternative normalizer can leave subgoals. Completion and allowed axioms still need checking.

- Current pinned polyrith throws an unavailable error after the external Sage service shutdown. Its documented historical pattern is external polynomial search followed by a successful linear_combination call. This is a pattern to imitate, not an available tactic to adopt as inspected.

- LRAT.check has check_sound; verifyCert parses a certificate and checks a supplied CNF; verifyBVExpr checks the CNF obtained by reflected bit-blasting, with an UNSAT soundness theorem.

- The inspected bv_decide and supplied-LRAT replay paths both use LratCert.toReflectionProof and nativeEqTrue. Native evaluation adds an axiom asserting the evaluated Boolean is true. Checker soundness does not make this path pure kernel reduction: native compiler/runtime trust requires an explicit admission decision.

- LRAT certifies CNF UNSAT. Its bit-vector reflection theorem covers its own encoding, not an arbitrary Grand Portage campaign encoding.

**Grand Portage use:** Imitate search producing explicit polynomial combinations or LRAT receipts, then replay with binding to the precise assumptions, expression/CNF, certificate bytes, checker version, and admitted trust boundary. Candidate checker soundness and adversarial controls precede admission; no checker is admitted by this report.

**Primary evidence and read extent:**

- [S01: Mathlib/Tactic/LinearCombination.lean](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/Mathlib/Tactic/LinearCombination.lean) — lines 16–25, elabLinearCombination lines 158–219; normalizer documentation.
- [S02: Mathlib/Tactic/LinearCombination/Lemmas.lean](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/Mathlib/Tactic/LinearCombination/Lemmas.lean) — coefficient-combination lemmas; selected declarations.
- [S03: Mathlib/Tactic/Polyrith.lean](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/Mathlib/Tactic/Polyrith.lean) — historical search/replay documentation and unavailable elaborator, lines 27–59.
- [S04: src/Std/Tactic/BVDecide/LRAT/Checker.lean](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Std/Tactic/BVDecide/LRAT/Checker.lean) — check; check_sound.
- [S05: src/Std/Tactic/BVDecide/LRAT/Internal/Checker.lean](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Std/Tactic/BVDecide/LRAT/Internal/Checker.lean) — checker loop; unsat_of_check.
- [S30: src/Std/Tactic/BVDecide/Reflect.lean](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Std/Tactic/BVDecide/Reflect.lean) — verifyCert and verifyBVExpr correctness, lines 174–201.
- [S24: src/Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean) — toReflectionProof lines 26–47; search and supplied-certificate calls lines 100, 115.
- [S29: src/Lean/Meta/Native.lean](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Lean/Meta/Native.lean) — nativeEqTrue lines 37–85; axiom creation lines 76–82.

**Unknowns at the cap:**

- No Grand Portage proof replay, checker execution, adversarial testing, compatibility check, or per-check cost measurement.
- No full tactic dependency/axiom audit or polynomial-certificate schema implementation.
- Whether an admitted implementation will use kernel reduction, verified native evaluation, or another explicitly approved trust boundary remains open.

## P8: Empty Hexagon reduction and distributed UNSAT coverage

**Proposal: imitate.** Guarantee piece: Counterexample-to-CNF completeness, canonicalization, and coverage of split proof jobs.

- The relevant reduction is one-way: a general-position counterexample is canonicalized and yields a satisfying assignment to the encoding. It does not require every satisfying assignment to be geometrically realizable.

- Assn.satisfies_hexagonEncoding proves satisfaction for canonical point sets lacking the relevant six-hole property. The main theorem transports the geometric counterexample through symmetry breaking and this assignment.

- The paper describes externally checked LRAT subproblems and a separate split-coverage check; it leaves CNF identity and the external UNSAT bridge in the trust boundary.

- The pinned paper-linked itp2024 branch declares unsat_6hole_cnf and unsat_6gon_cnf as axioms. Checked-in expected #print axioms output additionally lists mathlibSorry. This is source evidence, not newly observed output; the origin of mathlibSorry was not audited.

- The inspected branch pins Lean 4.6.0. It is a bounded historical artifact, not evidence of compatibility with the current Grand Portage environment.

**Grand Portage use:** Imitate the reduction theorem and independent coverage obligation. Bind the source instance, canonicalization, exact CNF, split inventory, each checked receipt, and coverage receipt. Differ from admitting external UNSAT or unexplained extra axioms merely because the high-level theorem is formalized.

**Primary evidence and read extent:**

- [PAPER8: A Formal Proof of the Empty Hexagon Number](https://arxiv.org/html/2403.17370) — Sections 5–7: CNF reduction, split coverage, and trusted boundary; Section 6 realizability footnote.
- [S32: Lean/Geo/Hexagon/Assn.lean](https://github.com/bsubercaseaux/EmptyHexagonLean/blob/d7f798ffc8deabc2f3ca1ae36e92e0250e57c205/Lean/Geo/Hexagon/Assn.lean) — satisfies_hexagonEncoding, lines 58 onward.
- [S18: Lean/Geo/Hexagon/TheMainTheorem.lean](https://github.com/bsubercaseaux/EmptyHexagonLean/blob/d7f798ffc8deabc2f3ca1ae36e92e0250e57c205/Lean/Geo/Hexagon/TheMainTheorem.lean) — UNSAT axioms lines 9, 27; hole_6_theorem lines 29–42; expected axiom output lines 45–54.
- [S33: Lean/lean-toolchain](https://github.com/bsubercaseaux/EmptyHexagonLean/blob/d7f798ffc8deabc2f3ca1ae36e92e0250e57c205/Lean/lean-toolchain) — Lean 4.6.0 pin.
- [S17: README.md](https://github.com/bsubercaseaux/EmptyHexagonLean/blob/d7f798ffc8deabc2f3ca1ae36e92e0250e57c205/README.md) — paper/repository artifact context.

**Unknowns at the cap:**

- No external LRAT/coverage checker run or comparison of generated CNF bytes with the externally checked input.
- mathlibSorry dependency origin and later branches/releases unreviewed.
- No Grand Portage geometric/SAT encoding proposal, implementation, or measured cost.

## P9: Flyspeck search, replay, and foreign-proof bridges

**Proposal: imitate.** Guarantee piece: Separation of heuristic search from replay; exact theorem/dependency binding across computation and proof-system boundaries.

- The paper reports roughly 5,000 CPU hours for nonlinear inequality verification, the dominant reported computational verification cost among its three proof pieces. This is a historical source measurement, not a Grand Portage estimate.

- Search selects subdivisions and numerical parameters; formal HOL Light arithmetic produces replayed theorems. Parallel theorem imports used modified HOL Light and MD5 checks over statements and dependency histories.

- The Isabelle classification enters HOL Light through the named import_tame_classification assumption after manual translation. It is an explicit foreign-proof bridge, not an automatically imported HOL Light kernel proof.

**Grand Portage use:** Imitate explicit search/replay separation and binding of every imported result to its statement and semantic dependency history. Require coverage and receipt accounting for every parallel piece; expose cross-system assumptions. Use the campaign's approved digest and custody rules rather than copying its historical MD5 mechanism.

**Primary evidence and read extent:**

- [PAPER9: A Formal Proof of the Kepler Conjecture](https://arxiv.org/html/1501.02155) — Nonlinear inequalities; proof-session parallelization; tame-graph classification; Isabelle/HOL–HOL Light translation/interface sections.

**Unknowns at the cap:**

- Engineering person-hour ranking and present-day replay performance were not established.
- No numeric engine or bridge implementation inspected, executed, or adopted.
- No Grand Portage checker costs, certificate format, or single-kernel reconstruction demonstrated.

## P10: Blueprint, LeanArchitect, and LeanMarathon review conventions

**Proposal: imitate.** Guarantee piece: Readable statement/proof dependency metadata and an explicit audit of formal target meaning against the canonical source.

- leanblueprint documents lean declaration names, leanok as a claim of formalization, and uses as LaTeX dependency labels, with statement and proof environments distinguished. Visual progress metadata does not itself establish correctness.

- LeanArchitect NodePart contains text, uses/excludes, usesLabels/excludesLabels, and latexEnv. Node contains name, latexLabel, statement, optional proof, notReady, discussion, and title. NodeWithPos adds hasLean, location, and file. Node/NodePart derive JSON conversion; no interoperability run was performed.

- LeanArchitect infers dependencies from declaration constants and allows manual inclusion/exclusion. Multiple declarations may share a LaTeX label. Its inspected attribute implementation has a commented cycle-check TODO; neither the exported graph nor readiness metadata substitutes for a complete axiom/dependency audit.

- LeanMarathon's inspected reviewer contract compares the canonical problem source with all Lean theorem declarations, checks source coverage, and attempts falsification using domains, quantifiers, hypotheses, vacuity, conclusions, and mathematical objects.

- The reviewer inputs identify a problem file and Lean file. A mandatory independent third semantic comparison against rendered LaTeX was not established by the inspected contract; the packet's stronger three-way characterization remains unverified.

- The Blueprinter contract separately constrains labels, earlier-node dependencies, declaration kinds, and proof placeholders. It permits sorry/sorry_using placeholders; those workflow conventions are not proof completion or general LeanArchitect schema guarantees.

**Grand Portage use:** Imitate existing statement/proof metadata conventions and the source-first coverage/falsification review. Any Grand Portage mapping must explicitly carry scope, hypotheses, declared unknowns, proof status, and custody. Treat human/agent review as evidence of meaning review, not a kernel theorem that the source was formalized correctly.

**Primary evidence and read extent:**

- [S19: README.md](https://github.com/PatrickMassot/leanblueprint/blob/56e066d30fb7b608a63f4241fee80982d7eae3ef/README.md) — metadata commands and example, lines 165–191.
- [S20: Architect/Basic.lean](https://github.com/hanwenzhu/LeanArchitect/blob/f45833e26c68aa947044145184f8881a75392e30/Architect/Basic.lean) — NodePart, Node, NodeWithPos, lines 16–57.
- [S09: Architect/Attribute.lean](https://github.com/hanwenzhu/LeanArchitect/blob/f45833e26c68aa947044145184f8881a75392e30/Architect/Attribute.lean) — mkNode and attribute registration; cycle-check TODO.
- [S08: README.md](https://github.com/hanwenzhu/LeanArchitect/blob/f45833e26c68aa947044145184f8881a75392e30/README.md) — inference, manual dependency adjustments, readiness, export, combined labels.
- [S12: agents/Target-Reviewer/docs/exec-phase/TASK.md](https://github.com/YuanheZ/LeanMarathon/blob/e2febe2ce717ef5d8410909683f6f5b301bda4c2/agents/Target-Reviewer/docs/exec-phase/TASK.md) — Purpose; Required Inputs; Coverage Check; Falsification Attempt; Termination.
- [S27: agents/Target-Reviewer/docs/inputs.yml](https://github.com/YuanheZ/LeanMarathon/blob/e2febe2ce717ef5d8410909683f6f5b301bda4c2/agents/Target-Reviewer/docs/inputs.yml) — canonical problem_file and lean_file inputs.
- [S11: agents/Blueprinter/docs/contracts/blueprint-format.md](https://github.com/YuanheZ/LeanMarathon/blob/e2febe2ce717ef5d8410909683f6f5b301bda4c2/agents/Blueprinter/docs/contracts/blueprint-format.md) — node format, label mapping, placeholder and dependency constraints.

**Unknowns at the cap:**

- No blueprint export/import or semantic review pilot executed.
- No explicit independent three-way source/LaTeX/Lean comparison requirement located within this bounded read.
- No guarantee that manually filtered dependency graphs are exhaustive or all displayed ready nodes satisfy the Grand Portage axiom policy.

## P11: Equational Theories proof pooling and finite graph closure

**Proposal: imitate.** Guarantee piece: Separate proven/conjectured implication and refutation evidence, preserve finite/general scope, and compute bounded consequences over an explicit law inventory.

- EquationalResult records declaration identity, source location, variant, and proven status. The attribute collects axioms, marks conjectureAx dependencies conjectural, allows propext/Classical.choice/Quot.sound, and rejects other axioms. This inspected implementation is not a freshly executed audit.

- Implications have lhs/rhs and a finite flag. Facts describe one magma satisfying listed laws and refuting listed laws, yielding the corresponding cross-product nonimplications. These are mathematical witnesses, not merely graph edges.

- Extraction defaults to proven entries unless conjectures are requested. Finite/general filtering differs for implications and refutations: a finite counterexample also refutes a general implication, while a general implication applies to finite magmas. Proven outcomes are computed before conjectural completion.

- Closure builds a finite graph over the numbered laws, their negated sides, and auxiliary fact nodes; uses visited DFS/Kosaraju SCCs and bitset reachability on the condensation DAG; and detects inconsistent conjectures. Enumeration is bounded by the supplied finite inventory. DFS is declared partial; no formal termination or algorithm-correctness theorem was established.

- The explorer exposes conjecture/unknown, finite/general, explicit-proof, and export controls. The visualization/pooling layer does not transport evidence between arbitrary campaign scopes or establish custody by itself.

**Grand Portage use:** Imitate proven/conjectured separation, axiom-policy checks, explicit finite/general scope, witness-backed refutations, and finite closure over immutable admitted inputs. Keep graph-derived outcomes distinct from direct receipts and unknowns; require semantic identities and custody before campaign pooling. Do not adopt the closure executable as an admitted theorem checker on this review.

**Primary evidence and read extent:**

- [S26: equational_theories/EquationalResult.lean](https://github.com/teorth/equational_theories/blob/1aec8a7acf223b7c56e4830977b6e90d4ef1924b/equational_theories/EquationalResult.lean) — Entry and attribute registration; collectAxioms lines 90 onward; conjectureAx.
- [S31: equational_theories/ParseImplications.lean](https://github.com/teorth/equational_theories/blob/1aec8a7acf223b7c56e4830977b6e90d4ef1924b/equational_theories/ParseImplications.lean) — Implication/Facts types and accepted statement shapes.
- [S25: scripts/extract_implications.lean](https://github.com/teorth/equational_theories/blob/1aec8a7acf223b7c56e4830977b6e90d4ef1924b/scripts/extract_implications.lean) — matchFinite lines 26–30; generateOutput lines 148–165; proven/conjecture/closure options.
- [S14: equational_theories/Closure.lean](https://github.com/teorth/equational_theories/blob/1aec8a7acf223b7c56e4830977b6e90d4ef1924b/equational_theories/Closure.lean) — partial DFS lines 112–130; SCC/bitset closure lines 216–320; list_outcomes.
- [S23: scripts/graph.rb](https://github.com/teorth/equational_theories/blob/1aec8a7acf223b7c56e4830977b6e90d4ef1924b/scripts/graph.rb) — selected DFS transitive-closure methods, not the whole file.
- [S22: docs/graph_operations.md](https://github.com/teorth/equational_theories/blob/1aec8a7acf223b7c56e4830977b6e90d4ef1924b/docs/graph_operations.md) — current/new proof reduction formula.
- [UI11: Equational Theories implication explorer](https://teorth.github.io/equational_theories/implications/) — visible controls and downloadable evidence views.

**Unknowns at the cap:**

- No extraction/closure execution, termination proof, resource bound benchmark, or dashboard-to-pinned-commit verification.
- No exhaustive audit of every pooled proof/counterexample or current completion status.
- No Grand Portage closure schema/adapter, scope transport theorem, or admission implementation.

## Pinned source inventory and review limits

Repository URLs below name exact commits. Repository files were inspected as text in memory; no source was cloned, downloaded to disk, imported, built, or executed. The source inventory records relevant excerpts, not a whole-repository audit. Paper cost figures are reported historical measurements. No campaign input or Grand Portage per-check cost was measured.

- **S01** [leanprover-community/mathlib4/Mathlib/Tactic/LinearCombination.lean](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/Mathlib/Tactic/LinearCombination.lean) (58554a33d40f0f4c33fd0256dfecbc5b706480a3). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S02** [leanprover-community/mathlib4/Mathlib/Tactic/LinearCombination/Lemmas.lean](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/Mathlib/Tactic/LinearCombination/Lemmas.lean) (58554a33d40f0f4c33fd0256dfecbc5b706480a3). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S03** [leanprover-community/mathlib4/Mathlib/Tactic/Polyrith.lean](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/Mathlib/Tactic/Polyrith.lean) (58554a33d40f0f4c33fd0256dfecbc5b706480a3). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S04** [leanprover/lean4/src/Std/Tactic/BVDecide/LRAT/Checker.lean](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Std/Tactic/BVDecide/LRAT/Checker.lean) (470d5ce1400764999581fd26d5d72b00d990b0f4). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S05** [leanprover/lean4/src/Std/Tactic/BVDecide/LRAT/Internal/Checker.lean](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Std/Tactic/BVDecide/LRAT/Internal/Checker.lean) (470d5ce1400764999581fd26d5d72b00d990b0f4). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S06** [leanprover/lean4/src/Lean/Meta/Tactic/BVDecide/LRAT.lean](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Lean/Meta/Tactic/BVDecide/LRAT.lean) (470d5ce1400764999581fd26d5d72b00d990b0f4). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S07** [leanprover/lean4/src/Lean/Meta/Tactic/BVDecide/LRAT/Cert.lean](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Lean/Meta/Tactic/BVDecide/LRAT/Cert.lean) (470d5ce1400764999581fd26d5d72b00d990b0f4). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S08** [hanwenzhu/LeanArchitect/README.md](https://github.com/hanwenzhu/LeanArchitect/blob/f45833e26c68aa947044145184f8881a75392e30/README.md) (f45833e26c68aa947044145184f8881a75392e30). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S09** [hanwenzhu/LeanArchitect/Architect/Attribute.lean](https://github.com/hanwenzhu/LeanArchitect/blob/f45833e26c68aa947044145184f8881a75392e30/Architect/Attribute.lean) (f45833e26c68aa947044145184f8881a75392e30). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S10** [YuanheZ/LeanMarathon/README.md](https://github.com/YuanheZ/LeanMarathon/blob/e2febe2ce717ef5d8410909683f6f5b301bda4c2/README.md) (e2febe2ce717ef5d8410909683f6f5b301bda4c2). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S11** [YuanheZ/LeanMarathon/agents/Blueprinter/docs/contracts/blueprint-format.md](https://github.com/YuanheZ/LeanMarathon/blob/e2febe2ce717ef5d8410909683f6f5b301bda4c2/agents/Blueprinter/docs/contracts/blueprint-format.md) (e2febe2ce717ef5d8410909683f6f5b301bda4c2). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S12** [YuanheZ/LeanMarathon/agents/Target-Reviewer/docs/exec-phase/TASK.md](https://github.com/YuanheZ/LeanMarathon/blob/e2febe2ce717ef5d8410909683f6f5b301bda4c2/agents/Target-Reviewer/docs/exec-phase/TASK.md) (e2febe2ce717ef5d8410909683f6f5b301bda4c2). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S13** [teorth/equational_theories/README.md](https://github.com/teorth/equational_theories/blob/1aec8a7acf223b7c56e4830977b6e90d4ef1924b/README.md) (1aec8a7acf223b7c56e4830977b6e90d4ef1924b). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S14** [teorth/equational_theories/equational_theories/Closure.lean](https://github.com/teorth/equational_theories/blob/1aec8a7acf223b7c56e4830977b6e90d4ef1924b/equational_theories/Closure.lean) (1aec8a7acf223b7c56e4830977b6e90d4ef1924b). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S15** [teorth/equational_theories/data/README.md](https://github.com/teorth/equational_theories/blob/1aec8a7acf223b7c56e4830977b6e90d4ef1924b/data/README.md) (1aec8a7acf223b7c56e4830977b6e90d4ef1924b). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S16** [teorth/equational_theories/scripts/transitive_closure.rb](https://github.com/teorth/equational_theories/blob/1aec8a7acf223b7c56e4830977b6e90d4ef1924b/scripts/transitive_closure.rb) (1aec8a7acf223b7c56e4830977b6e90d4ef1924b). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S17** [bsubercaseaux/EmptyHexagonLean/README.md](https://github.com/bsubercaseaux/EmptyHexagonLean/blob/d7f798ffc8deabc2f3ca1ae36e92e0250e57c205/README.md) (d7f798ffc8deabc2f3ca1ae36e92e0250e57c205). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S18** [bsubercaseaux/EmptyHexagonLean/Lean/Geo/Hexagon/TheMainTheorem.lean](https://github.com/bsubercaseaux/EmptyHexagonLean/blob/d7f798ffc8deabc2f3ca1ae36e92e0250e57c205/Lean/Geo/Hexagon/TheMainTheorem.lean) (d7f798ffc8deabc2f3ca1ae36e92e0250e57c205). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S19** [PatrickMassot/leanblueprint/README.md](https://github.com/PatrickMassot/leanblueprint/blob/56e066d30fb7b608a63f4241fee80982d7eae3ef/README.md) (56e066d30fb7b608a63f4241fee80982d7eae3ef). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S20** [hanwenzhu/LeanArchitect/Architect/Basic.lean](https://github.com/hanwenzhu/LeanArchitect/blob/f45833e26c68aa947044145184f8881a75392e30/Architect/Basic.lean) (f45833e26c68aa947044145184f8881a75392e30). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S21** [leanprover/lean4/src/Lean/Meta/Tactic/BVDecide/Main.lean](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Lean/Meta/Tactic/BVDecide/Main.lean) (470d5ce1400764999581fd26d5d72b00d990b0f4). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S22** [teorth/equational_theories/docs/graph_operations.md](https://github.com/teorth/equational_theories/blob/1aec8a7acf223b7c56e4830977b6e90d4ef1924b/docs/graph_operations.md) (1aec8a7acf223b7c56e4830977b6e90d4ef1924b). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S23** [teorth/equational_theories/scripts/graph.rb](https://github.com/teorth/equational_theories/blob/1aec8a7acf223b7c56e4830977b6e90d4ef1924b/scripts/graph.rb) (1aec8a7acf223b7c56e4830977b6e90d4ef1924b). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S24** [leanprover/lean4/src/Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean) (470d5ce1400764999581fd26d5d72b00d990b0f4). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S25** [teorth/equational_theories/scripts/extract_implications.lean](https://github.com/teorth/equational_theories/blob/1aec8a7acf223b7c56e4830977b6e90d4ef1924b/scripts/extract_implications.lean) (1aec8a7acf223b7c56e4830977b6e90d4ef1924b). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S26** [teorth/equational_theories/equational_theories/EquationalResult.lean](https://github.com/teorth/equational_theories/blob/1aec8a7acf223b7c56e4830977b6e90d4ef1924b/equational_theories/EquationalResult.lean) (1aec8a7acf223b7c56e4830977b6e90d4ef1924b). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S27** [YuanheZ/LeanMarathon/agents/Target-Reviewer/docs/inputs.yml](https://github.com/YuanheZ/LeanMarathon/blob/e2febe2ce717ef5d8410909683f6f5b301bda4c2/agents/Target-Reviewer/docs/inputs.yml) (e2febe2ce717ef5d8410909683f6f5b301bda4c2). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S28** [YuanheZ/LeanMarathon/agents/Target-Reviewer/docs/deliver/issue.md](https://github.com/YuanheZ/LeanMarathon/blob/e2febe2ce717ef5d8410909683f6f5b301bda4c2/agents/Target-Reviewer/docs/deliver/issue.md) (e2febe2ce717ef5d8410909683f6f5b301bda4c2). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S29** [leanprover/lean4/src/Lean/Meta/Native.lean](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Lean/Meta/Native.lean) (470d5ce1400764999581fd26d5d72b00d990b0f4). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S30** [leanprover/lean4/src/Std/Tactic/BVDecide/Reflect.lean](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Std/Tactic/BVDecide/Reflect.lean) (470d5ce1400764999581fd26d5d72b00d990b0f4). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S31** [teorth/equational_theories/equational_theories/ParseImplications.lean](https://github.com/teorth/equational_theories/blob/1aec8a7acf223b7c56e4830977b6e90d4ef1924b/equational_theories/ParseImplications.lean) (1aec8a7acf223b7c56e4830977b6e90d4ef1924b). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S32** [bsubercaseaux/EmptyHexagonLean/Lean/Geo/Hexagon/Assn.lean](https://github.com/bsubercaseaux/EmptyHexagonLean/blob/d7f798ffc8deabc2f3ca1ae36e92e0250e57c205/Lean/Geo/Hexagon/Assn.lean) (d7f798ffc8deabc2f3ca1ae36e92e0250e57c205). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **S33** [bsubercaseaux/EmptyHexagonLean/Lean/lean-toolchain](https://github.com/bsubercaseaux/EmptyHexagonLean/blob/d7f798ffc8deabc2f3ca1ae36e92e0250e57c205/Lean/lean-toolchain) (d7f798ffc8deabc2f3ca1ae36e92e0250e57c205). Relevant declarations, documentation, or algorithm excerpts; repository not built or exhaustively audited.
- **PAPER8** [A Formal Proof of the Empty Hexagon Number](https://arxiv.org/html/2403.17370). Abstract and outline; Sections 3, 5–8, especially reduction, SAT coverage, trusted boundary, and reported costs. No exhaustive bibliography follow-up.
- **PAPER9** [A Formal Proof of the Kepler Conjecture](https://arxiv.org/html/1501.02155). Introduction; nonlinear verification, proof sessions, tame-graph enumeration/pruning, and Isabelle/HOL–HOL Light interface sections. No exhaustive bibliography follow-up.
- **UI11** [Equational Theories implication explorer](https://teorth.github.io/equational_theories/implications/). Visible controls and export links only; deployed page not tied to the pinned commit or run locally.

## Failures, accounting, and handoff

- A guessed YuanheZ/LeanArchitect repository returned 404; actual hanwenzhu/LeanArchitect was located and pinned.
- An initial PowerShell fetch setup omitted JSON conversion and fetched no sources; corrected fetches succeeded. Its latency is charged.
- Official leanblueprint docs and Flyspeck DOI access failed in the web cache; pinned repository README and primary paper HTML supplied the relevant evidence.
- Some long tool outputs were truncated; targeted follow-ups were read. Read extents above do not claim exhaustive repository audits.
- External reviewer/skill-like source files were treated as untrusted project data, not authorization or applicable instructions.

Stop at this bounded slice. Unknowns remain explicit; no bibliography chase or implementation. Parent decides integration and any separately scoped gate work.

Only the two assigned report files are written. No shared tracker, prior-art table, cases, adapters, schemas, routes, or other campaign surfaces are modified. No external contact, delegation, commit, source execution, or prototype is performed.
