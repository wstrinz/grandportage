# M4: Census semantics

Research memo for the GP 0.50 Phase 4 builder (rev 3 §10 M4; the Phase 4 prerequisite, post-G2 §4). Sources: rev 3 §7.2, Phase 4 and §10 M4; post-G2 handoff §4; Addendum A §4; `TCB.md`; `LIMITS.md`; and the external sources cited inline. 2026-10-03.

## Answer up front

VeriPB's certified symmetry breaking preserves **satisfiability or the optimal value, and nothing more**. It does not preserve solution counts, and it does not preserve counts up to isomorphism. PBLean checks only refutations ("this PB formula is unsatisfiable"). So certified symmetry breaking settles NONE, and through NONE it settles EXHAUSTIVE. It never settles COUNT directly.

GP does not need count-preserving symmetry breaking. **COUNT = k up to isomorphism should be decomposed** into three parts:

- k exact witnesses (EXISTS);
- pairwise non-isomorphism, shown by distinct verified canonical forms (HexGraphIso `iso_iff_canon_eq`);
- an EXHAUSTIVE claim, which is a NONE claim on the encoding with the listed objects blocked.

Every NONE carried from CNF is a carry-kind-2 rule. It needs two things:

- a Lean model-expansion theorem (each source object, or an isomorphic copy of it, yields a model of the encoding), with any symmetry-breaking WLOG argument inside it;
- a checked UNSAT receipt (LRAT-Catcher, with its cube cover as a `COVERAGE` premise).

The two weaker routes are a trusted generator (geng) and two-route agreement. They enter only as visibly labelled premises.

## 1. Symmetry breaking: existence versus counts

**What VeriPB guarantees.** Bogaerts, Gocht, McCreesh and Nordström define proof configurations by "(F,f)-validity". The redundance and dominance rules keep that invariant. The final guarantee is: either F is unsatisfiable, or v\* is the optimal value. The preprocessing output modes are DERIVABLE, EQUISATISFIABLE and EQUIOPTIMAL (JAIR 77 (2023) 1539–1589, Def. 1, Thm. 2, App. A.4: https://arxiv.org/abs/2203.12275). Nothing in that system counts solutions.

McCreesh, Nordström, Oertel and Tan say this directly. Strengthening "allows a proof to exclude some solutions", so it "cannot be used in enumeration proofs" as is (CP 2026, LIPIcs.CP.2026.43, §2.1: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CP.2026.43). Their fix is new: a `solx` rule, the conclusions `ENUMERATION_COMPLETE n` and `EQUIENUMERABLE`, and Theorem 9. Theorem 9 makes the count exact only if no strengthening step's patching touches a preserved variable.

- **My inference:** lex-leader symmetry breaking patches by applying σ to exactly the object variables. It therefore falls outside Theorem 9 whenever those variables are preserved.
- **Status:** the CP 2026 extension is implemented in VeriPB and CakePB. PBLean's paper does not mention it.

**What PBLean verifies.** PBLean takes an OPB file and a kernel-format VeriPB proof and registers a theorem "F is unsatisfiable". It checks with a Boolean checker proved sound in Lean and run by `native_decide`, so it trusts `Lean.trustCompiler`. It supports `red`/`dom` and verified encodings ("encode, soundness theorem, bridge theorem"). It pins Lean v4.28.0-rc1 with no Mathlib, and runs about 200× slower than CakePB (arXiv 2602.08692, §§3–6: https://arxiv.org/abs/2602.08692). Only one example (PHP) exercises `red`. In GP terms, PBLean yields NONE receipts in which symmetry-breaking soundness is discharged by the checker.

**When a lex-leader is complete.** Fix a variable order on the object variables V. Let G be a group of syntactic symmetries of the formula φ, meaning φ∘σ = φ. The full lex-leader for G accepts exactly the lex-least member of each G-orbit of φ's models: exactly one per orbit (Crawford, Ginsberg, Luks and Roy, KR 1996; definition restated in JAIR 2023 §5). A lex-leader for any subset of G, such as generators, accepts that same lex-least member, plus possibly others. So a partial lex-leader is complete (at least one per orbit) but not exact.

Completeness fails in three situations:

- a σ that is not a symmetry of φ, for example an encoding with a static constraint that is not G-invariant;
- two breaking predicates built on different orders;
- auxiliary variables that are not functionally determined by V, because model orbits then differ from object orbits.

SAT Modulo Symmetries (SMS) keeps exactly one representative per orbit: the lex-minimal adjacency matrix. Each pruning clause carries a permutation "nc-certificate". Its minimality check can be capped with `--cutoff`, which keeps completeness but loses exactness (Szeider, SMS survey, CEUR Vol-4116: https://ceur-ws.org/Vol-4116/invited1.pdf).

**What COUNT up to isomorphism needs.** There are two sound designs.

1. **List-based (recommended).** COUNT = EXHAUSTIVE(L) ∧ |L| = k ∧ pairwise distinct canonical forms. This needs only existence-sound symmetry breaking.
2. **Count-based.** A count-preserving certificate (CPOG, or VeriPB `ENUMERATION_COMPLETE` under Thm 9) of φ ∧ ψ, where ψ is *proved in Lean* to accept exactly one member per orbit.

   This needs the full group. For Sₙ acting on graphs that means n! constraints, so it is impractical beyond small n. I found no count-preserving certificate format for SMS's dynamic canonicity; the survey describes none.

**Conditions GP should check.** Notation: P is the property, required to be isomorphism-invariant. φ is the encoding over the object variables V plus auxiliary variables. ψ is the breaking predicate. G is the relabelling group acting on V.

| Claim | Condition the checker requires |
|---|---|
| EXISTS | A concrete object x with P(x), checked directly on x (embedding or model check). No encoding and no symmetry breaking. A SAT model is only a search hint; decode it, then check it. |
| NONE | (i) Unsat(φ ∧ ψ) via an admitted checker. (ii) Model expansion: ∀x. P(x) → ∃m ⊨ φ with m restricted to V equal to x. (iii) Orbit meeting: every G-orbit of φ-models contains a ψ-model. (iii) holds if G ⊆ Aut_syn(φ) and ψ is a lex-leader for some subset of G in one fixed order. It is also discharged if ψ was derived inside the VeriPB proof by `red`/`dom`. (iv) P is G-invariant. |
| EXHAUSTIVE(L) | Each Lᵢ ⊨ P (direct check). NONE for φ ∧ ψ ∧ ⋀ᵢ ¬block(bᵢ), with blocks over V only. Each bᵢ has a permutation certificate bᵢ ≅ Lᵢ. A wrong bᵢ costs only proof-finding, not soundness: an unblocked orbit makes the formula SAT. |
| COUNT = k | EXHAUSTIVE(L), plus \|L\| = k, plus canon(Lᵢ) ≠ canon(Lⱼ) for i ≠ j. Alternatively, design 2 above. |

LRAT-Catcher's queen-domination theorem follows the EXHAUSTIVE pattern. Its statement is that every set of at most 10 dominating queens is "a symmetry image of one of 11 listed placements", proved by blocking the listed solutions and their images and then refuting (arXiv 2607.00815: https://arxiv.org/abs/2607.00815).

## 2. Enumeration-completeness warrants

The options below are ranked from strongest trust to weakest.

- **(c′) Lean-checked EXHAUSTIVE via block-and-refute** (§1 table).
  - *Artifact:* a Lean encoder with a model-expansion theorem; LRAT leaves; a cover LRAT; the list L; permutation certificates; HexGraphIso canonical forms.
  - *Proves:* the mathematical EXHAUSTIVE claim, trusting the kernel and native evaluation.
  - *Cost:* one formalization per family; checking about 15× the fastest verified verdict (LRAT-Catcher paper); memory about 10× the certificate per `native_decide`, per its README.
  - *Pitfalls:* symmetry-breaking WLOG lemmas are the expensive part (Keller needed about 2,000 lines); blocks must be over V.
- **(d) Certified counting plus the orbit–stabilizer mass formula.**
  - *Artifact:* a certified projected labelled count N of φ with no symmetry breaking, from CPOG, whose checker and counter are formally verified in Lean 4 (Bryant, Nawrocki, Avigad and Heule, SAT 2023: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2023.6; projected version SAT 2025: https://drops.dagstuhl.de/storage/00lipics/lipics-vol341-sat2025/LIPIcs.SAT.2025.8/LIPIcs.SAT.2025.8.pdf). Alternatives are MICE (SAT 2022: https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SAT.2022.30) and VeriPB enumeration. Also needed: L with exact |Aut(Lᵢ)| (HexGraphIso proves `Aut.order` is the full group order).
  - *Check:* Σᵢ n!/|Aut(Lᵢ)| = N, with L pairwise non-isomorphic and each Lᵢ ⊨ P. This forces L to be exhaustive. It is Kaski and Östergård's standard double count (*Classification Algorithms for Codes and Designs*, 2006, "Validity of computational results").
  - *Cost:* knowledge compilation of the unbroken formula. This is feasible only where #SAT is.
  - *Pitfalls:* N must be projected onto V; auxiliary variables inflate it.
  - *Status:* compatibility of the CPOG Lean checker with GP's pin is unverified.
- **(c) Orderly generation or canonical augmentation certificates.**
  - *Status:* I found no checkable completeness artifact for McKay-style generation. One source notes nauty's generator cannot emit an exhaustiveness certificate.
  - *What exists:* verified generators, namely Marić's Isabelle Faradžev–Read scheme (IJCAR 2020, LNCS 12167: https://link.springer.com/chapter/10.1007/978-3-030-51054-1_16) and Nipkow's plane-graph enumeration. Also certificates for single canonical labellings (arXiv 2112.14303: https://arxiv.org/abs/2112.14303).
  - *SMS:* gives a checkable enumeration with nc-certificates, DRAT and blocking clauses. Its checkers are DRAT-trim plus a polynomial permutation check, neither verified in Lean (SMS survey §3.3).
  - *For GP:* SMS output feeds (c′). Its nc-certificate clauses are G-orbit-meeting by construction, so they satisfy condition (iii) once a Lean permutation checker replays them.
- **(b) Independent double enumeration (the DK E5 pattern).**
  - *Artifact:* two lists or counts from disjoint pipelines. GP can check exactly that both lists are equal as sets of canonical forms.
  - *Proves:* agreement only. That is evidence, not a warrant for completeness.
  - *Pitfalls:* shared encoder, shared definitions or a shared canonical labeller destroys independence, and agreement cannot catch a shared meaning error.
  - *Status:* the DK specifics (the Lu cell counts) are taken from rev 3's table and not re-verified here.
- **(a) Trusted generator with a TCB label** (geng, nauty 2.9.x).
  - *Artifact:* the generator version, its options, and its output.
  - *Proves:* nothing checkable about completeness. GP still checks each output against P and checks distinctness with HexGraphIso.
  - *Cost:* cheapest.
  - *Pitfalls:* user prune hooks and the semantics of option flags.
- **(e) Cross-validation on small cases** (counts matching OEIS, e.g. A000088 for graphs).
  - *Proves:* nothing at the target size. Treat it as an adversarial control.

## 3. Encoding correctness

The empty-hexagon formalization (Subercaseaux, Nawrocki, Gallicchio, Codel, Carneiro and Heule, ITP 2024, LIPIcs 309: https://arxiv.org/abs/2403.17370) works in five steps:

1. The theorem is stated with Mathlib `convexHull`.
2. Every point set is reduced, WLOG, to canonical position. This is symmetry breaking proved as a theorem; the authors found a small error in the original argument.
3. Holes are shown to depend only on triple orientations.
4. One direction is proved: every 30-point set in canonical position with no 6-hole yields a satisfying assignment τ_S of φ₃₀, the formula *emitted by the Lean encoder*.
5. The 312,418 cubes were checked by cake_lpr (25,876 CPU hours). Unsatisfiability was then *asserted as an axiom* in Lean, and cover completeness was checked by "another formula".

The authors flag two gaps. First, "we trust that the CNF … is the same one" that was checked. Second, SAT would not imply realizability (their footnote 2). The encoding and symmetry-breaking proofs took about 1,550 of 4.7k lines and roughly 300 person-hours.

The reusable pattern, now packaged by LRAT-Catcher and PBLean:

- the encoder is a Lean function;
- one theorem gives `P x → (encode n).eval (τ x)`;
- a bridge theorem `(encode n).Unsat → ¬∃x, P x` is built from that theorem and an imported `Unsat` theorem stated *on the Lean-defined CNF* (`lrat_reflect_cnf`).

LRAT-Catcher's Ramsey showcase has exactly this shape: `no_ramsey_free_of_unsat` (https://github.com/leansolving/lrat-catcher, `LRATCatcher/Showcases/Ramsey.lean`). That closes the empty-hexagon "same CNF" gap.

This is carry kind 2's model-expansion obligation discharged as a theorem. Its direction table:

- **NONE** carries back with model expansion alone.
- **EXISTS** would need the converse (every model decodes to an object satisfying P). Empty-hexagon shows the converse can fail. Use direct witnesses instead (§1).
- **COUNT** through counting needs a bijection between projected models and objects, or an orbit-level bijection.

Cross-validation on small cases is a different kind of evidence: it samples the meaning and certifies no size. GP should record it as an open premise ("encoding cross-validated for n ≤ m") under the post-G2 rule that intended-to-discharge assumptions are premises. A claim held on it stays visibly conditional.

## 4. LRAT reach

An LRAT check proves exactly one thing: "this CNF, byte for byte or as this Lean term, is unsatisfiable". `TCB.md` records `Std.Tactic.BVDecide.LRAT.check_sound` and its native trust from the Phase 0c spike, at Lean 4.32.1; it must be re-checked at the rc2 pin. A mathematical NONE or EXHAUSTIVE claim adds four obligations:

1. **Encoding correctness:** model expansion (§3).
2. **Symmetry-breaking soundness:** orbit meeting (§1 (iii)). It is discharged in one of three ways:
   - in Lean, as with the hexagon WLOG;
   - by VeriPB `red`/`dom` inside the PB proof;
   - by LRAT-Catcher "certified presolve". A RAT derivation F ⊢ F′ gives a proved transfer `F′.Unsat → F.Unsat`. RAT steps preserve satisfiability only, so this is usable for NONE and never for COUNT.
3. **Cover completeness for cube-and-conquer.** LRAT-Catcher refutes the conjunction of negated cubes (`cover_complete`) and composes it with the per-leaf `Unsat` theorems via `cover_unsat` (arXiv 2607.00815, Lemma 17). In GP, wire the cover theorem as a `COVERAGE` premise bound to the *same* base-formula digest and cube file as the leaves.
4. **Parameter binding:** the CNF is for exactly n. Its reach is that n, never "all n" and never "up to n".

Trust: LRAT-Catcher theorems carry one `native_decide` axiom per leaf and per cover. They are admitted-checker receipts with native trust (Addendum A4). LRAT-Catcher pins v4.30.0, so a port to GP's v4.34.0-rc2 pin is needed. Its `+kernel` mode removes the native axiom but embeds the CNF. Treat it as small-case only: in Phase 3a, kernel replay (`decide +kernel`) of a Hex checker exhausted memory and wedged the build machine.

## 5. Must-refuse and must-accept

| Trap | Refusing mechanism | Must-accept control |
|---|---|---|
| Timeout read as UNSAT | Only a checker-produced `Unsat` receipt mints NONE. A solver exit status or `s UNKNOWN` is not a receipt. A timed-out leaf has no leaf theorem, so `cover_unsat` cannot compose. | R(3,3) = 6 upper half: NONE at n = 6 from the LRAT-Catcher showcase encoder plus its LRAT. |
| "None found up to n" read as "none exist" | The receipt's region is the exact bound parameter set. K2 narrowing cannot widen a region (§8.1 split). A NONE for all n needs a proof, not a search. | NONE for each n ≤ N, as N separate held claims with their exact regions. |
| Unsound symmetry break used for counts | The COUNT checker accepts only the §1 decomposition, or a count certificate with a Lean exactly-one-per-orbit theorem. A model count of φ ∧ ψ alone is refused. | COUNT = 11 for graphs on 4 vertices: 11 witnesses, distinct HexGraphIso canonical forms, and block-and-refute EXHAUSTIVE using a partial lex-leader. |
| Non-exhaustive cover | The cover receipt must be `Unsat(negCubesCNF cubes)` on the bound cube file. A missing cube makes that formula SAT, so no certificate exists. Leaves must bind the same base digest. | An 8-cube cover with a valid cover LRAT (e.g. the S(4) pipeline). |
| Unchecked LRAT | Only the admitted checker's receipt counts. An `.lrat` file, a solver log or a DRAT-trim verdict that GP has not replayed is not evidence. | The same proof file replayed through the admitted LRAT-Catcher path. |
| Floating-point "verification" | Decoders reject float fields. Every census checker uses exact `Nat`/`Int`/`Rat`. Geometric EXISTS needs an exact rational witness; orientation determinants are recomputed exactly. | EXISTS with rational coordinates and exactly recomputed orientations. |
| Encoding without correctness warrant | A carry-kind-2 rule needs either a model-expansion theorem bound to the encoder used, or an OPEN cross-validation premise. Without either, the encoding's `Unsat` stays a fact about a CNF. | A NONE via `lrat_reflect_cnf` on a Lean encoder with a bridge theorem, plus a "held under premise" claim with the cross-validation premise visible. |

Two extra traps belong in the refuse set:

- a SAT model used as an EXISTS witness without decoding and a direct check (the realizability gap);
- a symmetry-broken encoding whose extra static constraint is not G-invariant.

## Ranked recommendation

| Rank | Option | Trust basis | Artifact | Cost | Use for |
|---|---|---|---|---|---|
| 1 | Direct witness check | Lean kernel or native checker | Exact object, embedding or permutation | Trivial | EXISTS; members of L |
| 2 | Verified encoding + LRAT-Catcher (+ cover) | Kernel + native_decide | Lean encoder and model-expansion theorem; leaf/cover LRAT | High formalization cost once per family; ~15× verified-verdict checking time | NONE; EXHAUSTIVE via blocks |
| 3 | List + HexGraphIso canon + rank 2 | As rank 2 + Hex v0.6.0 theorems | L, canonical forms, permutation certificates | Moderate | COUNT = k (k listable) |
| 4 | VeriPB `red`/`dom` via PBLean | Kernel + trustCompiler | OPB + VeriPB proof | Slow (~200× CakePB) | NONE where symmetry breaking is hard to prove in Lean |
| 5 | Mass formula + certified #SAT (CPOG) | Lean-verified CPOG checker (pin unverified) | Projected count; Aut orders | #SAT-limited | Independent COUNT/EXHAUSTIVE cross-check |
| 6 | Two-route agreement | Independence of routes | Two canonical-form lists | Two pipelines | Labelled premise only (DK retrodiction) |
| 7 | Trusted generator (geng) | nauty implementation, TCB-labelled | Version, flags, output | Cheapest | Labelled premise only |
| 8 | Small-case cross-validation | None at target size | Counts vs. OEIS | Cheap | OPEN encoding premise; adversarial control |

## Open questions for Will

1. **Labelled premises.** May ranks 6–7 make a census claim *held under a visible premise*, or only *open*? *Recommendation:* held under premise, with the TCB label shown in `explain`.
2. **What counts as "independent" for two-route warrants?** *Recommendation:* disjoint encoder, solver and canonical labeller, compared on HexGraphIso forms.
3. **DK V4-sector size.** If its counts are listable, rank 3 suffices and #SAT (rank 5) can wait. What are the counts?
4. **Isomorphism invariance of P.** Restrict the statement AST to invariant constructs with one generic invariance theorem, or prove invariance per predicate? *Recommendation:* restrict the AST.
5. **Incidence structures.** Represent them as 2-coloured Levi graphs in HexGraphIso, where colour preservation excludes duality. This needs a small Lean lemma relating the two notions of isomorphism, and it cannot represent repeated blocks. Is that acceptable for Phase 4?
6. **Ports and upstream work.** Port LRAT-Catcher (v4.30.0) and PBLean (v4.28.0-rc1) to v4.34.0-rc2, and offer the ports upstream? Whether PBLean will gain the CP 2026 enumeration rules is unknown, and no Szeider contact is authorized.
