# GP 0.50 — post-G2 handoff: Phase 2.5 through G5

**Date:** 2026-10-02 · **Owner:** Will · **Applies to:** workspace `master` / `codex/phase-0` → Phase 2.5 onward
**Authority:** This document records Will's post-G2 decisions and authorizes Phase 2.5 and Phase 3a. It amends the revision 3 packet, the Phase 2 handoff and `DECISIONS.md`; where they conflict, this document wins. Copy §1 into `DECISIONS.md` verbatim. Phases 4, 3b and 5 are planned here, and each opens only when its predecessor gate passes.

---

## 0. Plain-language summary (the model for `STATUS.md`)

Phase 2 built a small Lean kernel and proved it does its job. Given admitted checkers, it holds exactly what the evidence supports, whatever order events arrive in, and retraction, retries and conflicts behave correctly.

What it has not yet done is the thing GP exists for. Every Phase 2 test had either a trivial or a toy notion of "world", and the one real checker ignored context entirely. Carrying results between worlds is still untested.

The next stretch makes it real:

- **Phase 2.5** makes three kernel-semantics changes now, because later gates freeze the kernel. It defines what "kernel" means as a package; it splits `Profile` so executables never need Mathlib; and it makes contexts universe-polymorphic, so a context can be an actual field.
- **Phase 3a** builds the first real profile: polynomial systems with rational coefficients, where a certificate's reach is computed from its denominators. An identity with integer coefficients holds over every field. One that divides by 2 says nothing about characteristic 2, which is exactly where the Fano plane exists.
- **Phase 4** adds a census profile, as the test of whether the kernel really is domain-independent.
- **Phase 3b** adds the heavier algebra: ordered fields, number fields and real algebraic points.
- **Phase 5** runs the u(22) pilot and the comparison against a notebook baseline.

Two process rules change. Corpus cases now run through one shared frontend instead of a hand-written bridge per case. G3 counts only the cases owned by the minimal profile, while checking that no profile case anywhere is wrongly accepted.

---

## 1. Post-G2 decisions (ratified by Will, 2026-10-02)

1. **Scope/statement criterion.** Scope contains only what the profile's `le` can compare without evidence: characteristic sets, field-class flags, and standing named hypotheses such as GRH.
   - Anything whose inclusion needs a certificate (loci, ideals, regions, relaxations, branches) belongs in the statement and moves only by K3 rules with checked relation certificates.
   - Relaxation (v0.37 NECESSARY_CONDITION) is a K3 inclusion rule, with exactly one encoding.
   - Context splits (kernel `Cover`) and object splits (K3 cover rules) are distinct, and both are legitimate.
   - Phase 2 harnesses that put contexts in statements (`ContextReach`) or regions in scopes (`ConditionalRoutes`, `ConditionalPointRoutes`) remain valid kernel tests. They are not normative profile encodings.

2. **Statement signature and computed reach.** An algebraic statement's coefficient ring is ℤ[1/S_stmt], where S_stmt is the set of primes dividing any denominator in the statement.
   - The statement is meaningful only in fields whose characteristic lies outside S_stmt. A claim whose scope leaves that domain is ill-formed.
   - Certificate reach is computed from the certificate, never declared (§3.3).
   - An F_p-replayed certificate reaches exactly {p}.
   - Characteristic specialization is therefore reach, not a transport.

3. **Contexts are models; Profile is split.**
   - `Profile` splits into a Mathlib-free, executable `ProfileOps` (`Stmt`, `Scope`, `same`, `same_sound`, `le`, `contra`) and a universe-polymorphic semantic `Profile.{u}` extending it (`Ctx : Type u`, `mem`, `Holds`, `le_sound`, `contra_sound`).
   - Executable kernel code takes `ProfileOps`; theorems take `Profile`.
   - `Overlap.witness` returns profile-chosen data, and its soundness states that a common context exists.
   - The target algebraic context is Mathlib's `Theory.field.ModelType`.
   - Rationale: `Means` is literally truth in every model the scope denotes, with no kind-partition side condition, and the institution correspondence stays exact.

4. **Signature morphisms: no kernel concept.**
   - ℚ-coefficient statements already range over every suitable field, so ℚ → ℚ(i) base extension is K2 (GP-C01).
   - GP-A02 refuses because the statement's signature lacks i and no rule supplies it.
   - Number-field statements (3b) use a fixed signature ℤ[1/S][t]/(m). Translating a statement into that signature is a profile K3 rule of carry kind 1.
   - Promotion into the kernel happens only under D9.

5. **Ledger conflicts.** The kernel stays strict. A log is malformed, with no partial snapshot, if it contains any of:
   - conflicting same-version current bindings;
   - conflicting warrant contents under one ID;
   - retraction plus supersession of one target.

   Robustness lives in an adapter commit/merge guard:
   - an append or merge lands only if the resulting log still folds;
   - ID allocation is branch-safe (namespaced or content-derived);
   - collisions surface as merge conflicts, resolved before landing.

   Two of the three collision types cannot be repaired by later appends, so the guard is mandatory before any multi-writer use. It is required at Phase 5 entry.

6. **Kernel freeze.** Phase 2.5 splits the Lean package into `Kernel`, `Stub` and `Run`. `Kernel` holds what is domain-independent and soundness-critical, by the rev 3 §6.4 boundary test. Phase 2.5 re-measures the D8 budget on `Kernel` only and pins it in `KERNEL-PIN.json`. At later gates, "kernel unchanged" means the pin is unchanged, or each change is logged with its reason in `PROMOTIONS.md`.

7. **Checker admission.**
   - Each checker is a Mathlib-free executable replay, admitted with a one-time soundness theorem in the binding package, adversarial controls, and a `TCB.md` entry.
   - Receipts remain the per-claim currency.
   - Per G1 decision 3, overlapping tools must be named. For algebraic certificates, Mathlib's `linear_combination` checks the same identities, but it costs Mathlib-scale elaboration per claim (the 0c measurement: 40–150 s) and computes no reach. It remains the upgrade path for durable claims.

8. **Execution rule.**
   - Corpus cases execute through one shared case-to-profile frontend.
   - Bridges may construct only profile inputs: the statement AST, the scope, and raw certificate or relation-certificate bytes.
   - Bridges never construct events, warrants, admission results or success flags. Checkers and the proposer produce events.
   - A case that requires case-specific code is reported as an expressiveness loss, never as a pass.
   - Per-family runner scripts are retired for profile work.

9. **Proposer.** An untrusted adapter proposes claim declarations and warrant events:
   - the widest claim each held receipt's reach allows;
   - K3 instances over declared statements with available relation certificates;
   - K2 narrowings to scopes named by open obligations.

   It writes through the commit guard and affects authority only through admitted checkers and rules. The earned surface ranks results by the open obligations they touch and shows at most five by default.

10. **Phase order: 2.5 → 3a → 4 → 3b → 5.**
    - 3a is the Nullstellensatz regime.
    - 4 is census, the portability test.
    - 3b covers ordered/SOS, number fields, selected real algebraic points and sections.
    - G4 is the most informative architectural test, so it comes before the heaviest builds.
    - 3b still precedes the pilot, because u(22) and Cloquet need real algebraic points.
    - D10's spirit is kept: census comes immediately after a genuinely minimal algebraic profile.

11. **Gate ownership.**
    - A sidecar, `corpus/GATE-OWNERS.json`, assigns every profile-layer case to one of: 3a, 3b, census, or campaign-op. Campaign-op cases are admitted only when a live campaign needs that operation.
    - The policy matches the layer tags: expectations and bytes are unchanged, and ambiguous cases go to Will.
    - G3a requires 100% of 3a-owned cases to pass, plus zero false ACCEPTs across all profile cases. G3b applies the same rule to 3b.
    - Campaign-op cases remain regression material, not minimal-profile scope.

12. **Visibility and release.**
    - The workspace stays public for reviewability and will later go private.
    - CI certification and toolchain portability are deferred until then.
    - At G3a, the builder prepares `v0.50.0-alpha` for the public `wstrinz/grandportage`, per `reports/PUBLIC-INTEGRATION-PLAN.md`. Publication still needs Will's explicit approval at that time.

13. **Unchanged and authorized.**
    - Theorem transport licenses only exact premise records.
    - Every K3 rule declares `carry_kind`.
    - The Phase 2 process caps carry over (§8).
    - The Fano realizability cases (§3.6) and the census must-refuse set (§4) are authorized new corpus cases. Any other new case needs Will.

---

## 2. Phase 2.5 — pre-freeze kernel window

Goal: make the kernel-semantics changes that later gates forbid, while the Phase 2 proofs are fresh. No profile work.

### 2.5a Package split (§1.6)

Classify every module in `phase2/lean/GP50` by the boundary test:

- **`Kernel`:** generic over `Profile`/`Admission` and soundness-critical.
- **`Stub`:** mentions `PolyStub`, `Span` or a concrete test profile.
- **`Run`:** JSON presentation and runner mains.

The expected `Kernel` contents are `Events`, `Decoder`, `Entry`, `Closure`, `Runtime`, `Semantics`, `Narrowing`, `Cover`, `Conflict` and `Queries`, plus their proof and completeness modules. Report the list, and send ambiguous modules to Will.

Re-run the budget on `Kernel` only (logic/decoder/statement) and record the actual numbers. Then write `KERNEL-PIN.json` with per-file SHA-256, the toolchain and the commit.

### 2.5b Profile split and universe polymorphism (§1.3)

- **`ProfileOps`:** in `Type`, executable and Mathlib-free. Fields: `Stmt`, `Scope`, `same`, `same_sound`, `le`, `contra`.
- **`Profile.{u}`:** extends `ProfileOps` with `Ctx : Type u`, `mem`, `Holds`, `le_sound` and `contra_sound`. `Means` is unchanged.
- **Executable code takes `ProfileOps`:** `Clause` and the executable checks (`checkNarrow`, `acceptsNarrow`, `withNarrowing`, `checkCover`, `acceptsCover`, `assessConflict`, `conflictFindings`, `reviewRelease`).
- **Semantics takes `Profile`:** the semantic contracts (`Coverage.sound` and `Overlap` soundness) and all theorems.
- **`Overlap`:** has executable `Code : Type` and `witness : Scope → Scope → Option Code`. Soundness is `∀ a b k, witness a b = some k → ∃ c, mem c a ∧ mem c b`. Release review reports the code. A witness without its soundness proof cannot be registered.
- **Harness profiles** instantiate at `u = 0`. No harness semantics change.

**Acceptance:**

- every kernel module re-checked with `leanchecker`, using standard axioms only;
- 79/79 kernel cases re-run with unchanged verdicts;
- native outputs byte-identical, except fields the refactor necessarily renames (list them);
- the 459-case legacy replay and the 67 protected artifacts unchanged.

### 2.5c Algebraic context spike

Budget: at most 2 active hours, in the binding package, Mathlib pin `520045ab14e26149ee970e2e617ca04b09bde5d6`, Lean 4.32.1.

1. Instantiate the 3a profile's semantic half with `Ctx := Theory.field.ModelType`. Will's reviewer confirmed these files exist at the pin: `Mathlib/ModelTheory/Bundled.lean` and `Mathlib/ModelTheory/Algebra/Field/Basic.lean`.
2. Prove `le_sound` for the §3.2 characteristic lattice, and `contra_sound` for EMPTY versus NONEMPTY of one statement.
3. Measure the friction of converting between `Language.ring` structures and Mathlib's `Field` (via `CompatibleRing`).
4. If the friction is poor, define a local bundle `FieldCtx` (a carrier in `Type` plus a `Field` instance). Prove an equivalence with `Theory.field.ModelType`, so the institution link is a theorem rather than a slogan.

Report the choice in at most 300 words.

### Gate G2.5

Pass conditions:

- the split and pin are written;
- the refactor is done and its acceptance checks pass;
- the spike is reported;
- `reports/PHASE-2.5-REPORT.md` is at most 800 words;
- new Markdown for the phase is at most about 2,000 words.

Will ratifies G2.5 before any 3a profile code lands.

---

## 3. Phase 3a — algebraic profile, Nullstellensatz regime

### 3.1 Statement AST

The AST is Mathlib-free, canonical JSON, and hashed.

- **`vars`:** ordered variable names.
- **`eqs`:** sparse polynomials with rational coefficients, canonicalized: reduced fractions, sorted terms, no zero terms.
- **`guards`:** polynomials required to be nonzero. The locus over K is {a ∈ Kⁿ : eqs(a) = 0 and every guard(a) ≠ 0}.
- **`kind`:** one of:
  - **EMPTY / NONEMPTY:** the locus is empty or nonempty;
  - **VANISHES_ON(h):** h(a) = 0 at every point a of the locus;
  - **IN_IDEAL(h):** h ∈ ⟨eqs⟩ in K[x][1/∏guards], ambient when there are no guards. This is ideal level, kept separate from VANISHES_ON (GP-A03a).
- **S_stmt** is computed from all coefficients, including h's.
- **Elaboration target** (binding package): Mathlib `MvPolynomial (Fin n)` over K, through the ring map ℤ[1/S_stmt] → K. That map exists exactly when `ringChar K ∉ S_stmt`.
- **Input syntax:** an untrusted adapter may parse Singular/Macaulay2-style infix into canonical form. It must echo the canonical form back for review, because a mistranslation here is a meaning error (M5).

### 3.2 Scope: characteristic sets

- A scope is `(char0 : Bool, primes : Finite F | Cofinite E)`.
- `mem K S ⇔ ringChar K ∈ ⟦S⟧`.
- `le` is exact, decidable set inclusion.
- **Well-formedness:** ⟦S⟧ ∩ S_stmt = ∅. Otherwise the claim is ill-formed (GP-A05).
- Field-class flags belong to 3b.

### 3.3 Checkers

All checkers replay; search stays external; reach is computed.

**C1. Unit/saturation certificate (EMPTY).** Cofactors q_i and an exponent k ≥ 0 with Σ q_i·eq_i = (∏guards)^k.
- Replayed over ℚ: reach is every characteristic outside S_stmt ∪ S_cofactors.
- Replayed over F_p: reach is {p}.
- This covers the X65 localized unit ideal, which Phase 2 bound by verdict only.

**C2. Witness (NONEMPTY).** A point a over ℚ or F_p with eqs(a) = 0 and every guard(a) ≠ 0.
- ℚ reach: every characteristic outside S_stmt ∪ S_a ∪ {p : p divides the numerator of some guard(a)}. A guard that vanishes after reduction is not a point (GP-X410).
- F_p reach: {p}.

**C3. Membership (IN_IDEAL(h), VANISHES_ON(h)).** A certificate h^m·(∏guards)^k = Σ q_i·eq_i.
- m = 1 admits IN_IDEAL(h).
- Any m ≥ 1 admits VANISHES_ON(h).
- Reach is computed as for C1.

**C4. Relation certificates** for the §3.4 rules, built from C1 and C3 instances:
- **Inclusion** locus_T ⊆ locus_L: each loose equation vanishes on the tight locus (C3); each loose guard is nonvanishing on the tight locus (C1 on the tight system plus that guard as an equation). For IN_IDEAL transport, the inclusion must instead be ideal-level (m = 1, k = 0).
- **Polynomial map** φ: locus_S → locus_T: each target equation ∘ φ vanishes on the source locus (C3); each target guard ∘ φ is nonvanishing on the source locus (C1 on the augmented system).
- **Structural split** on a polynomial h: one branch adds the equation h, the other adds the guard h.

**Each admission requires:**
- the Mathlib-free executable;
- a Mathlib soundness theorem in the binding package, connecting the replay to `MvPolynomial` evaluation and to the computed reach;
- adversarial controls: wrong cofactor; swapped generator; a denominator hidden in a cofactor; a guard vanishing after reduction; an F_p certificate used in characteristic 0;
- a `TCB.md` entry;
- the overlapping tool named (§1.7);
- at most about 300 lines per checker, or a written justification.

### 3.4 K3 rules

Each rule's direction table is part of its admission. All are carry kind 3.

- **R1:** IN_IDEAL(h) ⇒ VANISHES_ON(h), on the same locus.
- **R2, inclusion** (locus_T ⊆ locus_L by C4):
  - EMPTY and VANISHES_ON move L → T;
  - NONEMPTY moves T → L;
  - IN_IDEAL moves L → T only with an ideal-level inclusion certificate;
  - never reversed. This is the one encoding of relaxation.
- **R3, map** (φ: locus_S → locus_T by C4):
  - NONEMPTY moves S → T;
  - EMPTY moves T → S;
  - VANISHES_ON(h) on T gives VANISHES_ON(h∘φ) on S;
  - EMPTY S → T is refused (GP-X360).
- **R4, object cover by checked structural splits:** EMPTY, or VANISHES_ON(h), on every branch gives the same on the parent. NONEMPTY of a branch reaches the parent only through R2.

Context covers over scopes (for example, char ∈ {2} and char ∉ {2}) use the kernel `Cover`.

The other carry kinds: kind 1 (number-field translation) arrives in 3b; kind 2 (encodings) arrives in Phase 4. Kind 4 is expected to have no 3a instance (M1 checks this).

### 3.5 Proposer duties in 3a (§1.9)

- the widest-reach claim per held receipt;
- R1–R4 instances over declared statements with available C4 certificates;
- K2 narrowings to the scopes of open obligations;
- the ranked, capped earned surface.

### 3.6 First slice: reach demonstrations

Run this before broad case work. Deliverable: `reports/PHASE-3A-SLICE.md`, at most 500 words.

- **GP-A08b:** the integral certificate's reach is every field. The proposer files the widened claim, and the earned surface shows it.
- **GP-A08c:** the witness reaches characteristic 3. Report the computed exclusion set.
- **GP-A05:** refused as ill-formed. **GP-A04** and **GP-X126:** refused on reach. **GP-X125:** accepted. **GP-X15/X16:** an F_2 replay reaches exactly {2}.
- **Fano cases (new, authorized).** Encode the Fano plane realization system in the 3a AST: an affine chart, the incidence equations and nondegeneracy guards.
  - Must-ACCEPT: a C1 certificate found by external search holds EMPTY in characteristic 0. Its computed reach must exclude 2; the report states whatever cofinite set it actually reaches.
  - Must-ACCEPT: an F_2 witness holds NONEMPTY at {2}.
  - Must-REFUSE: using the C1 certificate in characteristic 2.
  - If certificate search fails within one active hour, report the failure; do not weaken the case.
- **DK-B027:** disposition it here. "Finite-field controls are not a char-0 proof" is reach {p}.

### 3.7 Corpus execution

1. Write `corpus/GATE-OWNERS.json` first (§1.11). Assignment rules:
   - Nullstellensatz-regime cases → 3a.
   - Ordered/SOS, number-field, selected-root/embedding and section cases → 3b.
   - Campaign-specific operations → campaign-op. Examples: graded face extraction, Laurent lowering, recurrence/jump schedules, Cramer clearing, dm4 caps, triangular chains, coefficient-row packing.
   - Ambiguous cases → Will.
   - Secondary profile duties in `corpus/LAYER-TAGS.json` (for example X175's replacement section certificate) follow their case's owner.
2. Run every 3a-owned case through the shared frontend (§1.8).
3. Re-execute kernel cases X177–X186, A01, A08a, X14 and X283 through the profile where they are expressible. Report each one: expressible-and-consistent, or inexpressible with the reason.
4. **Global safety run:** every profile-layer case through the 3a profile. No must-REFUSE case may be ACCEPTed. Vacuous refusals never count as passes for owned cases.

### 3.8 Differential tests against the v0.37 oracle

- Run the JC(2) plane fixture and the matroid realizability fixture. The matroid fixture is characteristic-dependent, so it exercises §1.2.
- Triage each disagreement as a GP bug, a core bug or an expressiveness loss.
- The DK retrodiction moves to Phase 4.
- `gamma_window` is dropped, since the JC material was extracted.

### 3.9 Binding package

- A separate Lake package that depends on the Mathlib pin. It contains the `Ctx` choice (§2.5c), statement elaboration and checker soundness theorems.
- It is never imported by `Kernel` or by any runtime executable.
- **Amends rev 3 §8.5:** a Mathlib bump requires re-checking every admission theorem. Warrants stay current if their checker's theorem re-checks unchanged. If re-admission fails, that checker's warrants go stale.

### Gate G3a (replaces rev 3 G3)

Pass conditions:

- 100% of 3a-owned cases pass through the shared frontend. Each expressiveness loss counts against G3a unless Will reassigns its owner.
- Zero false ACCEPTs across all 239 profile-layer cases.
- The reach slice has executed, including the Fano cases and one earned widening shown by the surface.
- Every 3a checker is admitted (§3.3). Every K3 rule carries `carry_kind` and a proved direction table.
- Oracle disagreements are triaged, and corpus corrections are signed off in `corpus/CHANGES.md`.
- The kernel pin is unchanged since G2.5, or every change is logged.
- Will reads `STATUS.md` cold in under 10 minutes.

**On failure:** report the expressiveness losses and stop. Do not widen `le` to evidence-backed comparisons, and do not add per-case bridges to pass.

On pass: prepare `v0.50.0-alpha` (§1.12).

---

## 4. Phase 4 — census profile (the portability test)

The rev 3 Phase 4 plan stands, with these amendments:

- **Prerequisite:** the M4 memo (ranked options for enumeration completeness and symmetry breaking) comes before checker work.
- **Hypotheses: scope or premise.**
  - Standing assumptions the campaign does not intend to discharge (GRH-type) may be scope.
  - Assumptions the campaign intends to discharge (encoding correctness, enumeration completeness, split coverage) are premises, so they stay visible as open obligations.
  - Carrying a result from an encoding back to the claim is a K3 rule of carry kind 2. Its obligation is model expansion: every source object must arise from some model of the encoding.
- **Checkers:**
  - SAT model check;
  - LRAT (the native candidate, with explicit trust per `TCB.md`; admission needs an argument plus controls; cake_lpr deferred);
  - permutation certificates for isomorphism and automorphism;
  - embedding witnesses;
  - enumeration completeness per M4.
- **Proposer:** subcase consequences of held NONE and COUNT claims, for example "this held NONE at n = 22 also settles these subcases."
- **Must-refuse set (authorized):** the rev 3 list, each with matching must-accept controls:
  - a timeout read as UNSAT;
  - "none found up to n" read as "none exist";
  - an unsound symmetry break used for counts;
  - a non-exhaustive cover;
  - an unchecked LRAT proof;
  - a floating-point "verification";
  - an encoding without a correctness warrant.
- **Retrodiction:** reproduce the DK V4-sector census slice (moved here from the G3 differential list).

### Gate G4

Pass conditions:

- The kernel pin is unchanged; bug fixes and D9 promotions are logged.
- The `ProfileOps`/`Profile` split and `Ctx` polymorphism are used unchanged by a second real profile.
- Census traps are refused.
- The DK slice reproduces.

**On failure:** an unjustified kernel change means the abstraction leaks. Report and stop.

---

## 5. Phase 3b — algebraic profile, remaining regimes

**Open design question.** Decide this with M1 before writing code, against GP-A10-C/Q/R and GP-X345. Ordered statements can either:

- **(a)** stay in the field profile, with `Holds` quantifying over orderings of K and a scope flag for formally real fields; or
- **(b)** form an ordered-field profile with its own `Ctx` (ordered field models), plus a kind-1 translation rule from field statements.

**Scope additions:** field-class flags (formally real, real closed, algebraically closed), as the decision requires.

**Number-field statements:**
- The signature is ℤ[1/S][t]/(m), with m irreducible over ℚ.
- `Holds` quantifies over the roots of m in K, unless the statement selects a root.
- A selected real root carries an isolating interval (rev 3 §8.8).
- A kind-1 rule translates ℚ-statements into this signature.

**Checkers:**
- exact SOS/Positivstellensatz replay: rational Gram matrices, with positive semidefiniteness decided by exact LDLᵀ;
- extension-valued witnesses with an irreducibility certificate for m (the rational-root test for degree ≤ 3; GP-X350);
- selected real algebraic points: root existence, isolation and equation replay, with the Isabelle AFP *Algebraic_Numbers* development as the algorithm and pitfall reference;
- sections and map identities (X255–X268, X173–X176).

### Gate G3b

Pass conditions:

- 100% of 3b-owned cases pass.
- Zero false ACCEPTs on a re-run over all profile cases.
- The kernel pin is unchanged, or every change is logged.
- The Cloquet and u(22) realization moves have an admitted checker path.

---

## 6. Phase 5 — pilot and comparison

The rev 3 Phase 5 plan and G5 stand, including the kill criterion: if the core does not beat the notebook baseline, stop and reconsider; do not add features to rescue it.

Added entry prerequisites:

- **Commit/merge guard (§1.5):** built and tested with collision controls: a same-version current tie across branches; retraction versus supersession of one target; conflicting warrant contents under one ID; and a clean concurrent merge.
- **M5 meaning audit** of the u(22) goal, using Formal Conjectures first.
- **Prospective cost-log schema** written before the u(22) slice starts: time, tokens, catches, and expensive near-misses.

---

## 7. Math lanes

**M1 — start now, alongside 2.5 and 3a.** The deliverable is as amended in Phase 2 handoff §3.4, checked against the post-2.5 definitions, plus:

- **(a)** State the §1.1 criterion formally, and test it on about 10 hard examples: symmetry sectors, "up to isomorphism", SAT encodings and conditional claims.
- **(b)** Confirm that `Ctx = Theory.field.ModelType` gives the first-order-logic institution exactly:
  - sentences in `Language.ring`;
  - models `ModelType`;
  - satisfaction `Realize`;
  - model reduction `ModelType.reduct`.
- **(c)** Decide whether §1.2 leaves carry kind 4 with any 3a instance, and what remains of it. Hensel lifting to ℚ_p is the candidate.
- **(d)** Feed the §5 ordered-statement decision.

Stop as before.

**M2** is closed by the Phase 1 scope map. Reopen it only for 3b field classes.

**M3** is largely absorbed by §1.2. What remains:
- Record Mathlib's ACF transfer at the pin as a possible later rule: `Theory.ACF`, `ACF_isComplete`, and `ACF_zero_realize_iff_infinite_ACF_prime_realize` in `Mathlib/ModelTheory/Algebra/Field/IsAlgClosed.lean`.
- It yields "all but finitely many p" with no explicit exceptions. That is not a scope in the §3.2 lattice, and explicit certificates dominate it for GP's purposes.
- The Fano fixtures move into 3a.

**M4** comes before Phase 4 checker work, unchanged. **M5** comes before Phase 5, unchanged. **M6** comes after G5, unchanged.

---

## 8. Process

Phase 2 handoff §4 carries over, with these changes:

- Each phase or sub-phase opens its own report: `PHASE-2.5-REPORT.md`, `PHASE-3A-SLICE.md`, `PHASE-3A-REPORT.md`, and so on, under the 800- and 500-word caps. `STATUS.md` remains the single source of truth, with a plain-language top section of at most 300 words.
- New Markdown per phase targets 10,000 words, with the tripwire at 15,000. Phase 2.5 targets 2,000.
- Produce one aggregate receipt per gate run, not one JSON file per case family.
- Single-chat GPC operation continues unless Will re-splits it. Heartbeats stay paused unless Will restarts them.
- Deferred: CI certification and toolchain portability (§1.12).

**Stop and ask Will if:**

- you want to change a §1 decision;
- a 3a-owned case is inexpressible under §1.1 or §1.2 (a possible pivot);
- any kernel change after G2.5 is not a logged bug fix;
- a checker's soundness theorem needs a non-standard axiom;
- gate-ownership assignments are ambiguous;
- the Fano certificate search fails.

---

## 9. Gates (revised)

| Gate | Pass condition | On failure |
|---|---|---|
| G2.5 | Package split and pin; `Profile` split plus polymorphism; 79/79 unchanged; proofs re-checked; spike reported; Will ratifies | Report; no 3a profile code |
| G3a | 100% of 3a-owned cases; zero false ACCEPTs across profile cases; reach slice incl. Fano; checkers admitted; rules carry `carry_kind`; pin unchanged | Report expressiveness losses; never widen `le` or add bridges |
| G4 | Pin unchanged or D9-logged; split used unchanged by census; traps refused; DK slice reproduces | Abstraction leaks: report and stop |
| G3b | 100% of 3b-owned cases; zero false ACCEPTs re-run; pin unchanged; realization path for Cloquet/u(22) | Report |
| G5 | Rev 3 G5 unchanged | Kill or rethink; no rescue features |

---

## 10. Not-list additions

GP 0.50 will not:

- use per-case bridges in profile work (§1.8);
- put Mathlib in `Kernel` or in any runtime executable; Mathlib appears only in the binding package's semantics and admission theorems;
- admit evidence-backed comparisons into `le` (§1.1);
- put campaign-op checkers in a minimal profile;
- add a kernel concept for signature morphisms without D9.

---

## 11. Carried forward

- **Unresolved owners:** DK-B027 is now owned by 3a (§3.6). GP-SRC-CQ-G02, JC-B010, JC-B014, PR-C13, PR-O01 and PR-T16 stay open, revisited only if a profile touches them.
- **Phase 2 closeout deferrals:** multivariate replay → C1/C3. X65 → C1 with guards. X173–X176 → 3b sections. LRAT → Phase 4 admission. `carry_kind` → §3.4.
- **Meaning** remains the named blind spot (M5).
- **ADAPTER** was the largest incident class: keep the checker count low and the admission bar high.
- **LMFDB contact** is Will's.
- **Policies open to revision:** exact-premise theorem transport, and the assumptions of the conditional harnesses.
