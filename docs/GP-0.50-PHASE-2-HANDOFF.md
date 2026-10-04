# GP 0.50 — Phase 2 handoff (G1 closed)

**Date:** 2026-09-30 · **Owner:** Will · **Applies to:** `codex/phase-0` → Phase 2
**Authority:** This document records Will's G1 decisions and authorizes Phase 2. It amends the revision 3 packet and `DECISIONS.md`. Where they conflict, this document wins. Copy §1 into `DECISIONS.md` verbatim.

---

## 0. Plain-language summary (the model for `STATUS.md`)

Phase 0 and Phase 1 produced a good design. The core idea survived its riskiest test: across every recorded incident, narrowing a claim's scope never needed to change *which objects* the claim is about. Paper coverage was 52 of 67. The eight rows outside the guarantee are genuinely outside it, and seven are unresolved. That is close enough to pass.

The builders found a real bug in v0.37: merging branches in a different order can change what counts as verified. They also caught that "no missed implications" needs its own completeness proof, because soundness alone is satisfied by a system that never holds anything. And they measured that Mathlib proofs are too slow (40–150 s each) to be the everyday currency.

Phase 2 builds the actual kernel in Lean, proves it sound *and* complete over a finite domain, and runs about ten real cases end to end early on. The goal is to get off paper. The process also has to shrink: Phase 0 produced about 180k words of reports, more than twice the whole predecessor's documentation. Phase 2 has a hard documentation budget and one readable status page.

---

## 1. G1 decisions (ratified by Will, 2026-09-30)

1. **Coverage exception accepted.** Paper expressiveness is 52/67 (77.6%), with 8 outside and 7 unresolved. This passes G1 as a documented exception to the ~80% screen. No prevention rate is claimed. All 459 expectations are unchanged, and G3's full obligations remain.
2. **Both warrant forms, one scope interface.** Admitted replay receipts and bound Lean proofs share exact statement/model/hypothesis/authority identities.
   - **Policy:** receipts are the default working currency. A Lean-proved warrant is an *upgrade* for durable or important claims, or where no receipt checker exists.
   - The binder checks declaration type, imported axioms and exact input identity. A theorem pointer or build flag is never enough.
   - Generated native-result axioms are excluded from ordinary theorem warrants.
3. **MathEvidence: imitate the contracts, qualify components individually.** Adopt its capability-specific, bound-candidate, fail-closed discipline. Import no code wholesale. Before building any checker that overlaps an existing tool, name that tool and the contract it lacks.
4. **Mathlib vocabulary through a pinned binding layer, with explicit exceptions.** Use `reports/PHASE-1-SCOPE-MAP.md` as the initial map. Do not substitute old labels mechanically. For example, A08b needs only `Ring`, while general ideal checks need `CommRing`. GRH, selected roots, coverage and encodings stay as explicit hypotheses or statement/model fields.
5. **Native LRAT is accepted as a checker candidate with a named trust boundary.** The compiler, runtime and generated Boolean-result axiom go in `TCB.md` as explicit assumptions. Admission still requires a soundness argument and adversarial controls. A verified alternative such as cake_lpr is deferred until a claim needs it.
6. **Earned closure is defined as a least fixpoint.** `held` is the least fixpoint of admitted checkers and rules over the declared finite domain: claim keys, narrowing requests and admitted rule instances. Phase 2 must prove **completeness** against this definition: every claim reachable in the finite domain from current valid warrants is held. This is what gives "no missed implications" teeth.
7. **Freeze patch: authorized.** Push the prepared v0.37.1 doc-only patch, including the banner, to `wstrinz/grandportage`, exactly as prepared in `reports/freeze-v0.37.1/`. This is the only public action authorized here.
8. **Terminology.** "Profile" is retained as GP's name. Its correspondence to institutions is documented in §3 and used as reference semantics.

---

## 2. Phase 2 scope

### 2a. Corpus layer tags (do this first; metadata only)

Tag each of the 459 cases with its layer: `kernel` / `profile` / `adapter` / `surface` / `host`. Examples:

- "output must end with exactly one completion token" → `adapter`;
- "stale history must not overwrite a current result" → `kernel`;
- "point containment doesn't give ideal pullback" → `profile` (algebraic).

**Rules:**

- Tags never change expectations.
- Put ambiguous cases in a short list for Will instead of deciding them.
- G2 gates only on `kernel` cases. Later gates take their own layers.

### 2b. Vertical slice (early; before the kernel is complete)

Run about 10 `kernel`-layer cases end to end: through the real Lean fold and `held`, plus one stub algebraic checker. The spike's exact `Rat` cofactor replay can serve as the stub.

Include at least these:

- a stale receipt (A18-type);
- a timeout or absent attempt (A17-type);
- a non-exhaustive cover (A16-type);
- warrant retraction with independent support surviving;
- a failed retry that does not revoke;
- the v0.37 merge-order case (the result must be the same in both orders);
- one K2 narrowing;
- one earned-but-unclaimed consequence;
- one conflict at a proved overlap;
- one positive control.

Deliverable: `reports/PHASE-2-SLICE.md` (≤ 500 words) listing the *executed* refusals and acceptances. These are the first non-paper results.

### 2c. Kernel (Lean, Mathlib-free)

- A typed event schema and decoder. Unknown constructors and statuses are malformed; there is no silent replacement of IDs.
- A fold that computes `held` as the §1.6 least fixpoint, with K1–K6.
- The conflict finding: contradictory statements at *proved* inhabited overlap freeze new promotion, while unknown overlap is only reported as unresolved.
- Two queries: **why-not** (what is missing for claim X) and **earned** (what is held but unclaimed, ranked by the open obligations it touches).
- `TCB.md` integration.

### 2d. Proofs and properties

Allowed axioms are Lean's standard three: `propext`, `Quot.sound` and `Classical.choice`. No `sorry`, no `native_decide` and no custom axioms in the kernel.

1. **Soundness.** Instantiate `heldSoundStatement` with the actual fold and `held`, and prove it.
2. **Completeness.** `held` equals finite reachability under admitted instances (§1.6).
3. **Order independence.** The held set depends only on the *set* of events. Retraction and supersession reference their targets by ID, and current versions use explicit version numbers, not arrival order. Prove this as a theorem if feasible. Otherwise prove it for a named sub-class and list the exceptions. Either way, the v0.37 merge-order case must pass.
4. **Lifecycle properties.** Failed retries never revoke independent support. Retracting a warrant invalidates exactly its dependents. Circular support never bootstraps authority.
5. **Determinism and totality** of the fold.

### 2e. Budget (unchanged from D8)

- core logic ≤ ~500 lines;
- decoding ≤ ~400 lines;
- soundness statement plus dependencies ≤ ~80 lines;
- proofs uncapped;
- tripwire at 1.5× any budget line: stop and report.

### Not in Phase 2

- profiles beyond the stub checker;
- the census profile;
- package or checker adoption;
- surfaces beyond the two queries;
- new corpus cases (except layer tags);
- further predecessor audits.

---

## 3. Profiles and institutions (reference semantics; seed for math lane M1)

"Profile" stays GP's term. Its *semantic* half corresponds precisely to a well-studied notion, and naming the correspondence gives GP a mathematician-built vocabulary and a principled classification of carry rules.

### 3.1 Background

An **institution** (Goguen & Burstall) has four parts:

- a category of *signatures* Σ (vocabularies);
- for each Σ, a set of *sentences* Sen(Σ);
- for each Σ, a class of *models* Mod(Σ);
- a *satisfaction* relation M ⊨ φ.

Along each signature morphism σ: Σ → Σ′, sentences translate forward and models reduce backward. The **satisfaction condition** requires that truth is invariant under this change of notation:

M′ ⊨ σ(φ)  ⇔  M′|σ ⊨ φ.

Meseguer's **general logics** add *entailment systems* and *proof calculi* on top. A proof calculus is **sound** when everything it proves is semantically true.

### 3.2 Correspondence

| GP (`SoundnessStatement.lean`) | Institution theory | Match |
|---|---|---|
| `Stmt` | sentences Sen(Σ) | exact |
| `Ctx` | models Mod(Σ) | exact |
| `Holds φ c` | satisfaction c ⊨ φ | exact |
| `Scope`, `mem` | a class of models, typically Mod(T) for a presented theory T | exact, restricted to finitely described scopes |
| `le S′ S` (sound, decidable) | Mod(T′) ⊆ Mod(T), e.g. when T′ ⊨ T | GP's test is *sound but incomplete*; institutions don't require decidability |
| `Means φ S` | semantic consequence T ⊨ φ | exact |
| K2 weakening (`weakening_sound`) | monotonicity of consequence: more axioms, fewer models, more consequences | exact; this is why K2 is polarity-independent |
| `CheckerSound k` | soundness of an entailment system/proof calculus with respect to ⊨ (Meseguer) | exact in shape |
| checker *reach* | the theory whose models the proof's axioms cover (cf. Logipedia) | exact in spirit |
| `contra` | joint unsatisfiability of φ and ψ | exact |
| one `Profile` | an institution restricted to one signature, plus an entailment system | GP currently has no signature morphisms |
| warrants, bindings, freshness, log, lifecycle | — | **no counterpart**; operational custody (build-system territory) |

### 3.3 What institutions add: a taxonomy of carry rules (K3)

The correspondence classifies GP's "carrying" into four kinds with *different* soundness obligations. Each admitted K3 rule should declare its `carry_kind`:

1. **Theory-morphism translation** (change of notation within a logic). Example: base extension, adding a constant *i* with i² = −1. If σ is a theory morphism (T′ entails σ(T)), then T ⊨ φ implies T′ ⊨ σ(φ). This is **sound by the satisfaction condition**; the only obligation is proving that σ is a theory morphism.
2. **Comorphism / encoding** (translation into another logic). Example: a census statement encoded as CNF. Carrying UNSAT back requires the satisfaction condition for the comorphism **plus model expansion**: every source model must arise from some target model. This is exactly GP's *totality* property on relations, and exactly the empty-hexagon encoding-correctness obligation.
3. **Statement-level relation rules within one logic** (inclusion, image, equivalence between objects). These are sound by relation properties, not by change of notation. Imitate Mathlib's `Relator` / Trocq.
4. **Proof translation with no model-level justification.** Example: reducing a p-integral certificate mod p (char 0 → char p). The two model classes are *disjoint*, so no satisfaction-condition argument exists. The certificate *itself* is translated and re-checked. The builders' scope-map note, "characteristic-changing specialization is not a generic inclusion of worlds", is this point.

### 3.4 Decisions for now

- **No kernel change in Phase 2.** A single-signature Profile is sufficient and fits the budget. Signature morphisms are a Phase 3+ design question, to be decided against the base-extension cases (A1, A2) under D9.
- **Documentation vocabulary.** Use institution terms in `SPEC-CORE` glossaries and in M1: sentence, model, satisfaction, theory, theory morphism, comorphism. Do not use them in user-facing surfaces.
- **M1 deliverable, amended.** A short note that:
  - states Profile as an institution fragment plus an entailment system;
  - checks the table above against the actual Lean definitions;
  - gives one worked example for each of the four carry kinds, using corpus cases.
- **References:**
  - Goguen & Burstall, "Institutions: Abstract Model Theory for Specification and Programming", JACM 1992;
  - Meseguer, "General Logics", 1989;
  - Diaconescu, *Institution-Independent Model Theory*, 2008;
  - Mossakowski et al., Hets (heterogeneous specification via comorphisms).

---

## 4. Process rules for Phase 2

The Phase 0 work was careful and honest. It was also far larger than useful, and hard for Will to read. These rules bind:

1. **One `STATUS.md`** is the single source of truth. Its top section is a plain-language summary of ≤ 300 words, written for Will, updated each working session. Everything else is linked from it.
2. **Length caps:**
   - phase reports ≤ 800 words;
   - decision-log entries ≤ 150 words;
   - the slice report ≤ 500 words.
3. **State limits once.** Standing caveats live in `LIMITS.md`. Do not repeat hedges ("bounded", "not a claim that", "under explicit limits") paragraph by paragraph. Say what *is* true plainly.
4. **Code over prose.** A proof or test replaces a paragraph. New markdown in Phase 2 totals ≤ ~10k words, excluding generated JSON. The tripwire is at 15k: stop and report.
5. **No predecessor audits** unless a named Phase 2 decision needs a specific case. No new corpus cases without Will's approval (layer tags excepted).
6. **Workers and heartbeats** are allowed, but every worker assignment must produce code, a proof or a test. Reading-only assignments need Will's approval.

---

## 5. Gate G2

- **Slice:** the 2b report shows about 10 executed kernel-layer cases, all as expected.
- **Kernel:** built within the 2e budget, with no tripwire crossed.
- **Proofs:** soundness, completeness, and order independence (or its documented sub-class) are proved with only standard axioms. Lifecycle properties are proved or tested.
- **Corpus:** 100% of `kernel`-tagged cases pass. Other layers are reported, not gated.
- **Readability:** Will reads `STATUS.md` cold and can say what is done, what is proved and what is next in under 10 minutes.

On passing G2, proceed to Phase 3 (minimal algebraic profile) as in the rev 3 packet, with §3.3's `carry_kind` field on every K3 rule.

---

## 6. Carried forward

- **Seven unresolved owners** (DK-B027, GP-SRC-CQ-G02, JC-B010, JC-B014, PR-C13, PR-O01, PR-T16) stay open. Revisit them only if a Phase 3 profile touches them.
- **Meaning** remains the named blind spot. M5 is unchanged, with Formal Conjectures as the first-choice goal source.
- **Cost data.** Retrospective cost is unrecoverable. Instead, log cost *prospectively* in the first live campaign slice (u(22)): time, tokens, what was caught, and what would have been expensive. Design the log schema in Phase 5, not now.
- **Fellow travellers.** LMFDB's Lean bridge is the leading consumer candidate. Will handles any contact.
- **ADAPTER was the largest incident class** (34 of 115). Expect Phase 3+ risk to concentrate in checker quality, and keep the admission bar high and the checker count low.