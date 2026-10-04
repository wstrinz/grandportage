# GP 0.50 — post-G2 handoff, Addendum A: Lean-first, built on experts' substrate

**Date:** 2026-10-02 · **Owner:** Will · **Applies to:** Phase 2.5 (in progress) onward
**Authority:** This addendum amends `GP-0.50-POST-G2-HANDOFF.md`; where they conflict, this addendum wins. Append §1 to `DECISIONS.md` verbatim. It takes effect immediately, including for the Phase 2.5 work already running. §2.5d must land before `KERNEL-PIN.json` is written.

---

## 0. Plain-language summary

Since the handoff was written, people who build Lean for a living released much of what GP was going to build itself:

- **Hex** (Lean FRO): verified computational algebra in Lean, with polynomials, real roots, number fields, factoring and graph isomorphism. Its architecture matches GP 0.50's: computational libraries without Mathlib, plus separate libraries proving correspondence with Mathlib.
- **LRAT-Catcher** and **PBLean** (Szeider): SAT and pseudo-Boolean certificates turned into Lean theorems, including cube-and-conquer coverage.
- **AutoGeneralization**: finds the weaker typeclass assumptions a Lean proof actually needs. This is GP's "earned but unclaimed" idea, implemented for proofs.

GP should stand on these rather than build its own. That leaves GP's own job smaller and clearer: compute how far each result reaches; keep the campaign ledger honest; and tell the user what is held, what is missing and what was earned.

Will's stated preference is that it would be fine for all of this to be Lean, and fine if GP eventually dissolves into plain Lean. So GP becomes **Lean-first**, prefers Lean theorems wherever they are cheap, and measures at every gate how much of its value plain Lean already provides.

---

## 1. Decisions (ratified by Will, 2026-10-02)

**A1. Lean-first.**
- New GP code is Lean: kernel, checkers, reach computation, proposer, the shared case-to-profile frontend, and the cores of the query surfaces.
- Python is limited to:
  - replaying the v0.37 oracle;
  - glue code that launches external solvers;
  - repository tooling such as budget checks and snapshot audits.
- The Phase 2 per-family Python runners retire under post-G2 §1.8.

**A2. Pin alignment.**
- GP adopts the Hex v0.6.0 release pins: Lean `v4.34.0-rc2` and Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`. Kernel and binding packages share them.
- The bump happens in Phase 2.5, before `KERNEL-PIN.json` is written.
- The release-candidate toolchain is recorded in `TCB.md`.
- Moving later to a Hex release on a stable toolchain is a logged change. The kernel re-checks; it is not a new design decision.

**A3. Adopt the substrate; build only what is GP's own.**

Adopt:

| Need | Adopted library |
|---|---|
| Polynomial representation and evaluation | `HexMvPoly` / `HexMvPolyMathlib` |
| Arithmetic modulo a prime | `HexModArith` |
| Real roots | `HexRealRoots` |
| Number fields | `HexNumberField`, `HexNumberFieldTower` |
| Univariate real decisions | `HexRCF` |
| Factoring and irreducibility | `HexBerlekampZassenhaus` |
| Graph isomorphism | `HexGraphIso` |
| Permutation groups | `HexPermGroup` |
| SAT certificates | LRAT-Catcher |
| Pseudo-Boolean certificates | PBLean |

GP builds only:
- reach computation;
- relation-certificate composition (the C4 bundles);
- receipt and theorem binding;
- the proposer;
- the kernel;
- the surfaces.

Each adopted component goes through admission, as for any checker:
- an axiom audit of the declarations GP relies on, with `leanchecker`;
- adversarial controls;
- a `TCB.md` entry naming any trusted runtime code it brings, such as GMP externs or native evaluation.

**A4. Warrant policy: Lean theorems first when cheap.** This amends the policy line of G1 decision 2; the binder contract is unchanged.
- For each 3a checker, measure two costs for the same claim:
  - **receipt cost:** replaying the receipt;
  - **theorem cost:** producing a Lean theorem with only the standard axioms, via Hex, `linear_combination` or `decide +kernel`.
- Mint a theorem warrant when its cost per claim is within 30 s of elaboration and checking (Will may adjust this number). Otherwise mint a receipt.
- The binder (G1 decision 2) becomes a 3a deliverable. It checks declaration type, imported axioms and exact input identity.
- Theorems that depend on native evaluation (for example LRAT-Catcher's) are not ordinary theorem warrants. They enter as admitted-checker receipts with explicit native trust, as G1 decisions 2 and 5 require.

**A5. Lean-convergence tracking.** Every gate report from G2.5 onward includes a short convergence section:

- **(a)** the fraction of held claims that also exist as standard-axiom Lean theorems, or could within the A4 budget;
- **(b)** for each held claim, the GP-specific value that remained, using these tags: `REACH` (computed reach wider or narrower than the request), `CUSTODY` (staleness, retraction or supersession affected it), `COVERAGE` (a coverage or premise obligation was tracked), `EARNED` (surfaced unclaimed), or `NONE`;
- **(c)** a one-paragraph read of the trend.

If (a) approaches 100% and (b) is mostly `NONE`, report it as a finding. GP may properly become a custody and reach layer over a Lean environment. That is an acceptable and interesting outcome, not a failure.

**A6. Concentration safeguard.**
- Pin released aggregates (`leanprover/hex` v0.6.0), never `hex-dev`.
- State GP's admission theorems against Mathlib definitions through Hex's Mathlib bridges. Then any substrate library can be swapped out without changing GP's semantics.
- `TCB.md` lists which GP guarantees rest on which external library and version.
- Several adopted libraries are developed largely by AI agents at high velocity. Their authority comes only from the kernel-checked theorems GP actually uses, so admission inspects those exact theorems. A library-level status label is not evidence.

**A7. Comparison arm.** G5's arm (b), Lean plus blueprint, uses the strongest Lean-native tooling available when Phase 5 starts, recorded with versions. This includes Hex tactics, LRAT-Catcher, and current autoformalization agents.

**A8. Outside contact remains Will's.** Candidate threads are recorded in §6 for him; the builder makes no contact.

---

## 2. Phase 2.5 additions

### 2.5d Pin alignment (A2)

1. Move the kernel, stub and binding packages to Lean `v4.34.0-rc2` and Mathlib `85e3a25e…`.
2. Re-run every Phase 2 proof with `leanchecker` (standard axioms only) and the 79 kernel cases.
3. Confirm the 459-case legacy replay is unchanged.
4. Re-run the 2.5c context spike at the new Mathlib pin. Confirm that `Mathlib/ModelTheory/Bundled.lean` (`ModelType`) and `Mathlib/ModelTheory/Algebra/Field/Basic.lean` (`Theory.field`) are present, and record any API drift.

Cap: 3 active hours. If the bump breaks more than mechanical names, stop and report before writing the pin.

### 2.5e Dependency layout

| Package | Depends on |
|---|---|
| `Kernel` | nothing (no Mathlib, no Hex) |
| Algebraic profile (executable) | `Kernel`; Hex libraries without Mathlib (`HexMvPoly`, `HexModArith`) |
| Binding | the profile; Mathlib; Hex's Mathlib bridges (`HexMvPolyMathlib`) |

Runtime executables never import Mathlib (post-G2 §1.3 and §10). Verify that the profile executable builds and runs with no Mathlib in its import closure.

### G2.5 additions

- The pins are aligned, and the Phase 2 proofs and cases re-pass.
- The dependency layout is verified.
- The report includes the first convergence section (A5). At G2.5 it is expected to be trivial; record the baseline anyway.

---

## 3. Phase 3a amendments

### 3.1 AST on HexMvPoly

- The canonical JSON wire format is unchanged.
- The decoder builds `HexMvPoly` values with fixed arity and an explicit monomial order. Use `lex` for canonical hashing; order is irrelevant to identity checks.
- First confirm that `MvPoly n Rat` has the instances the needed operations require.
- **Fallback if it doesn't:** use integer-coefficient polynomials with the denominator set S recorded beside them. Scaling an equation by d keeps the same locus exactly in characteristics that don't divide d, which matches §1.2's reach rule. Report which path was taken.

### 3.3 Checkers on Hex

- **C1 and C3 identity checks:** compute Σ q_i·g_i minus the right-hand side with `HexMvPoly` arithmetic and test it for zero. The representation is canonical, so structural zero equals mathematical zero.
- **C2 witnesses:** use `HexMvPoly` evaluation.
- **F_p replay:** use `HexModArith`.
- **Soundness:** prove through `HexMvPolyMathlib`'s correspondence with `MvPolynomial`.
- GP's own checker code reduces to:
  - certificate parsing and binding;
  - reach computation from denominators and from the guard values at a witness;
  - C4 relation-certificate composition.
- Hex's `hex-kronecker` and `hex-reflect` (kernel-checked identity checking) are in `hex-dev` but not in the v0.6.0 release. Use them only after a release includes them.

### 3.6a Lean-native shadow slice (A4, A5)

Budget: at most 4 active hours, after the receipt reach slice.

1. Restate the slice claims as Mathlib theorems: GP-A08b, A08c, A05/A04 (as refusals), X125/X126, and the Fano pair. Scope becomes typeclass hypotheses, for example `∀ (K) [Field K], ringChar K ≠ 2 → …`.
2. Prove each with Hex, `linear_combination` or `decide +kernel`.
3. Run AutoGeneralization (`#autogeneralize!`) on the proved statements, and compare its widening with the proposer's reach-based widening.

Report in at most 500 words:
- effort and time for each route;
- where the two routes' reach agreed or differed;
- which claims fit the A4 budget;
- the convergence tags from A5.

### 3.9 Binding package

Depends on Hex's Mathlib bridges at the A2 pins. The rest is unchanged, including the post-G2 rule that a Mathlib bump requires re-admission.

### G3a additions

- Every adopted library used by 3a is admitted under A3.
- The binder exists. The A4 costs are measured for every 3a checker, and the warrant policy is applied.
- The shadow slice is reported.
- The convergence section is present.

---

## 4. Phase 4 (census) amendments

- **Isomorphism and automorphism:** `HexGraphIso`, with `graph_iso` for theorem warrants where it fits the A4 budget, plus `HexPermGroup`.
- **SAT certificates:** LRAT-Catcher (`leansolving/lrat-catcher`), currently on Lean `v4.30.0` with no Mathlib.
  - Port it to the A2 pin. Offering an upstream PR is Will's call (§6).
  - Its theorems depend on `native_decide`, so they enter as admitted-checker receipts with explicit native trust (A4).
  - Its cube-and-conquer cover-completeness certificates discharge GP's split-coverage obligations. Wire them as `COVERAGE` premises.
- **Pseudo-Boolean certificates:** PBLean (Szeider, arXiv 2602.08692) for VeriPB certificates, including certified symmetry breaking.
- **M4** begins from these two tools. Its first question: does VeriPB's certified symmetry breaking settle the existence-versus-counts distinction for GP's census claims, or only existence?
- **Verified encodings** follow PBLean's and the empty-hexagon project's pattern: the encoding and its correctness proof both live in Lean. That is carry kind 2's model-expansion obligation discharged as a theorem.

---

## 5. Phase 3b amendments

- **Real roots and selected real algebraic points:** `HexRealRoots` (Sturm certificates) replaces building the rev 3 §8.8 checker from scratch. The Isabelle AFP stays as the pitfall reference.
- **Number-field statements and witnesses:** `HexNumberField` and `HexNumberFieldTower`.
- **Irreducibility certificates** (GP-X350): `HexBerlekampZassenhaus`.
- **`HexRCF`** decides univariate real-closed-field sentences. Its soundness theorem targets ℝ, so its warrants reach ℝ specifically, not every real closed field. Give the 3b scope lattice a specific-field atom for ℝ, distinct from the real-closed field-class flag.
- **SOS/Positivstellensatz:** no Hex checker was found at v0.6.0. Build per post-G2 §5, on `HexMvPoly`.

---

## 6. Outside threads (for Will; the builder makes no contact)

- **Hex / Kim Morrison** (Lean FRO; also behind Tau Ceti). Hex's future-work notes name ideal-membership cofactors as the compact trusted boundary, but have no account of reach. GP's certificate-reach computation and the Fano fixtures could be a natural upstream contribution or Zulip thread.
- **Stefan Szeider** (LRAT-Catcher, PBLean). The toolchain port; cube-and-conquer coverage as a reusable obligation pattern.
- **LMFDB / LeanBridge** (Roe, Sutherland, Birkbeck). Unchanged. LeanBridge now depends on Tau Ceti and carries number-field invariant certificates (A27 territory).

---

## 7. Math lanes

- **M1:** add one question. Does AutoGeneralization's proof-based widening and GP's receipt-based reach describe the same lattice for 3a claims? A worked comparison on the shadow-slice claims is enough.
- **M4:** seeded per §4.
- **M5:** for the u(22) goal, compare against the Lean Eval leaderboard's statement of the unit-distance count (`unitDist` over `EuclideanSpace ℝ (Fin 2)`, problem `erdos_unit_distance_conjecture_false`), alongside Formal Conjectures. Record any metric or counting-convention mismatch, such as ordered versus unordered pairs, or Euclidean versus sup metric.
- **Tailings consumer** (Phase 5 surfaces): Tao's optimization-constants site (`teorth.github.io/optimizationproblems`) tracks bounds with per-entry provenance. Note its format when designing the tailings export (D18).

---

## 8. Prior-art addendum

Append to `PRIOR-ART.md` as rows P19–P24, with the builder confirming each by primary source during admission:

| Row | Proposal | Reason and guarantee piece |
|---|---|---|
| P19 Hex (`leanprover/hex` v0.6.0) | adopt | Verified computational algebra with Mathlib-free cores and Mathlib bridges; same layering as GP; substrate for 3a, 3b and census checkers |
| P20 LRAT-Catcher (`leansolving/lrat-catcher`) | adopt | LRAT into Lean theorems by native reflection; cube-and-conquer cover certificates; census negatives and coverage |
| P21 PBLean (arXiv 2602.08692) | adopt (evaluate in M4) | VeriPB certificates with verified encodings and certified symmetry breaking |
| P22 AutoGeneralization (`pelicanhere/AutoGeneralization`) | adopt (proposer, Lean warrants) | Proof-based widening of typeclass assumptions: the earned-but-unclaimed dual for theorem warrants |
| P23 Tau Ceti (`TauCetiProject`) | imitate | Human roadmaps, AI implementation, adversarial review against open rubrics; a model for GP's builder workflow; a possible downstream home for GP's admission theorems |
| P24 Albilich (arXiv 2607.27705) | differ | Agentic CAS harness whose verifier trusts transcripts without re-execution; the contrast case for GP's replay-only authority |

---

## 9. Not-list additions

GP 0.50 will not:

- build its own polynomial, real-root, number-field, factoring or graph-isomorphism machinery where an admitted Hex library covers the need (D15);
- depend on unreleased `hex-dev` code;
- treat a library's status label, authorship or test count as evidence;
- resist Lean convergence. Report it (A5).
