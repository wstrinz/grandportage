# Phase 3a report (G3a)

Authority: post-G2 handoff §3 and Addendum A §3. Will continued past G3a-0 on 2026-10-02. The external review ([docs/GP-0.50-G3A-REVIEW.md](../docs/GP-0.50-G3A-REVIEW.md)) came back on 2026-10-03; Will adopted all eight rulings, and the 3a.1 patch below implements them. Every residue ruling is recorded in [DECISIONS.md](../DECISIONS.md). This report asks Will to ratify G3a.

## What exists

**Profile** (`profile/`, Mathlib-free, on HexMvPoly):
- **AST.** The canonical statement AST has kinds EMPTY, NONEMPTY, IN_IDEAL, VANISHES_ON, NOT_IN_IDEAL and COVER, over characteristic-set scopes. NONUNIT is gone: it is NOT_IN_IDEAL(1) on the system with the element added as an equation.
- **Checkers**, each with computed reach, run as exact rational replay:
  - C1/C3 ideal certificates;
  - C2 points, for NONEMPTY only;
  - the `proper` base checker for geometric nonemptiness;
  - COVER split trees.
- **K3 rules** (carry kind 3):
  - R1;
  - R2 and R3 with C4 obligations, including IN_IDEAL under the sound condition and NOT_IN_IDEAL(1);
  - R4, and R4 by cover;
  - the bridge NONEMPTY ⇒ NOT_IN_IDEAL.
- **Frontend.** A plan engine, strict-key family adapters (with `meta` ignored), an explicit statement surface, the instantiation-fixture loader, and the untrusted proposer behind the commit guard.

**Binding** (`binding/`, Mathlib `85e3a25e`):
- **Soundness.** `fold_held_meaning_rules`: every claim the Kernel fold holds, through receipts, rules, narrowing or bound theorem warrants, means its statement in every field of its scope. Theorem warrants rest on the `RecordsSound` hypothesis.
- **Context truth.** A context's truth is truth in every field of its characteristic (`means_iff`). This makes `contra` sound for EMPTY vs NOT_IN_IDEAL via the Nullstellensatz over the algebraic closure.
- **Binder.** The binder export (schema v2):
  - collects axioms on the registry's proof terms;
  - checks each entry's proof is the theorem it names;
  - keys records on canonical JSON identity;
  - stamps an environment block that the runtime checks.

Every listed theorem uses only `propext`, `Classical.choice` and `Quot.sound`. The Kernel pin is unchanged since G2.5.

## G3a conditions

| Condition | Status |
|---|---|
| 100% of 3a-owned cases | **Met: 105 cases, 106 rows, 106 agree, 0 losses** ([corpus](PHASE-3A-CORPUS.json)). 19 run through signed instantiation fixtures |
| Zero false ACCEPTs across all profile cases | **Met: 0 in 242** ([safety](PHASE-3A-SAFETY.json)) |
| Reach slice, including Fano and an earned widening | Met (19/19, [slice](PHASE-3A-SLICE.json)). The Fano cases are now corpus cases GP-X413–X415 |
| Checkers admitted | Met: soundness proofs, adversarial controls, build-time `#guard` instances (`GPProfile.RuleChecks`), TCB entries |
| K3 rules carry `carry_kind`, with proved direction tables | Met: `r1_sound`, `r2_sound`, `r3_sound`, `r4_sound`, `cover_rule_sound`, `witness_sound` |
| Binder; A4 policy applied | Met: 9 generated warrants, all bound at their computed reach ([binder](PHASE-3A-BINDER.json)). The runtime refuses a receipt from another environment |
| Oracle disagreements triaged | 25 inferences, 0 disagreements ([differential](PHASE-3A-DIFFERENTIAL.json)) |
| Kernel cases re-executed | 14, all schematic, each recorded with its proved profile analogue ([re-exec](PHASE-3A-KERNEL-REEXEC.json)) |
| Kernel pin unchanged | Met |

Owners after the rulings: 105 3a, 51 3b, 80 campaign-op, 4 census, 2 admission-control; none ambiguous ([expressiveness](PHASE-3A-EXPRESSIVENESS.json)).

## The 3a.1 patch (review rulings 1–8)

1. **Binder holes.** Canonical JSON identity (no `reprStr`); a registry-level axiom audit plus a named-constant check; environment-stamped receipts refused when foreign. The alpha's identity condition is met.
2. **`contra`.** Three pairs:
   - IN_IDEAL(h) vs NOT_IN_IDEAL(h);
   - EMPTY vs NOT_IN_IDEAL(h), by the Nullstellensatz;
   - VANISHES_ON(h) vs NONEMPTY with guard h.
   X124 and X128 file their counterexamples, and a contradicted claim is reported as refuted.
3. **R2/R3 IN_IDEAL** under the sound condition, with a generic `ideal_transport` lemma. Remaining conservatism is in [KNOWN-CONSERVATISM.md](../KNOWN-CONSERVATISM.md).
4. **Geometric nonemptiness.** NONUNIT removed. The bridge rule. NOT_IN_IDEAL(1) under R2/R3 by the radical argument. The `proper` base checker: two rational points with different values, so the equation is non-constant and its ideal proper. Points over ℚ[a]/(m) are R3 maps from (a; {m}).
5. **COVER split trees** and R4 by cover.
6. **Smaller items.**
   - Typed non-evidence: X138's bounded search.
   - Warrants minted at the full computed reach.
   - ℝ/ℂ field-strengthening tags; none apply today, since C01 is EMPTY over ℂ, which is exact.
   - `meta` keys are ignored, and `mechanism` is always a list.
7. **Instantiation fixtures**, signed in `corpus/CHANGES.md`:
   - A11b, A12, A23, C02 and X59 as the review proposed;
   - X49: an unrecognized verifier version, refused as custody;
   - X121, X51, X52 and A22 on the explicit surface;
   - X73–X81 compiled by the v0.37 ladder and depth-6 adapters, with the v0.37 tests' mutations as data.
8. **Owners and intake.** The try-as-3a pass and Will's residue ruling; the Fano intake.

## Findings

- **Inputs often omit the mathematics.** Fourteen 3a-owned cases needed a fixture:
  - X45 and X49 have byte-identical inputs but opposite verdicts;
  - X75–X77 equal their ACCEPT siblings, so the refusal lived only in a label for the old harness;
  - several attempts never appear in the inputs.
  Fixtures make each case a soundness test of supplied data, and a stale fixture fails closed.
- **One semantic choice is 3a-specific.** The binding reads context truth as "every field of this characteristic". That is sound only because 3a scopes are closed under algebraic closure. 3b's ℝ atom breaks this, and 3b must revisit it (DECISIONS.md, 3a.1 builder note).
- **The frontend must never read past a key it does not understand.** This is still the most important safety property. Families declare exact keys at every level.
- **Kernel replay of Hex checkers does not scale.** Warrants come from generated `linear_combination` proofs.

## Convergence (A5)

Over the 3a corpus run with the binder receipt:
- **(a) What accepts.** 46 rows accept, holding 234 requested claims. Most are receipt-backed IN_IDEAL obligations of iso bundles; 7 are rule-derived (R2, R3, bridge).
- **(b) Theorem warrants.** Eight rows also carry standard-axiom warrants for their C1 claims: A08b, C01, X125, X64, X413, A23, C02 and X121.
- **(c) Widenings and kinds.** 71 rows file earned widenings. Held claims by kind: 214 IN_IDEAL, 8 NONEMPTY, 5 EMPTY, 4 NOT_IN_IDEAL, 3 COVER.
- **(d) What limits Lean-theorem coverage** is the generator, which covers C1 over ℚ, not proof cost. GP's distinct contributions remain computed reach, refusal at elaboration and strict well-formedness, custody, and the earned surface.

## Next

On ratification:
- merge to `master`, classifying the new paths in the snapshot;
- prepare `v0.50.0-alpha` per §1.12 (publication needs Will's approval);
- open Phase 4 (census).
