# Phase 3b: the ordered-statement question

Builder, 2026-10-08. A proposal for Will and M1. Post-G2 §5 and post-G3a §6 require this decision before any 3b code. Nothing here is decided.

## The question

The 3a reading of a claim is "true in every field whose characteristic is in the scope". That reading was sound because 3a's statements are settled by characteristic once scopes are closed under algebraic closure. Real statements are not: ℝ and ℂ both have characteristic 0, yet x² + 1 = 0 has a point over ℂ and none over ℝ. Post-G2 §5 offers two shapes:

- **(a)** Keep the field profile. `Holds` quantifies over the orderings of K, and the scope gains class flags (formally real, real closed, algebraically closed).
- **(b)** A separate ordered-field profile with its own contexts, plus a kind-1 translation rule from field statements.

## What u(22) actually needs

From post-G4 §7 and the 3P findings:

1. **Real realizability.** A point over ℝ satisfying the realization system: equations plus non-vanishing conditions. No order atoms appear in it.
2. **Complex realizability**, held as a relaxation of real realizability, with a refusing control showing that a ℂ claim never transports to ℝ.
3. **Square-class independence** (the Kummer split), through a checker or as a visible OPEN premise.
4. **Non-realizability over ℝ**, through Positivstellensatz/SOS certificates. The order is used in the certificate, not in the statement.

None of these needs a statement that quantifies over orderings.

## Proposal: (b), narrowed to two field classes

A 3b profile with two context classes. A claim's scope names one of them.

- **Semireal fields**: fields in which −1 is not a sum of squares. Mathlib calls these `IsSemireal`, and they are the orderable fields. Examples: ℚ, ℝ, every real closed field.
- **Real closed fields** (RCF): Mathlib's `IsRealClosed`, which extends `IsSemireal`.

A claim at semireal scope means "true in every semireal field"; one at RCF scope means "true in every real closed field". Both include ℝ, so "over ℝ" is what the user reads. Corpus case GP-A10-Q (no point of x² + 1 = 0 in ℚ, ACCEPT) is why the semireal class exists: ℚ is semireal but not real closed.

- **No ordering quantification.** An RCF has exactly one ordering, and it is definable (x ≥ 0 ⇔ ∃ y, x = y²). So order atoms, if a later case needs them, have one meaning, with no choice of ordering. This drops (a)'s main cost.
- **Every check is literal, with no transfer theorem.**
  - A real algebraic witness (isolating intervals, equation replay) is a point of ℚ's real closure, which embeds into every RCF, ℝ included. NONEMPTY claims are held at RCF scope; ℚ has no √2.
  - A Positivstellensatz/SOS certificate refutes the system in every semireal field: it reduces to `-1` being a sum of squares there. So EMPTY claims are held at semireal scope, which covers ℚ and every RCF.
  - Order atoms occur only at selected real roots (cases X351–X354, X404, X405). They are read in the RCF's unique ordering.
  - Neither step needs Tarski transfer, which Mathlib does not have.
- **3a stays frozen.** The algebraic profile's `Scope`, kinds and proofs are untouched. (a) would change 3a's `Scope` type and re-open its soundness proofs, which DECISIONS 2026-10-06 froze.
- **Kind-1 rules**, each a short soundness lemma:
  - *char 0 → semireal:* a 3a claim held at characteristic 0 holds at semireal scope, because every semireal field has characteristic 0.
  - *semireal → RCF:* restriction to the subclass.
  - *RCF → algebraically closed, characteristic 0:* a real algebraic witness lies in ℚ̄, which embeds into every algebraically closed field of characteristic 0. This is u(22)'s complex relaxation.
  - *No rule from algebraically closed to semireal or RCF.* The refusing controls (GP-A10-C, GP-X345; x² + 1 = 0) show that the scope order never relates them.
- **Kummer.** Square-class independence is a fact about specific rationals, not about RCF contexts. Exact prime factorization checks multiplicative independence modulo squares. Until that checker exists it stays an OPEN premise, as post-G4 §7 allows. It needs no new context either way.
- **Emitter path** (post-G4 §7). RCF claims emit as Comparator challenges over ℝ, `∃ x : Fin n → ℝ, …`, in plain Mathlib vocabulary. The solution proves them from the witness or the certificate. The "every RCF" generality stays in GP's held meaning; the challenge states the ℝ instance users care about.

## Corpus fit (51 3b-owned cases)

| Group | Cases | Where they land |
| --- | --- | --- |
| Positivstellensatz/SOS refutation | A10-Q, A10-R, X01, X02, X308–X311 | semireal scope |
| ℂ refusals | A10-C, X343, X345 | refusing controls; no rule into semireal/RCF |
| Selected real roots, signs and intervals | X273–X280, X351–X354, X404, X405 | RCF scope, isolating intervals |
| Number-field points | X347–X350, A11a, X48, X56, A07a/b | the post-G2 §5 number-field signature; unaffected by this choice |
| Sections, outputs, finite quotients, residuals, covers | X255–X262, X319, X320, X332–X336, X368, X369 | receipt binding; unaffected by this choice |

## What it costs

- A new Kernel-facing context, but no Kernel change: the profile supplies `Ctx` and `Holds`, as 3a does.
- A definition of real closed field: none needed. Mathlib at the binding's pin has `IsRealClosed` (`Mathlib/FieldTheory/IsRealClosed/Basic.lean`), so RCF contexts and their Comparator challenges use Mathlib vocabulary directly.
- Checkers, as post-G2 §5 already plans: real algebraic points (AFP *Algebraic_Numbers* as the reference) and exact SOS with LDLᵀ.

## When (a) would be needed instead

Only for statements whose truth depends on choosing an ordering of a field that is not real closed. Examples are ordered number fields with several orderings, or "positive in some ordering". No u(22) or Cloquet move is of that kind. If one appears, (a)'s quantification can be added as a later profile without disturbing this one.

## Decision requested

Adopt (b) narrowed to semireal and RCF contexts, with the rules and refusing controls above, and M1 to confirm:

1. that the RCF reading is the intended meaning of "realizable over ℝ" in the u(22) goal;
2. that no Cloquet move needs ordering quantification.

## Revision 2026-10-09: ℝ first, and M1's corrections

Will decided ("ℝ first"). The real contexts are staged:
- **Stage 1:** the **semireal** class, plus **the field ℝ itself**.
  - NONEMPTY witnesses, selected-root signs and EMPTY claims with order atoms are held over ℝ. That is exactly u(22)'s "22 points in ℝ²".
  - The soundness proof uses Mathlib's intermediate value theorem. Proving the same in every RCF would take about 800–1,500 lines (IVT in an arbitrary RCF, via Galois theory and Sylow).
- **Later:** the RCF class, only if a case needs that generality. None found.

The M1 analysis (all 51 cases plus the u(22) and Cloquet moves) confirms the fit and corrects this note:
1. Semireal scope is for **order-free** claims only, such as SOS refutations of polynomial systems. EMPTY claims that contain order atoms are held over ℝ.
2. Order atoms also occur in A11a (`x > 0`) and in Cloquet's multivariate sign conditions, not only in the six cases listed above.
3. The ℂ relaxation targets 3a's existing **NOT_IN_IDEAL(1) at characteristic 0**, not a new algebraically closed class.
4. Regrouping in the corpus table:
   - X275–X280 are point-universe controls;
   - A07a/b are image-versus-closure controls;
   - X56 is a base-change refusal;
   - A11a is a sign control;
   - X343 is an authority control over ℝ.
   All still fit.
5. Checker conventions that the cases force: closed isolating intervals (X353, X405), square-free counting (X351), and `lo < hi` checked first (X404).

**Profile shape.** K3 rules, kind-1 included, act within one profile. So 3b is a new profile whose statements and scopes are the sum of 3a's (reused unchanged) and the real ones, over field contexts. Sign atoms are read through squares (x ≥ 0 iff x is a square), which over ℝ is the usual order. 3a's code and proofs are untouched, and the Kernel stays generic.

**Open for Phase 5.** Combining census claims with 3b claims in one u(22) ledger.
