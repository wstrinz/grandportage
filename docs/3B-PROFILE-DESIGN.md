# Phase 3b profile design

Builder, 2026-10-09. Implements the decisions in [3B-CONTEXT-TRUTH-NOTE.md](3B-CONTEXT-TRUTH-NOTE.md): semireal and ℝ contexts, ℝ first, and one summed profile. 3a's code and proofs are reused unchanged. The Kernel is unchanged.

## Statements, scopes, truth

The 3b profile is one `ProfileOps` (executable) plus one `Semantic.Profile` (binding) over field contexts (`FieldCtx`, as in 3a).

| Statement family | Scope | `Holds` at a field K |
| --- | --- | --- |
| `alg s` (a 3a `Stmt`) | `alg sc` (a 3a `Scope`) | 3a's own: truth in every field of K's characteristic |
| `orderFree s` (a 3a `Stmt` of kind EMPTY or NONEMPTY) | `semireal` or `real` | `Admission.Holds K s`: truth in K itself, with no closure over the characteristic |
| `real r e` (a `RealSys` with sign atoms; `e` is EMPTY or NONEMPTY) | `real` | no point, or some point, of r in K, where a sign atom `(p, σ)` reads the sign of p(x) through squares (x ≥ 0 iff x is a square) |
| `realCover r bs` (branches: equations, guards, sign atoms) | `real` | every point of r in K is a point of some branch (3a's `cover` kind) |

Scope membership:
- `alg sc` is 3a's `Scope.mem`;
- `semireal` is `IsSemireal K`;
- `real` is `Nonempty (K ≃+* ℝ)`;
- `ratField` is `Nonempty (K ≃+* ℚ)` (Will, 2026-10-09).

Over ℝ the sign through squares is the usual order. Squares only stand in for the order where a statement has sign atoms, and those are held only at `real`.

**Scope order.** `le` holds within each family as before, plus `real ≤ semireal` and `ratField ≤ semireal`, because ℝ and ℚ are semireal. `ratField` is unrelated to `real` and to every `alg` scope (GP-X56). Nothing relates an `alg` scope to `semireal` or `real` in either direction. This is the refusing control: a ℂ or characteristic-0 claim never reaches the real family by narrowing (GP-A10-C, X343, X345).

**`contra`.** NONEMPTY and EMPTY of the same system in the same family contradict. Families never contradict each other, which is conservative and sound.

## Evidence

| Evidence | Proves | Soundness |
| --- | --- | --- |
| 3a receipts and rules, on `alg` | as in 3a | 3a's theorems, lifted |
| `sos` certificate (`Real/SOS.lean`), all guards or selected ones | `orderFree s` EMPTY at `semireal` | `sosCheck_sound` (`selectGuards_sub`) |
| rational-root certificate (`Real/RootCover.lean`) | `orderFree s` EMPTY at `ratField` | `ratRootCheck_holds` (rational root theorem) |
| selected-root cover (`Real/RootCover.lean`) | `realCover r bs` at `real` | `rootCoverCheck_holds` (Descartes uniqueness, `roots_countP_pos_le_signVariations`, plus a point replay) |
| `realPoint` witness (`Real/RealPoint.lean`) | `real r` NONEMPTY at `real` (and `orderFree s` NONEMPTY when r has no signs) | `pointCheck_sound` (IVT over ℝ) |
| refutation case tree (`Real/CaseTree.lean`, G-6): zero/sign splits; L1b unit steps; L1a collision and ordered leaves | `real r` EMPTY at `real` (and `orderFree s` EMPTY there) | `caseTreeCheck_sound`; P1 as the proved rule `rhombus_relation`, each use citing its edge equations and both diagonal guards; a unit step's derived edge by `unitOk_real` |
| `algPoint` witness plus a Bezout certificate per guard | `alg s` NOT_IN_IDEAL(1) at characteristic 0 | see below |

**`algPoint`.** The witness has a defining polynomial m and coordinates that are polynomials in θ. Every equation reduces to 0 modulo m, and every guard g has a certificate a·g + b·m = 1. In the algebraic closure L̄ of any characteristic-0 field L, any root θ′ of m is a point of the locus: the equations vanish by the identity modulo m, and the guards are nonzero by Bezout. 3a's `warranted_bridge` then gives NOT_IN_IDEAL(1) over L̄, and so over L, because membership maps from L[x] to L̄[x]. This is u(22)'s complex relaxation. It needs no descent theorem, and 3a's `Cert` stays frozen.

## Kind-1 rules (K3, inside the profile)

- **K1a:** `alg s` EMPTY at a scope that includes characteristic 0 gives `orderFree s` EMPTY at `semireal`, because every semireal field has characteristic 0.
- **K1b:** `alg s` NONEMPTY at such a scope gives `orderFree s` NONEMPTY at `real`.
- **Narrowing:** `orderFree s` EMPTY at `semireal` reaches `real` through `le`. That is Kernel K2, not a rule.

There is no rule from the real family into `alg`, and none from `alg` into the real family except K1a and K1b.

## Kummer

Square-class independence starts as a visible OPEN premise (post-G4 §7). Where u(22) needs a nonvanishing, a selected-root sign receipt at `real` can supply it.

## Corpus frontend

The 51 3b-owned cases parse into the summed statements by their `target_context`: `C`, `Q` or `R`, or a characteristic. The frontend refuses detached receipts (X02, X311) through `Receipt.binding`, as 3a does.

## Emitter path (post-G4 §7)

- **`real` NONEMPTY:** `∃ x : Fin n → ℝ, …`, in Mathlib vocabulary.
- **`orderFree` EMPTY at `semireal`:** `∀ K [Field K] [IsSemireal K], ¬ ∃ x, …`.
- **`algPoint`:** the 3a NOT_IN_IDEAL(1) challenge shape that Track E already uses.

## Files

| Owner | Files |
| --- | --- |
| Profile | `Real/SOS.lean`, `Real/RAlg.lean`, `Real/RealPoint.lean`, `Real/Profile.lean` (sum ops, scopes, `le`, `contra`, kind-1 checkers), `Real/AlgPoint.lean` |
| Binding | `Real/SOSSound.lean`, `Real/RAlgSound.lean`, `Real/Profile.lean` (the semantic profile, `le_sound`, `contra_sound`), `Real/AlgPointSound.lean`, `Real/RuleSound.lean` |
