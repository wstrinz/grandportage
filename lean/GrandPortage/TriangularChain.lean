/-
# Ordered solve chains compose semantically

The runtime `localized_triangular_solve_chain_v1` checker validates exact
ordered polynomial substitutions and state fingerprints. It does not mint
this semantic premise. Once every checked solve step has been bound to a
`MappedEquivalence`, however, the entire chain is one mapped equivalence and
emptiness moves in both directions.
-/

import GrandPortage.MappedEquivalence
import GrandPortage.FactorPower

namespace GrandPortage

universe u

/-- Runtime v2 checks `equation = unit * affine + contextDebt`. If the
normalization equations make `contextDebt` zero and the checked coefficient is
interpreted as a unit, equation vanishing forces the normalized affine form to
vanish. -/
theorem normalizedAffine_zero_of_equation_zero
    {R : Type u} [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
    (zeroMul : forall r : R, 0 * r = 0)
    (addZero : forall r : R, r + 0 = r)
    (zeroNeOne : Not ((0 : R) = 1))
    (noZeroDivisors : HasNoZeroDivisors (R := R))
    {equation unit affine contextDebt : R}
    (unitWitness : HasRightInverse unit)
    (receipt : equation = unit * affine + contextDebt)
    (equationZero : equation = 0)
    (contextZero : contextDebt = 0) :
    affine = 0 := by
  have productZero : unit * affine = 0 := by
    calc
      unit * affine = unit * affine + 0 := (addZero _).symm
      _ = unit * affine + contextDebt := by rw [contextZero]
      _ = equation := receipt.symm
      _ = 0 := equationZero
  have unitNonzero := rightInverse_nonzero zeroMul zeroNeOne unitWitness
  exact (noZeroDivisors unit affine productZero).resolve_left unitNonzero

/-- The reverse implication uses only the checked receipt and ordinary zero
laws: a solved affine form plus vanishing normalization debt satisfies the
original equation. -/
theorem normalizedEquation_zero_of_affine_zero
    {R : Type u} [Mul R] [Add R] [OfNat R 0]
    (mulZero : forall r : R, r * 0 = 0)
    (zeroAdd : forall r : R, 0 + r = r)
    {equation unit affine contextDebt : R}
    (receipt : equation = unit * affine + contextDebt)
    (affineZero : affine = 0)
    (contextZero : contextDebt = 0) :
    equation = 0 := by
  calc
    equation = unit * affine + contextDebt := receipt
    _ = unit * 0 + 0 := by rw [affineZero, contextZero]
    _ = 0 := by rw [mulZero, zeroAdd]

/-- Together these are the semantic normalization law a v2 solve step still
must bind at its interpreted model. -/
theorem normalizedEquation_zero_iff_affine_zero
    {R : Type u} [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
    (zeroMul : forall r : R, 0 * r = 0)
    (mulZero : forall r : R, r * 0 = 0)
    (addZero : forall r : R, r + 0 = r)
    (zeroAdd : forall r : R, 0 + r = r)
    (zeroNeOne : Not ((0 : R) = 1))
    (noZeroDivisors : HasNoZeroDivisors (R := R))
    {equation unit affine contextDebt : R}
    (unitWitness : HasRightInverse unit)
    (receipt : equation = unit * affine + contextDebt)
    (contextZero : contextDebt = 0) :
    equation = 0 <-> affine = 0 :=
  Iff.intro
    (fun equationZero => normalizedAffine_zero_of_equation_zero
      zeroMul addZero zeroNeOne noZeroDivisors unitWitness receipt
      equationZero contextZero)
    (fun affineZero => normalizedEquation_zero_of_affine_zero
      mulZero zeroAdd receipt affineZero contextZero)

/-- The equation adjoined by the runtime localization compiler supplies the
unit witness required by the semantic solve-step theorem. This is the precise
bridge used when a principal open is algebraized with an inverse coordinate. -/
theorem normalizedEquation_zero_iff_affine_zero_of_inverseEquation
    {R : Type u} [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
    (zeroMul : forall r : R, 0 * r = 0)
    (mulZero : forall r : R, r * 0 = 0)
    (addZero : forall r : R, r + 0 = r)
    (zeroAdd : forall r : R, 0 + r = r)
    (zeroNeOne : Not ((0 : R) = 1))
    (noZeroDivisors : HasNoZeroDivisors (R := R))
    {equation unit inverse affine contextDebt : R}
    (inverseEquation : unit * inverse = 1)
    (receipt : equation = unit * affine + contextDebt)
    (contextZero : contextDebt = 0) :
    equation = 0 <-> affine = 0 :=
  normalizedEquation_zero_iff_affine_zero
    zeroMul mulZero addZero zeroAdd zeroNeOne noZeroDivisors
    ⟨inverse, inverseEquation⟩ receipt contextZero

/-- On a principal open, an affine equation with a two-sided inverse is exactly
the translated zero-coordinate equation used by the depth-6 generic stratum
compiler. The explicit laws keep this bridge independent of Mathlib. -/
theorem affineEquation_zero_iff_shift_zero_of_inverse
    {R : Type u} [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
    (mulAssoc : forall a b c : R, (a * b) * c = a * (b * c))
    (mulAdd : forall a b c : R, a * (b + c) = a * b + a * c)
    (oneMul : forall r : R, 1 * r = r)
    (mulZero : forall r : R, r * 0 = 0)
    {coefficient inverse pivot constant : R}
    (rightInverse : coefficient * inverse = 1)
    (leftInverse : inverse * coefficient = 1) :
    coefficient * pivot + constant = 0 <->
      pivot + inverse * constant = 0 := by
  constructor
  · intro equationZero
    calc
      pivot + inverse * constant =
          1 * pivot + inverse * constant := by rw [oneMul]
      _ = (inverse * coefficient) * pivot + inverse * constant := by
            rw [leftInverse]
      _ = inverse * (coefficient * pivot) + inverse * constant := by
            rw [mulAssoc]
      _ = inverse * (coefficient * pivot + constant) := by
            rw [mulAdd]
      _ = inverse * 0 := by rw [equationZero]
      _ = 0 := mulZero inverse
  · intro shiftedZero
    calc
      coefficient * pivot + constant =
          coefficient * pivot + 1 * constant := by rw [oneMul]
      _ = coefficient * pivot + (coefficient * inverse) * constant := by
            rw [rightInverse]
      _ = coefficient * pivot + coefficient * (inverse * constant) := by
            rw [mulAssoc]
      _ = coefficient * (pivot + inverse * constant) := by
            rw [mulAdd]
      _ = coefficient * 0 := by rw [shiftedZero]
      _ = 0 := mulZero coefficient

/-- On the discriminant stratum the affine coefficient is a multiple of a
vanishing factor, so the boundary equation is exactly its constant term. -/
theorem affineEquation_zero_iff_constant_zero_of_factor_zero
    {R : Type u} [Mul R] [Add R] [OfNat R 0]
    (mulZero : forall r : R, r * 0 = 0)
    (zeroMul : forall r : R, 0 * r = 0)
    (zeroAdd : forall r : R, 0 + r = r)
    {scale discriminant pivot constant : R}
    (discriminantZero : discriminant = 0) :
    (scale * discriminant) * pivot + constant = 0 <-> constant = 0 := by
  have collapse : (scale * discriminant) * pivot + constant = constant := by
    rw [discriminantZero, mulZero, zeroMul, zeroAdd]
  rw [collapse]

/-- Identity is a mapped equivalence. -/
def MappedEquivalence.refl {A : Type u} (model : Model A) :
    MappedEquivalence model model where
  forward := id
  backward := id
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  forward_maps := by intro _ hx; exact hx
  backward_maps := by intro _ hx; exact hx

/-- An explicitly ordered sequence of mapped-equivalent model states. The
intermediate point types may differ, which accommodates actual coordinate
elimination rather than pretending every step is literal containment. -/
inductive MappedEquivalenceChain :
    {A B : Type u} -> Model A -> Model B -> Type (u + 1) where
  | nil {A : Type u} (model : Model A) :
      MappedEquivalenceChain model model
  | cons {A B C : Type u}
      {src : Model A} {mid : Model B} {dst : Model C}
      (head : MappedEquivalence src mid)
      (tail : MappedEquivalenceChain mid dst) :
      MappedEquivalenceChain src dst

/-- A checked sequence composes to one endpoint equivalence. -/
def MappedEquivalenceChain.toMappedEquivalence
    {A B : Type u} {src : Model A} {dst : Model B}
    (chain : MappedEquivalenceChain src dst) :
    MappedEquivalence src dst :=
  match chain with
  | .nil model => MappedEquivalence.refl model
  | .cons head tail => head.trans tail.toMappedEquivalence

/-- A chain transports witnesses from its initial state to its final state. -/
theorem MappedEquivalenceChain.hasPoint_forward
    {A B : Type u} {src : Model A} {dst : Model B}
    (chain : MappedEquivalenceChain src dst) :
    HasPoint src -> HasPoint dst :=
  chain.toMappedEquivalence.hasPoint_forward

/-- A chain reconstructs initial witnesses from final witnesses. -/
theorem MappedEquivalenceChain.hasPoint_backward
    {A B : Type u} {src : Model A} {dst : Model B}
    (chain : MappedEquivalenceChain src dst) :
    HasPoint dst -> HasPoint src :=
  chain.toMappedEquivalence.hasPoint_backward

/-- Final-state emptiness licenses initial-state emptiness. -/
theorem MappedEquivalenceChain.isEmpty_backward
    {A B : Type u} {src : Model A} {dst : Model B}
    (chain : MappedEquivalenceChain src dst) :
    IsEmpty dst -> IsEmpty src :=
  fun emptyDst x hx =>
    Exists.elim (chain.hasPoint_forward (Exists.intro x hx))
      (fun y hy => emptyDst y hy)

/-- Initial-state emptiness also licenses final-state emptiness. -/
theorem MappedEquivalenceChain.isEmpty_forward
    {A B : Type u} {src : Model A} {dst : Model B}
    (chain : MappedEquivalenceChain src dst) :
    IsEmpty src -> IsEmpty dst :=
  fun emptySrc y hy =>
    Exists.elim (chain.hasPoint_backward (Exists.intro y hy))
      (fun x hx => emptySrc x hx)

/-- A semantically bound ordered solve chain preserves emptiness exactly. -/
theorem MappedEquivalenceChain.isEmpty_iff
    {A B : Type u} {src : Model A} {dst : Model B}
    (chain : MappedEquivalenceChain src dst) :
    IsEmpty src <-> IsEmpty dst :=
  Iff.intro chain.isEmpty_forward chain.isEmpty_backward

end GrandPortage
