/-
# Semantic bridge for exact binary product splits

Runtime verifies a finite identity `equation = unit * left * right`. This file
states the domain-level disjunction it supports while leaving model binding,
branch construction, and cover recombination outside the theorem.
-/

import GrandPortage.FactorPower

namespace GrandPortage

universe u

theorem unit_times_product_zero_implies_factor_zero
    {R : Type u} [Mul R] [OfNat R 0] [OfNat R 1]
    (zeroMul : forall r : R, 0 * r = 0)
    (zeroNeOne : Not ((0 : R) = 1))
    (noZeroDivisors : HasNoZeroDivisors (R := R))
    {unit left right : R}
    (unitWitness : HasRightInverse unit)
    (equationZero : (unit * left) * right = 0) :
    left = 0 ∨ right = 0 := by
  cases noZeroDivisors (unit * left) right equationZero with
  | inr rightZero => exact Or.inr rightZero
  | inl unitLeftZero =>
      have unitNonzero :=
        rightInverse_nonzero zeroMul zeroNeOne unitWitness
      cases noZeroDivisors unit left unitLeftZero with
      | inl unitZero => exact False.elim (unitNonzero unitZero)
      | inr leftZero => exact Or.inl leftZero

end GrandPortage
