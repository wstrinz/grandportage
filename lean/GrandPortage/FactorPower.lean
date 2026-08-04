/-
# Semantic bridge for exact factor-power receipts

The runtime checker proves an exact polynomial identity

    equation = unit * base^k,  k > 0.

This file isolates the extra semantic premises needed to conclude that `base`
vanishes at an interpreted point. It deliberately assumes only the fragment
needed by the argument, keeping the proof Mathlib-free.
-/

namespace GrandPortage

universe u

/-- A strictly positive power of `base`. Unlike `PowerOf` in Localization,
this relation has no exponent-zero constructor. -/
inductive PositivePowerOf {R : Type u} [Mul R] (base : R) : R -> Prop
  | one : PositivePowerOf base base
  | step {power : R} :
      PositivePowerOf base power -> PositivePowerOf base (base * power)

/-- The exact cancellation property needed from the interpreted target. -/
def HasNoZeroDivisors {R : Type u} [Mul R] [OfNat R 0] : Prop :=
  forall a b : R, a * b = 0 -> a = 0 ∨ b = 0

/-- A small witness that an interpreted scalar is a unit. -/
def HasRightInverse {R : Type u} [Mul R] [OfNat R 1]
    (unit : R) : Prop :=
  Exists fun inverse => unit * inverse = 1

theorem rightInverse_nonzero
    {R : Type u} [Mul R] [OfNat R 0] [OfNat R 1]
    (zeroMul : forall r : R, 0 * r = 0)
    (zeroNeOne : Not ((0 : R) = 1))
    {unit : R} (unitWitness : HasRightInverse unit) :
    Not (unit = 0) := by
  intro unitZero
  let inverse := unitWitness.choose
  have inverseLaw := unitWitness.choose_spec
  apply zeroNeOne
  calc
    (0 : R) = 0 * inverse := (zeroMul inverse).symm
    _ = unit * inverse := by rw [unitZero]
    _ = 1 := inverseLaw
theorem positivePower_zero_implies_base_zero
    {R : Type u} [Mul R] [OfNat R 0]
    (noZeroDivisors : HasNoZeroDivisors (R := R))
    {base power : R}
    (positivePower : PositivePowerOf base power)
    (powerZero : power = 0) :
    base = 0 := by
  induction positivePower with
  | one => exact powerZero
  | step prior inductionHypothesis =>
      cases noZeroDivisors base _ powerZero with
      | inl baseZero => exact baseZero
      | inr priorZero => exact inductionHypothesis priorZero

/-- The semantic theorem behind a verified `factor_power_v1` receipt.

Runtime checks the factor identity and the syntactic unit monomial. A consumer
must still establish that the equation evaluates to zero, the scalar evaluates
to a unit, and the target has no zero divisors. -/
theorem unit_times_positive_power_zero_implies_base_zero
    {R : Type u} [Mul R] [OfNat R 0] [OfNat R 1]
    (zeroMul : forall r : R, 0 * r = 0)
    (zeroNeOne : Not ((0 : R) = 1))
    (noZeroDivisors : HasNoZeroDivisors (R := R))
    {unit base power : R}
    (unitWitness : HasRightInverse unit)
    (positivePower : PositivePowerOf base power)
    (equationZero : unit * power = 0) :
    base = 0 := by
  have unitNonzero := rightInverse_nonzero zeroMul zeroNeOne unitWitness
  have powerZero : power = 0 :=
    (noZeroDivisors unit power equationZero).resolve_left unitNonzero
  exact positivePower_zero_implies_base_zero
    noZeroDivisors positivePower powerZero

/-- Compositional semantic linker for the JC p-axis contradiction.

The runtime affine pass checks the two substitution identities represented by
`consequenceAtBaseZero`. Binding both recorded equations to one model supplies
their vanishing hypotheses. The only conclusion here is inconsistency of those
premises; graph-level emptiness remains a separate authority decision. -/
theorem factorPower_and_unitConsequence_are_incompatible
    {R : Type u} [Mul R] [OfNat R 0] [OfNat R 1]
    (zeroMul : forall r : R, 0 * r = 0)
    (zeroNeOne : Not ((0 : R) = 1))
    (noZeroDivisors : HasNoZeroDivisors (R := R))
    {factorUnit base power consequence residual : R}
    (factorUnitWitness : HasRightInverse factorUnit)
    (positivePower : PositivePowerOf base power)
    (factorEquationZero : factorUnit * power = 0)
    (consequenceZero : consequence = 0)
    (consequenceAtBaseZero : base = 0 -> consequence = residual)
    (residualWitness : HasRightInverse residual) :
    False := by
  have baseZero :=
    unit_times_positive_power_zero_implies_base_zero
      zeroMul zeroNeOne noZeroDivisors factorUnitWitness positivePower
      factorEquationZero
  have consequenceEqualsResidual := consequenceAtBaseZero baseZero
  apply rightInverse_nonzero zeroMul zeroNeOne residualWitness
  rw [← consequenceEqualsResidual]
  exact consequenceZero
end GrandPortage
