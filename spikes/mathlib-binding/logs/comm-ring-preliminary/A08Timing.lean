import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
namespace TimingA08
/-- The exact GP-A08b generators, evaluated at a point in a named ring. -/
def IntegralSystemSolvable (R : Type*) [CommRing R] : Prop :=
  ∃ x : R, 2 * x = 0 ∧ 1 - 2 * x = 0

/-- The integral cofactor identity (both cofactors are 1). -/
theorem integral_unit_identity {R : Type*} [CommRing R] (x : R) :
    (1 : R) = 2 * x + (1 - 2 * x) := by
  ring

/-- The same integral identity excludes a common zero in every nontrivial ring. -/
theorem integral_system_empty {R : Type*} [CommRing R] [Nontrivial R] :
    ¬ IntegralSystemSolvable R := by
  rintro ⟨x, hx, hy⟩
  have h := integral_unit_identity x
  rw [hy, hx] at h
  exact (one_ne_zero : (1 : R) ≠ 0) (by simpa using h)

/-- Actual GP-A08b conclusion: no common zero over F_3 = ZMod 3. -/
theorem gp_a08b_F3 : ¬ IntegralSystemSolvable (ZMod 3) :=
  integral_system_empty

#print axioms integral_unit_identity
#print axioms integral_system_empty
#print axioms gp_a08b_F3
end TimingA08
