import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
namespace TimingA05
/-- In characteristic 2, the actual denominator 8 is zero. -/
theorem denominator_eight_zero {R : Type*} [CommRing R] [CharP R 2] :
    (8 : R) = 0 := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  calc
    (8 : R) = (2 : R) * 4 := by norm_num
    _ = 0 := by rw [h2]; simp

/-- GP-A05's denominator cannot be inverted in a nontrivial char-2 ring. -/
theorem denominator_eight_not_unit {R : Type*} [CommRing R]
    [Nontrivial R] [CharP R 2] : ¬ IsUnit (8 : R) := by
  rw [denominator_eight_zero]
  simp

/-- A coefficient representing 3/8 would have to satisfy 8*c = 3; none exists. -/
theorem gp_a05_no_coefficient {R : Type*} [CommRing R]
    [Nontrivial R] [CharP R 2] : ¬ ∃ c : R, (8 : R) * c = 3 := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have h3 : (3 : R) = 1 := by
    calc
      (3 : R) = (2 : R) + 1 := by norm_num
      _ = 1 := by rw [h2]; simp
  rintro ⟨c, hc⟩
  have h01 : (0 : R) = 1 := by
    simpa [denominator_eight_zero, h3] using hc
  exact zero_ne_one h01

/-- Specializing the coefficient obstruction to F_2, rather than an API failure. -/
theorem gp_a05_F2 : ¬ ∃ c : ZMod 2, (8 : ZMod 2) * c = 3 :=
  gp_a05_no_coefficient

/-- A unital Q-ring hom to characteristic 2 would send the rational 3/8 to
an impossible solution of 8*c=3. This is a second precise refusal formulation. -/
theorem gp_a05_no_rat_ring_hom {R : Type*} [CommRing R]
    [Nontrivial R] [CharP R 2] : ¬ Nonempty (ℚ →+* R) := by
  rintro ⟨f⟩
  apply gp_a05_no_coefficient (R := R)
  refine ⟨f (3 / 8), ?_⟩
  have h : (8 : ℚ) * (3 / 8) = 3 := by norm_num
  have hf := congrArg f h
  simpa only [map_mul, map_ofNat] using hf

/-- Totalized division in F_2 exists syntactically, but is not reduction of 3/8. -/
theorem totalized_division_is_zero : (3 : ZMod 2) / (8 : ZMod 2) = 0 := by
  rw [denominator_eight_zero (R := ZMod 2), div_zero]

#print axioms denominator_eight_not_unit
#print axioms gp_a05_no_coefficient
#print axioms gp_a05_F2
#print axioms gp_a05_no_rat_ring_hom
end TimingA05
