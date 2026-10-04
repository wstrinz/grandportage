import GPBinding.Shadow.Common

namespace GPBinding.Shadow
open GPBinding.Shadow

/-- GP-A04, positive side at p = 3: outside characteristic 3, `3x = 0` forces `x = 0`. -/
theorem a04_reach (K : Type*) [Field K] (hK : ringChar K ≠ 3) (x : K) : 3 * x = 0 → x = 0 := by
  intro h
  have h3 : ((3 : ℕ) : K) ≠ 0 := cast_prime_ne_zero Nat.prime_three hK
  push_cast at h3
  exact (mul_eq_zero.mp h).resolve_left h3

/-- GP-A04 refusal at p = 3: in characteristic 3, `3x = 0` does not force `x = 0`. -/
theorem a04_refusal : ∃ x : ZMod 3, 3 * x = 0 ∧ x ≠ 0 := ⟨1, by decide⟩

/-- GP-A05 refusal: Lean elaborates `3/8` in characteristic 2 as `3 * 8⁻¹ = 3 * 0⁻¹`, the junk
value 0, so the "reduced" identity silently becomes `d2 = h2`; it typechecks, not refuses. -/
theorem a05_junk : (3 : ZMod 2) * (8 : ZMod 2)⁻¹ = 0 := by
  have h8 : (8 : ZMod 2) = 0 := by decide
  rw [h8, ZMod.inv_zero, mul_zero]

end GPBinding.Shadow
