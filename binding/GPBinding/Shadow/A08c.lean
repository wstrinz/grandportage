import GPBinding.Shadow.Common

namespace GPBinding.Shadow
open GPBinding.Shadow

/-- GP-A08c: `2x - 1` has a zero in every field of characteristic ≠ 2. -/
theorem a08c (K : Type*) [Field K] (hK : ringChar K ≠ 2) : ∃ x : K, 2 * x - 1 = 0 := by
  have h2 : (2 : K) ≠ 0 := by exact_mod_cast cast_prime_ne_zero Nat.prime_two hK
  exact ⟨2⁻¹, by rw [mul_inv_cancel₀ h2, sub_self]⟩

end GPBinding.Shadow
