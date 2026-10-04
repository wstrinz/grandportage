import GPBinding.Shadow.Common

namespace GPBinding.Shadow
open GPBinding.Shadow

/-- GP-X125: the unit certificate holds in every field of characteristic outside {2, 23}. -/
theorem x125 (K : Type*) [Field K] (h2 : ringChar K ≠ 2) (h23 : ringChar K ≠ 23) (x y : K) :
    y ^ 2 - x ^ 3 + x - 1 = 0 → 3 * x ^ 2 - 1 = 0 → 2 * y = 0 → False := by
  intro e1 e2 e3
  have h46 : ((2 : ℕ) : K) * ((23 : ℕ) : K) = 0 := by
    push_cast
    linear_combination (-(36 * x + 54)) * e1 + (8 - 12 * x ^ 2 - 18 * x) * e2 + ((18 * x + 27) * y) * e3
  exact mul_ne_zero (cast_prime_ne_zero Nat.prime_two h2)
    (cast_prime_ne_zero (by norm_num) h23) h46

/-- GP-X126 refusal: in characteristic 23 the system has the point (13, 0). -/
theorem x126_refusal : ∃ x y : ZMod 23, y ^ 2 - x ^ 3 + x - 1 = 0 ∧ 3 * x ^ 2 - 1 = 0 ∧ 2 * y = 0 :=
  ⟨13, 0, by decide⟩

end GPBinding.Shadow
