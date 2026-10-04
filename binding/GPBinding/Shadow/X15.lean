import GPBinding.Shadow.Common

namespace GPBinding.Shadow
open GPBinding.Shadow

/-- GP-X15: in characteristic 2, `y^2 + 1 = 0·(x+1) + (y+1)·(y+1)` (the ideal-membership
identity), the cross term `2y` vanishing. -/
theorem x15 (K : Type*) [CommRing K] [CharP K 2] (x y : K) :
    y ^ 2 + 1 = 0 * (x + 1) + (y + 1) * (y + 1) := by
  rw [zero_mul, zero_add, ← sq, add_pow_char, one_pow]

end GPBinding.Shadow
