import GPBinding.Shadow.Common

namespace GPBinding.Shadow
open GPBinding.Shadow

/-- GP-A08b: `2x` and `1 - 2x` have no common zero in any field. -/
theorem a08b (K : Type*) [Field K] (x : K) : 2 * x = 0 → 1 - 2 * x = 0 → False := by
  intro h1 h2
  have h : (1 : K) = 0 := by linear_combination h1 + h2
  exact one_ne_zero h

end GPBinding.Shadow
