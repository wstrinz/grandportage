import GPBinding.Shadow.Common

namespace GPBinding.Shadow
open GPBinding.Shadow

/-- GP-FANO-C1: the Fano incidence system is empty in every field of characteristic ≠ 2.
Guards are dropped: emptiness without them is the stronger statement. -/
theorem fano_c1 (K : Type*) [Field K] (hK : ringChar K ≠ 2) (x5 y4 z4 z5 y7 z7 : K) :
    z4 = 0 → x5 = 0 → 1 - y4 = 0 → -x5*y4*z7 + x5*y7*z4 + y4*z5 - y7*z5 - z4 + z7 = 0 → 1 - z5 = 0 → 1 - z7 = 0 → -y7 = 0 → False := by
  intro h0 h1 h2 h3 h4 h5 h6
  have hz : ((2 : ℕ) : K) = 0 := by push_cast; linear_combination (-x5*y7 + 1) * h0 + (y4*z7) * h1 + (z5) * h2 + (1) * h3 + (1 - y7) * h4 + (1) * h5 + (-1) * h6
  exact cast_prime_ne_zero Nat.prime_two hK hz

end GPBinding.Shadow
