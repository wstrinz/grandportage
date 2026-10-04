import GPBinding.Shadow.Common
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import AutoGeneralization

/-!
§3.6a step 3: each held slice claim stated at the scope the case requested, as typeclass
assumptions, with the same proof idea as its GP certificate. `#autogeneralize!` reports the
weaker assumptions the proof actually needs; compare with the proposer's reach-based widening.
-/

namespace GPBinding.Shadow.Requested
open GPBinding.Shadow

/-- GP-A08b as requested: characteristic 3. GP widens to every field. -/
theorem a08b_char3 {K : Type*} [Field K] [CharP K 3] (x : K) :
    2 * x = 0 → 1 - 2 * x = 0 → False := by
  intro h1 h2
  have h : (1 : K) = 0 := by linear_combination h1 + h2
  exact one_ne_zero h

/-- GP-A08c as requested: characteristic 3. GP widens to char 0 and every prime but 2. -/
theorem a08c_char3 {K : Type*} [Field K] [CharP K 3] : ∃ x : K, 2 * x - 1 = 0 := by
  have hc : ringChar K = 3 := ringChar.eq K 3
  have h2 : (2 : K) ≠ 0 := by exact_mod_cast cast_prime_ne_zero Nat.prime_two (by omega)
  exact ⟨2⁻¹, by rw [mul_inv_cancel₀ h2, sub_self]⟩

/-- GP-X125 as requested: characteristic 0. GP widens to every characteristic but 2, 23. -/
theorem x125_char0 {K : Type*} [Field K] [CharZero K] (x y : K) :
    y ^ 2 - x ^ 3 + x - 1 = 0 → 3 * x ^ 2 - 1 = 0 → 2 * y = 0 → False := by
  intro e1 e2 e3
  have h46 : (46 : K) = 0 := by
    linear_combination (-(36 * x + 54)) * e1 + (8 - 12 * x ^ 2 - 18 * x) * e2 + ((18 * x + 27) * y) * e3
  exact (by norm_num : (46 : K) ≠ 0) h46

/-- GP-FANO-C1 as requested: characteristic 0. GP widens to every characteristic but 2. -/
theorem fano_c1_char0 {K : Type*} [Field K] [CharZero K] (x5 y4 z4 z5 y7 z7 : K) :
    z4 = 0 → x5 = 0 → 1 - y4 = 0 → -x5*y4*z7 + x5*y7*z4 + y4*z5 - y7*z5 - z4 + z7 = 0 →
    1 - z5 = 0 → 1 - z7 = 0 → -y7 = 0 → False := by
  intro h0 h1 h2 h3 h4 h5 h6
  have hz : (2 : K) = 0 := by
    linear_combination (-x5*y7 + 1) * h0 + (y4*z7) * h1 + (z5) * h2 + h3 + (1 - y7) * h4 + h5 - h6
  exact two_ne_zero hz

#autogeneralize! a08b_char3
#autogeneralize! a08c_char3
#autogeneralize! x125_char0
#autogeneralize! fano_c1_char0

end GPBinding.Shadow.Requested
