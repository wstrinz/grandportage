import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime

/-! Shared lemma for the §3.6a shadow slice: a prime is nonzero outside its characteristic. -/

namespace GPBinding.Shadow

theorem cast_prime_ne_zero {K : Type*} [Field K] {p : ℕ} (hp : p.Prime)
    (h : ringChar K ≠ p) : (p : K) ≠ 0 := by
  intro hz
  rcases (Nat.dvd_prime hp).mp ((ringChar.spec K p).mp hz) with h1 | h2
  · exact CharP.ringChar_ne_one h1
  · exact h h2

end GPBinding.Shadow
