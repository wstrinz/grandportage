import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Nat.Prime.Basic

/-!
Rational coefficients in a field `K` of any characteristic. `Rat.cast` is not a ring hom in
characteristic `p`, but it is one on `Good K`, the rationals whose denominator is a unit in
`K`. `toK` casts a rational polynomial coefficientwise; on polynomials with `Good`
coefficients it agrees with `MvPolynomial.map` along that ring hom, so it respects `+`, `*`.
-/

noncomputable section

namespace GPBinding.Admission
open MvPolynomial

variable (K : Type*) [Field K]

/-- Rationals whose denominator is nonzero in `K`. -/
def Good : Subring Rat where
  carrier := {q | (q.den : K) ≠ 0}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb h
    obtain ⟨t, ht⟩ := Rat.add_den_dvd a b
    apply mul_ne_zero ha hb
    rw [← Nat.cast_mul, ht, Nat.cast_mul, h, zero_mul]
  mul_mem' := by
    intro a b ha hb h
    obtain ⟨t, ht⟩ := Rat.mul_den_dvd a b
    apply mul_ne_zero ha hb
    rw [← Nat.cast_mul, ht, Nat.cast_mul, h, zero_mul]
  neg_mem' := by
    intro a ha
    simpa [Rat.neg_den] using ha

theorem mem_good {K : Type*} [Field K] {q : Rat} : q ∈ Good K ↔ (q.den : K) ≠ 0 := Iff.rfl

/-- `Rat.cast` restricted to `Good K` is a ring hom. -/
def castGood : Good K →+* K where
  toFun q := (q.1 : K)
  map_one' := by simp
  map_zero' := by simp
  map_add' a b := Rat.cast_add_of_ne_zero a.2 b.2
  map_mul' a b := Rat.cast_mul_of_ne_zero a.2 b.2

variable {K}
variable {σ : Type*}

/-- Coefficientwise `Rat.cast` of a rational polynomial. -/
def toK (P : MvPolynomial σ Rat) : MvPolynomial σ K :=
  ∑ d ∈ P.support, monomial d ((coeff d P : Rat) : K)

@[simp] theorem coeff_toK (P : MvPolynomial σ Rat) (d : σ →₀ ℕ) :
    coeff d (toK (K := K) P) = ((coeff d P : Rat) : K) := by
  classical
  rw [toK, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, Rat.cast_zero]

variable (K σ)
/-- Rational polynomials all of whose coefficients are `Good`. -/
def GoodPoly : Subring (MvPolynomial σ Rat) := (MvPolynomial.map (Good K).subtype).range
variable {K σ}

theorem mem_goodPoly {P : MvPolynomial σ Rat} :
    P ∈ GoodPoly K σ ↔ ∀ d, coeff d P ∈ Good K := by
  change P ∈ Set.range (MvPolynomial.map (Good K).subtype) ↔ _
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
  constructor
  · intro h d
    by_cases hd : d ∈ P.support
    · obtain ⟨q, hq⟩ := h (MvPolynomial.coeff_mem_coeffs d (mem_support_iff.mp hd))
      rw [← hq]
      exact q.2
    · rw [notMem_support_iff.mp hd]
      exact (Good K).zero_mem
  · intro h c hc
    obtain ⟨d, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    exact ⟨⟨_, h d⟩, rfl⟩

theorem toK_map (P' : MvPolynomial σ (Good K)) :
    toK (MvPolynomial.map (Good K).subtype P') = MvPolynomial.map (castGood K) P' := by
  ext d
  simp [coeff_map]
  rfl

theorem toK_lift {P : MvPolynomial σ Rat} (hP : P ∈ GoodPoly K σ) :
    ∃ P', P = MvPolynomial.map (Good K).subtype P' ∧ toK P = MvPolynomial.map (castGood K) P' := by
  obtain ⟨P', rfl⟩ := hP
  exact ⟨P', rfl, toK_map P'⟩

theorem toK_add {P Q : MvPolynomial σ Rat} (hP : P ∈ GoodPoly K σ) (hQ : Q ∈ GoodPoly K σ) :
    toK (K := K) (P + Q) = toK P + toK Q := by
  obtain ⟨P', rfl, -⟩ := toK_lift hP
  obtain ⟨Q', rfl, -⟩ := toK_lift hQ
  rw [← map_add, toK_map, toK_map, toK_map, map_add]

theorem toK_sub {P Q : MvPolynomial σ Rat} (hP : P ∈ GoodPoly K σ) (hQ : Q ∈ GoodPoly K σ) :
    toK (K := K) (P - Q) = toK P - toK Q := by
  obtain ⟨P', rfl, -⟩ := toK_lift hP
  obtain ⟨Q', rfl, -⟩ := toK_lift hQ
  rw [← map_sub, toK_map, toK_map, toK_map, map_sub]

theorem toK_mul {P Q : MvPolynomial σ Rat} (hP : P ∈ GoodPoly K σ) (hQ : Q ∈ GoodPoly K σ) :
    toK (K := K) (P * Q) = toK P * toK Q := by
  obtain ⟨P', rfl, -⟩ := toK_lift hP
  obtain ⟨Q', rfl, -⟩ := toK_lift hQ
  rw [← map_mul, toK_map, toK_map, toK_map, map_mul]

theorem toK_pow {P : MvPolynomial σ Rat} (hP : P ∈ GoodPoly K σ) (k : ℕ) :
    toK (K := K) (P ^ k) = toK P ^ k := by
  obtain ⟨P', rfl, -⟩ := toK_lift hP
  rw [← map_pow, toK_map, toK_map, map_pow]

theorem toK_one : toK (K := K) (1 : MvPolynomial σ Rat) = 1 := by
  rw [show (1 : MvPolynomial σ Rat) = MvPolynomial.map (Good K).subtype 1 by simp, toK_map, map_one]

theorem toK_zero : toK (K := K) (0 : MvPolynomial σ Rat) = 0 := by
  rw [show (0 : MvPolynomial σ Rat) = MvPolynomial.map (Good K).subtype 0 by simp, toK_map, map_zero]

theorem toK_list_sum (l : List (MvPolynomial σ Rat)) (hl : ∀ P ∈ l, P ∈ GoodPoly K σ) :
    toK (K := K) l.sum = (l.map (toK (K := K))).sum := by
  induction l with
  | nil => simp [toK_zero]
  | cons P l ih =>
    simp only [List.sum_cons, List.map_cons]
    rw [toK_add (hl P List.mem_cons_self)
      ((GoodPoly K σ).list_sum_mem fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ)),
      ih fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ)]

theorem toK_list_prod (l : List (MvPolynomial σ Rat)) (hl : ∀ P ∈ l, P ∈ GoodPoly K σ) :
    toK (K := K) l.prod = (l.map (toK (K := K))).prod := by
  induction l with
  | nil => simp [toK_one]
  | cons P l ih =>
    simp only [List.prod_cons, List.map_cons]
    rw [toK_mul (hl P List.mem_cons_self)
      ((GoodPoly K σ).list_prod_mem fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ)),
      ih fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ)]

/-! ## When casts vanish -/

theorem ringChar_zero_or_prime : ringChar K = 0 ∨ (ringChar K).Prime :=
  (CharP.char_is_prime_or_zero K (ringChar K)).symm

theorem den_ne_zero_of_primes {q : Rat}
    (h : ∀ p, p.Prime → p ∣ q.den → ringChar K ≠ p) : (q.den : K) ≠ 0 := by
  intro hz
  have hd : ringChar K ∣ q.den := (ringChar.spec K q.den).mp hz
  rcases ringChar_zero_or_prime (K := K) with h0 | hp
  · rw [h0] at hd
    exact q.den_ne_zero (Nat.eq_zero_of_zero_dvd hd)
  · exact h _ hp hd rfl

theorem intCast_ne_zero_of_primes {z : ℤ} (hz : z ≠ 0)
    (h : ∀ p, p.Prime → p ∣ z.natAbs → ringChar K ≠ p) : (z : K) ≠ 0 := by
  intro hc
  have hd : (ringChar K : ℤ) ∣ z := (CharP.intCast_eq_zero_iff K (ringChar K) z).mp hc
  rcases ringChar_zero_or_prime (K := K) with h0 | hp
  · rw [h0, Nat.cast_zero, zero_dvd_iff] at hd
    exact hz hd
  · exact h _ hp (Int.natAbs_dvd_natAbs.mpr hd) rfl

theorem cast_ne_zero_of_primes {q : Rat} (hq : q ≠ 0)
    (hden : ∀ p, p.Prime → p ∣ q.den → ringChar K ≠ p)
    (hnum : ∀ p, p.Prime → p ∣ q.num.natAbs → ringChar K ≠ p) : (q : K) ≠ 0 := by
  rw [Rat.cast_def]
  exact div_ne_zero (intCast_ne_zero_of_primes (Rat.num_ne_zero.mpr hq) hnum)
    (den_ne_zero_of_primes hden)

theorem cast_eq_zero_of_dvd_num {q : Rat} (hq : ((ringChar K : ℕ) : ℤ) ∣ q.num) :
    (q : K) = 0 := by
  rw [Rat.cast_def, (CharP.intCast_eq_zero_iff K (ringChar K) q.num).mpr hq, zero_div]

end GPBinding.Admission

end
