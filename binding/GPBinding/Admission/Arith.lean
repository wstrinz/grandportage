import GPProfile.Algebra
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Prime

/-!
Arithmetic facts about the executable 3a profile: `isPrime` decides `Nat.Prime`, and
`primeFactors` lists every prime divisor. Reach soundness needs completeness only.
-/

namespace GPBinding.Admission
open GPProfile

theorem isPrime_iff (n : ℕ) : isPrime n = true ↔ n.Prime := by
  rw [Nat.prime_def_le_sqrt]
  simp only [isPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hle hdvd => ?_⟩
    rcases h m (Nat.lt_succ_of_le hle) with hlt | hmod
    · omega
    · exact hmod (Nat.mod_eq_zero_of_dvd hdvd)
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm => ?_⟩
    by_cases hm2 : m < 2
    · exact Or.inl hm2
    · right
      intro hmod
      exact h m (by omega) (Nat.le_of_lt_succ hm) (Nat.dvd_of_mod_eq_zero hmod)

theorem mem_primeFactors {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (hd : p ∣ n) :
    p ∈ primeFactors n := by
  unfold primeFactors
  dsimp only
  split_ifs with h
  · simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
    obtain ⟨hall, hprod⟩ := h
    rw [← hprod] at hd
    obtain ⟨a, ha, hda⟩ := (Nat.Prime.prime hp).dvd_prod_iff.mp hd
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    have hqp : q.Prime := (isPrime_iff q).mp (hall q hq)
    have := (Nat.prime_dvd_prime_iff_eq hp hqp).mp (hp.dvd_of_dvd_pow hda)
    exact this ▸ hq
  · simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, beq_iff_eq]
    exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd hn hd), (isPrime_iff p).mpr hp,
      Nat.mod_eq_zero_of_dvd hd⟩

theorem mem_union {x : ℕ} {a b : List ℕ} : x ∈ union a b ↔ x ∈ a ∨ x ∈ b := by
  simp [union, List.mem_eraseDups]

theorem mem_denominatorPrimes {p : ℕ} {cs : List Rat} {c : Rat} (hc : c ∈ cs) (hp : p.Prime)
    (hd : p ∣ c.den) : p ∈ denominatorPrimes cs := by
  have key : ∀ (acc : List ℕ) (l : List Rat), (p ∈ acc ∨ ∃ c ∈ l, p ∣ c.den) →
      p ∈ l.foldl (fun acc c => union acc (primeFactors c.den)) acc := by
    intro acc l
    induction l generalizing acc with
    | nil => simp
    | cons c l ih =>
      intro h
      apply ih
      rcases h with h | ⟨c', hc', hd'⟩
      · exact Or.inl (mem_union.mpr (Or.inl h))
      · rcases List.mem_cons.mp hc' with rfl | hl
        · exact Or.inl (mem_union.mpr (Or.inr (mem_primeFactors hp c'.den_pos hd')))
        · exact Or.inr ⟨c', hl, hd'⟩
  exact key [] cs (Or.inr ⟨c, hc, hd⟩)

theorem mem_foldl_union_iff {α : Type} {f : α → List ℕ} {x : ℕ} :
    ∀ (l : List α) (acc : List ℕ),
      x ∈ l.foldl (fun acc a => union acc (f a)) acc ↔ x ∈ acc ∨ ∃ a ∈ l, x ∈ f a
  | [], acc => by simp
  | a :: l, acc => by
    rw [List.foldl_cons, mem_foldl_union_iff l, mem_union]
    constructor
    · rintro ((h | h) | ⟨c', hc', h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, List.mem_cons_self, h⟩
      · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', h⟩
    · rintro (h | ⟨c', hc', h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hc' with rfl | hl
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨c', hl, h⟩

theorem primeFactors_one : primeFactors 1 = [] := by decide

theorem mem_denominatorPrimes_iff {x : ℕ} {cs : List Rat} :
    x ∈ denominatorPrimes cs ↔ ∃ c ∈ cs, x ∈ primeFactors c.den := by
  have key : ∀ (acc : List ℕ) (l : List Rat),
      x ∈ l.foldl (fun acc c => union acc (primeFactors c.den)) acc ↔
        x ∈ acc ∨ ∃ c ∈ l, x ∈ primeFactors c.den := by
    intro acc l
    induction l generalizing acc with
    | nil => simp
    | cons c l ih =>
      rw [List.foldl_cons, ih, mem_union]
      constructor
      · rintro ((h | h) | ⟨c', hc', h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨c, List.mem_cons_self, h⟩
        · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', h⟩
      · rintro (h | ⟨c', hc', h⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hc' with rfl | hl
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨c', hl, h⟩
  unfold denominatorPrimes
  rw [key]
  simp

theorem mem_union_left {x : ℕ} {a b : List ℕ} (h : x ∈ a) : x ∈ union a b :=
  mem_union.mpr (Or.inl h)

theorem mem_union_right {x : ℕ} {a b : List ℕ} (h : x ∈ b) : x ∈ union a b :=
  mem_union.mpr (Or.inr h)

end GPBinding.Admission
