/-! ## GPEmpty: frame normalization for `RealizesRank3` (EMPTY claims)

Any realization of a simple rank-3 matroid moves, by an invertible linear map and nonzero
rescalings, to one whose frame columns are `e₀, e₁, e₂` and `e₀ + e₁ + e₂` (`frame4`). Every
determinant keeps its zero-ness, so the moved vectors satisfy the framed system: its equations vanish
and its guards do not (`det_zero_iff`). The claim's ideal certificate is then a polynomial identity
in the free entries, checked per claim by `linear_combination`. Mathlib only; no kernel evaluation. -/

namespace GPEmpty

section
variable {K : Type*} [Field K]

/-- The 3×3 determinant with rows `u`, `v`, `w`. -/
def d3 (u v w : Fin 3 → K) : K :=
  u 0 * v 1 * w 2 - u 0 * v 2 * w 1 - u 1 * v 0 * w 2 + u 1 * v 2 * w 0 + u 2 * v 0 * w 1 - u 2 * v 1 * w 0

def dot (r u : Fin 3 → K) : K := r 0 * u 0 + r 1 * u 1 + r 2 * u 2

def cross (b c : Fin 3 → K) : Fin 3 → K :=
  ![b 1 * c 2 - b 2 * c 1, b 2 * c 0 - b 0 * c 2, b 0 * c 1 - b 1 * c 0]

/-- The linear map with rows `r₀`, `r₁`, `r₂`. -/
def lin (r₀ r₁ r₂ u : Fin 3 → K) : Fin 3 → K := ![dot r₀ u, dot r₁ u, dot r₂ u]

theorem li3 (u v w : Fin 3 → K) : LinearIndependent K ![u, v, w] ↔ d3 u v w ≠ 0 := by
  have h := Matrix.linearIndependent_rows_iff_isUnit (K := K) (A := Matrix.of ![u, v, w])
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_fin_three] at h
  simp [Matrix.row] at h
  exact h

theorem d3_lin (r₀ r₁ r₂ x y z : Fin 3 → K) :
    d3 (lin r₀ r₁ r₂ x) (lin r₀ r₁ r₂ y) (lin r₀ r₁ r₂ z) = d3 r₀ r₁ r₂ * d3 x y z := by
  simp only [d3, lin, dot, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem d3_smul (s t r : K) (x y z : Fin 3 → K) : d3 (s • x) (t • y) (r • z) = s * t * r * d3 x y z := by
  simp only [d3, Pi.smul_apply, smul_eq_mul]; ring

theorem d3_cross (a b c : Fin 3 → K) : d3 (cross b c) (cross c a) (cross a b) = d3 a b c ^ 2 := by
  simp only [d3, cross, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem dot_smul (s : K) (r u : Fin 3 → K) : dot (s • r) u = s * dot r u := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]; ring

theorem dot_cross (a b c : Fin 3 → K) : dot (cross b c) a = d3 a b c := by
  simp only [dot, cross, d3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem d3_cyc (a b c : Fin 3 → K) : d3 b c a = d3 a b c := by simp only [d3]; ring
theorem d3_aab (a b : Fin 3 → K) : d3 a a b = 0 := by simp only [d3]; ring
theorem d3_aba (a b : Fin 3 → K) : d3 a b a = 0 := by simp only [d3]; ring
theorem d3_abb (a b : Fin 3 → K) : d3 a b b = 0 := by simp only [d3]; ring

theorem d3_swap12 (u v w : Fin 3 → K) : d3 u v w = 0 ↔ d3 v u w = 0 := by
  rw [show d3 v u w = -d3 u v w by simp only [d3]; ring, neg_eq_zero]

theorem d3_swap23 (u v w : Fin 3 → K) : d3 u v w = 0 ↔ d3 u w v = 0 := by
  rw [show d3 u w v = -d3 u v w by simp only [d3]; ring, neg_eq_zero]

end

theorem onL_perm {n : ℕ} (lines : List (Finset (Fin n))) {a b c x y z : Fin n}
    (h : ∀ l : Finset (Fin n), (a ∈ l ∧ b ∈ l ∧ c ∈ l ↔ x ∈ l ∧ y ∈ l ∧ z ∈ l)) :
    (∃ l ∈ lines, a ∈ l ∧ b ∈ l ∧ c ∈ l) ↔ ∃ l ∈ lines, x ∈ l ∧ y ∈ l ∧ z ∈ l := by
  simp only [h]

variable {K : Type*} [Field K] {n : ℕ} {lines : List (Finset (Fin n))} {v : Fin n → Fin 3 → K}

/-- In a realization, three distinct elements (in any order) have a vanishing determinant exactly
when some line contains all three. -/
theorem det_zero_iff (hv : RealizesRank3 lines v) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : d3 (v a) (v b) (v c) = 0 ↔ ∃ l ∈ lines, a ∈ l ∧ b ∈ l ∧ c ∈ l := by
  have key : ∀ x y z : Fin n, x < y → y < z →
      (d3 (v x) (v y) (v z) = 0 ↔ ∃ l ∈ lines, x ∈ l ∧ y ∈ l ∧ z ∈ l) := by
    intro x y z hxy hyz
    have h := hv x y z hxy hyz
    rw [li3] at h
    exact ⟨fun h0 => by by_contra hn; exact h.mpr hn h0, fun he => by by_contra h0; exact h.mp h0 he⟩
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases lt_or_gt_of_ne hbc with h3 | h3
  · exact key a b c h1 h3
  · rw [d3_swap23, key a c b h2 h3]; exact onL_perm lines fun l => by tauto
  · exact absurd (h1.trans h3) (not_lt.mpr h2.le)
  · rw [d3_swap23, d3_swap12, key c a b h2 h1]; exact onL_perm lines fun l => by tauto
  · rw [d3_swap12, key b a c h1 h2]; exact onL_perm lines fun l => by tauto
  · exact absurd (h1.trans h2) (not_lt.mpr h3.le)
  · rw [d3_swap12, d3_swap23, key b c a h3 h2]; exact onL_perm lines fun l => by tauto
  · rw [d3_swap12, d3_swap23, d3_swap12, key c b a h3 h1]; exact onL_perm lines fun l => by tauto

theorem smul_vec3 (s x y z : K) : s • ![x, y, z] = ![s * x, s * y, s * z] := by
  funext i; fin_cases i <;> rfl

/-- **Frame normalization.** A realization moves to one with `a, b, c, f` at `e₀, e₁, e₂` and
`e₀ + e₁ + e₂`, when no line contains `a, b, c` or `f` with two of them. -/
theorem frame4 (hv : RealizesRank3 lines v) (a b c f : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hfa : f ≠ a) (hfb : f ≠ b) (hfc : f ≠ c)
    (h₀ : ¬ ∃ l ∈ lines, a ∈ l ∧ b ∈ l ∧ c ∈ l) (h₁ : ¬ ∃ l ∈ lines, f ∈ l ∧ b ∈ l ∧ c ∈ l)
    (h₂ : ¬ ∃ l ∈ lines, a ∈ l ∧ f ∈ l ∧ c ∈ l) (h₃ : ¬ ∃ l ∈ lines, a ∈ l ∧ b ∈ l ∧ f ∈ l) :
    ∃ w : Fin n → Fin 3 → K, RealizesRank3 lines w ∧
      w a = ![1, 0, 0] ∧ w b = ![0, 1, 0] ∧ w c = ![0, 0, 1] ∧ w f = ![1, 1, 1] := by
  have hD : d3 (v a) (v b) (v c) ≠ 0 := fun h => h₀ ((det_zero_iff hv hab hac hbc).mp h)
  have hu₀ : d3 (v f) (v b) (v c) ≠ 0 := fun h => h₁ ((det_zero_iff hv hfb hfc hbc).mp h)
  have hu₁ : d3 (v a) (v f) (v c) ≠ 0 := fun h => h₂ ((det_zero_iff hv hfa.symm hac hfc).mp h)
  have hu₂ : d3 (v a) (v b) (v f) ≠ 0 := fun h => h₃ ((det_zero_iff hv hab hfa.symm hfb.symm).mp h)
  set D := d3 (v a) (v b) (v c) with eD
  set u₀ := d3 (v f) (v b) (v c) with eu₀
  set u₁ := d3 (v a) (v f) (v c) with eu₁
  set u₂ := d3 (v a) (v b) (v f) with eu₂
  set r₀ := u₀⁻¹ • cross (v b) (v c)
  set r₁ := u₁⁻¹ • cross (v c) (v a)
  set r₂ := u₂⁻¹ • cross (v a) (v b)
  set μ : Fin n → K := fun j => if j = a then u₀ / D else if j = b then u₁ / D else if j = c then u₂ / D else 1
  have hμ : ∀ j, μ j ≠ 0 := by
    intro j; simp only [μ]; split_ifs <;> simp [hD, hu₀, hu₁, hu₂]
  have hr : d3 r₀ r₁ r₂ ≠ 0 := by
    simp only [r₀, r₁, r₂]; rw [d3_smul, d3_cross]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero hu₀) (inv_ne_zero hu₁)) (inv_ne_zero hu₂))
      (pow_ne_zero 2 hD)
  have hl : ∀ j, lin r₀ r₁ r₂ (v j) =
      ![u₀⁻¹ * d3 (v j) (v b) (v c), u₁⁻¹ * d3 (v j) (v c) (v a), u₂⁻¹ * d3 (v j) (v a) (v b)] := by
    intro j; simp only [lin, r₀, r₁, r₂, dot_smul, dot_cross]
  refine ⟨fun j => μ j • lin r₀ r₁ r₂ (v j), ?_, ?_, ?_, ?_, ?_⟩
  · intro x y z hxy hyz
    have h := hv x y z hxy hyz
    rw [li3] at h
    rw [li3, d3_smul, d3_lin, ← h]
    exact ⟨fun h h0 => h (by rw [h0, mul_zero, mul_zero]),
      fun h => mul_ne_zero (mul_ne_zero (mul_ne_zero (hμ x) (hμ y)) (hμ z)) (mul_ne_zero hr h)⟩
  · show μ a • lin r₀ r₁ r₂ (v a) = _
    rw [show μ a = u₀ / D by simp [μ], hl, d3_aba, d3_aab, ← eD, smul_vec3]
    ext i; (fin_cases i <;> simp); field_simp
  · show μ b • lin r₀ r₁ r₂ (v b) = _
    rw [show μ b = u₁ / D by simp [μ, hab.symm], hl, d3_aab, d3_aba,
      d3_cyc (v a) (v b) (v c), ← eD, smul_vec3]
    ext i; (fin_cases i <;> simp); field_simp
  · show μ c • lin r₀ r₁ r₂ (v c) = _
    rw [show μ c = u₂ / D by simp [μ, hac.symm, hbc.symm], hl,
      d3_aba, d3_aab, ← d3_cyc (v c) (v a) (v b), ← eD, smul_vec3]
    ext i; (fin_cases i <;> simp); field_simp
  · show μ f • lin r₀ r₁ r₂ (v f) = _
    rw [show μ f = 1 by simp [μ, hfa, hfb, hfc], hl, ← eu₀,
      d3_cyc (v a) (v f) (v c), ← eu₁, ← d3_cyc (v f) (v a) (v b), ← eu₂, smul_vec3]
    ext i; fin_cases i <;> simp <;> field_simp

/-- `s ≠ 0` in a field whose characteristic is outside a list containing the prime `s`. -/
theorem prime_ne_zero {S : List ℕ} (hK : ringChar K ∉ S) {s : ℕ} (hs : s.Prime) (hm : s ∈ S) :
    (s : K) ≠ 0 := by
  intro h0
  have hd := ringChar.dvd h0
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | hq
  · exact hK (by rwa [(Nat.prime_dvd_prime_iff_eq hq hs).mp hd])
  · rw [hq, zero_dvd_iff] at hd; exact hs.ne_zero hd

end GPEmpty
