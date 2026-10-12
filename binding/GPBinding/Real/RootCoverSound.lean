import GPBinding.Real.Profile
import GPBinding.Real.SOSSound
import GPBinding.Real.RAlgSound
import GPBinding.Real.NumberFieldSound
import GPProfile.Real.RootCover
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.Real.Sqrt

/-!
Soundness of the selected-root cover and rational-root checkers (`GPProfile.Real.RootCover`).

- **Descartes' bound** (`atMostOneRoot_sound`). The Möbius transform `T` of `m` on `(lo, hi)`
  sends `y ∈ (lo, hi)` to `t = (y - lo)/(hi - y) > 0` with `T(t) = k^d · m(y)`, `k > 0`; distinct
  `y` give distinct `t`. Coefficients of one sign below an index and the other sign from it on give
  at most one sign variation, and Mathlib's `Polynomial.roots_countP_pos_le_signVariations`
  bounds the positive roots of `T` by it: so `m` has at most one root in `(lo, hi)`.
- **Covers** (`rootCoverCheck_holds`). The point replay of the parent joined with a branch gives
  a real root of `m` in `(lo, hi)` meeting the branch; every parent point is a root of `m` in
  `(lo, hi)`, hence that root. Transported to every field isomorphic to ℝ.
- **Rational roots** (`ratRootCheck_holds`). Mathlib's rational root theorem, as in
  `NumberField.rrtOk_irreducible`, in any degree; transported to every field isomorphic to ℚ.
-/

noncomputable section

namespace GPBinding.Real.RootCover
open GPProfile GPProfile.Real HexPolyMathlib Polynomial Set
open GPBinding.Real.RAlg (rv rv_eq_sum rv_fieldEval rv_ratCast rv_zero rv_X rv_add rv_mul rv_C)

/-! ## Sign variations -/

theorem sv_zero_of_nonneg (P : ℝ[X]) (h : ∀ i, 0 ≤ P.coeff i) : P.signVariations = 0 := by
  induction hn : P.support.card using Nat.strong_induction_on generalizing P with
  | _ n ih =>
  by_cases hP : P = 0
  · simp [hP]
  have hE : ∀ i, 0 ≤ P.eraseLead.coeff i := fun i => by
    rw [eraseLead_coeff]; split_ifs
    · exact le_rfl
    · exact h i
  have ihE := ih _ (hn ▸ eraseLead_support_card_lt hP) P.eraseLead hE rfl
  rw [signVariations_eq_eraseLead_add_ite hP, ihE]
  have hl : 0 < P.leadingCoeff := lt_of_le_of_ne (h P.natDegree) (Ne.symm (leadingCoeff_ne_zero.mpr hP))
  rw [sign_pos hl]
  rcases (hE P.eraseLead.natDegree).lt_or_eq with h1 | h1
  · rw [show P.eraseLead.leadingCoeff = P.eraseLead.coeff P.eraseLead.natDegree from rfl, sign_pos h1]
    decide
  · rw [show P.eraseLead.leadingCoeff = P.eraseLead.coeff P.eraseLead.natDegree from rfl, ← h1, sign_zero]
    decide

/-- Coefficients `≥ 0` below `k` and `≤ 0` from `k` on: at most one sign variation. -/
theorem sv_le_one_of_switch (k : ℕ) (P : ℝ[X]) (hlo : ∀ i < k, 0 ≤ P.coeff i)
    (hhi : ∀ i, k ≤ i → P.coeff i ≤ 0) : P.signVariations ≤ 1 := by
  induction hn : P.support.card using Nat.strong_induction_on generalizing P with
  | _ n ih =>
  have nonneg : ∀ Q : ℝ[X], Q.natDegree < k → (∀ i < k, 0 ≤ Q.coeff i) → ∀ i, 0 ≤ Q.coeff i :=
    fun Q hd hq i => by
      by_cases hi : i < k
      · exact hq i hi
      · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
  by_cases hP : P = 0
  · simp [hP]
  by_cases hd : P.natDegree < k
  · rw [sv_zero_of_nonneg P (nonneg P hd hlo)]; omega
  have hlead : P.leadingCoeff < 0 := lt_of_le_of_ne (hhi _ (by omega)) (leadingCoeff_ne_zero.mpr hP)
  have hElo : ∀ i < k, 0 ≤ P.eraseLead.coeff i := fun i hi => by
    rw [eraseLead_coeff]; split_ifs
    · exact le_rfl
    · exact hlo i hi
  have hEhi : ∀ i, k ≤ i → P.eraseLead.coeff i ≤ 0 := fun i hi => by
    rw [eraseLead_coeff]; split_ifs
    · exact le_rfl
    · exact hhi i hi
  rw [signVariations_eq_eraseLead_add_ite hP, sign_neg hlead]
  by_cases hE : P.eraseLead = 0
  · rw [hE]; simp
  by_cases hEd : P.eraseLead.natDegree < k
  · rw [sv_zero_of_nonneg _ (nonneg _ hEd hElo)]; split_ifs <;> omega
  · have hl : P.eraseLead.leadingCoeff < 0 :=
      lt_of_le_of_ne (hEhi _ (by omega)) (leadingCoeff_ne_zero.mpr hE)
    rw [sign_neg hl, ite_cond_eq_false _ _ (eq_false (by decide))]
    have := ih _ (hn ▸ eraseLead_support_card_lt hP) P.eraseLead hElo hEhi rfl
    omega

/-- Descartes: two distinct positive roots need two sign variations. -/
theorem two_pos_roots {P : ℝ[X]} (hP : P ≠ 0) (hsv : P.signVariations ≤ 1) {s t : ℝ} (hs : 0 < s)
    (ht : 0 < t) (hst : s ≠ t) (hrs : P.eval s = 0) (hrt : P.eval t = 0) : False := by
  have hle := roots_countP_pos_le_signVariations P
  have hsub : ({s, t} : Multiset ℝ) ≤ P.roots.filter (0 < ·) := by
    rw [Multiset.le_iff_subset (by simp [hst])]
    intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rw [Multiset.mem_filter]
    rcases hx with rfl | rfl
    · exact ⟨(mem_roots hP).mpr hrs, hs⟩
    · exact ⟨(mem_roots hP).mpr hrt, ht⟩
  have h2 := Multiset.card_le_card hsub
  rw [← Multiset.countP_eq_card_filter] at h2
  simp only [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton] at h2
  omega

/-! ## The Möbius transform -/

theorem rv_mobius (g : RAlg.D) {c d : ℚ} {y : ℝ} (hu : (0 : ℝ) < d - y) :
    rv (RAlg.mobius g c d) ((y - c) / (d - y)) = ((d - c) / (d - y)) ^ (g.size - 1) * rv g y := by
  set t : ℝ := (y - c) / (d - y) with ht_def
  set k : ℝ := (d - c) / (d - y) with hk_def
  have hL : rv (RAlg.C c + RAlg.C d * RAlg.X) t = y * k := by
    simp only [rv_add, rv_mul, rv_C, rv_X, ht_def, hk_def]
    field_simp
    ring
  have hO : rv (RAlg.C 1 + RAlg.X) t = k := by
    simp only [rv_add, rv_C, rv_X, ht_def, hk_def, Rat.cast_one]
    field_simp
    ring
  rw [RAlg.mobius, GPBinding.Real.RAlg.rv_mobiusGo, hL, hO, rv_eq_sum g y, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ g.size - 1 := by have := Finset.mem_range.mp hi; omega
  rw [mul_pow, show k ^ (g.size - 1) = k ^ i * k ^ (g.size - 1 - i) by
    rw [← pow_add, Nat.add_sub_cancel' hi']]
  ring

/-- **Descartes' bound is sound**: an accepted `atMostOneRoot` leaves `m` at most one root in
`(lo, hi)`. -/
theorem atMostOneRoot_sound {m : RAlg.D} {lo hi : ℚ} (h : atMostOneRoot m lo hi = true) {x y : ℝ}
    (hx : x ∈ Ioo (lo : ℝ) hi) (hy : y ∈ Ioo (lo : ℝ) hi) (hmx : rv m x = 0) (hmy : rv m y = 0) :
    x = y := by
  by_contra hxy
  unfold atMostOneRoot oneSwitch at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range, bne_iff_ne,
    ne_eq, Bool.or_eq_true] at h
  obtain ⟨hlohi, ⟨j, -, hj0⟩, k, -, hsw⟩ := h
  set T := RAlg.mobius m lo hi
  set P : ℝ[X] := (toPolynomial T).map (Rat.castHom ℝ) with hPdef
  have hPc : ∀ i, P.coeff i = (T.coeff i : ℝ) := fun i => by
    rw [hPdef, coeff_map, coeff_toPolynomial]; rfl
  have hPe : ∀ t, P.eval t = rv T t := fun t => by rw [hPdef, eval_map]; rfl
  have hP0 : P ≠ 0 := fun h0 => hj0 (by
    have h1 := hPc j
    rw [h0, Polynomial.coeff_zero] at h1
    exact_mod_cast h1.symm)
  have hz : ∀ i, T.size ≤ i → (T.coeff i : ℝ) = 0 := fun i hi => by
    rw [Hex.DensePoly.coeff_eq_zero_of_size_le T hi]; exact Rat.cast_zero
  have hsv : P.signVariations ≤ 1 := by
    unfold switchAt at hsw
    rcases hsw with hsw | hsw <;> rw [List.all_eq_true] at hsw
    · refine sv_le_one_of_switch k P (fun i hi => ?_) (fun i hi => ?_) <;> rw [hPc] <;>
        by_cases hs : i < T.size
      · have := hsw i (List.mem_range.mpr hs)
        simp [hi] at this
        exact_mod_cast this
      · rw [hz i (by omega)]
      · have := hsw i (List.mem_range.mpr hs)
        simp [show ¬ i < k by omega] at this
        exact_mod_cast this
      · rw [hz i (by omega)]
    · have := sv_le_one_of_switch k (-P) (fun i hi => ?_) (fun i hi => ?_)
      · rwa [signVariations_neg] at this
      all_goals rw [coeff_neg, hPc]; by_cases hs : i < T.size
      · have := hsw i (List.mem_range.mpr hs)
        simp [hi] at this
        have : (T.coeff i : ℝ) ≤ 0 := by exact_mod_cast this
        linarith
      · rw [hz i (by omega)]; simp
      · have := hsw i (List.mem_range.mpr hs)
        simp [show ¬ i < k by omega] at this
        have : (0 : ℝ) ≤ T.coeff i := by exact_mod_cast this
        linarith
      · rw [hz i (by omega)]; simp
  have hlh : (lo : ℝ) < hi := by exact_mod_cast hlohi
  have root : ∀ z ∈ Ioo (lo : ℝ) hi, rv m z = 0 →
      0 < (z - lo) / (hi - z) ∧ P.eval ((z - lo) / (hi - z)) = 0 := fun z hz hmz => by
    refine ⟨div_pos (by linarith [hz.1]) (by linarith [hz.2]), ?_⟩
    rw [hPe, rv_mobius m (by linarith [hz.2]), hmz, mul_zero]
  obtain ⟨hx0, hxr⟩ := root x hx hmx
  obtain ⟨hy0, hyr⟩ := root y hy hmy
  refine two_pos_roots hP0 hsv hx0 hy0 (fun heq => hxy ?_) hxr hyr
  have h1 : (hi : ℝ) - x ≠ 0 := by linarith [hx.2]
  have h2 : (hi : ℝ) - y ≠ 0 := by linarith [hy.2]
  rw [div_eq_div_iff h1 h2] at heq
  have h3 : (x - y) * ((hi : ℝ) - lo) = 0 := by linear_combination heq
  rcases mul_eq_zero.mp h3 with h3 | h3
  · linarith
  · linarith

/-! ## Univariate values -/

-- `GPBinding.Real.signSq_real` and `signSq_map` (AdmissionSound, which imports this file).
theorem signSq_real (y : ℝ) : signSq y = ((SignType.sign y : SignType) : ℤ) := by
  unfold signSq
  rcases lt_trichotomy y 0 with h | rfl | h
  · have hn : ¬ IsSquare y := fun hsq => absurd hsq.nonneg (not_le.mpr h)
    simp [h.ne, hn, sign_neg h]
  · simp
  · have hsq : IsSquare y := ⟨√y, (Real.mul_self_sqrt h.le).symm⟩
    simp [h.ne', hsq, sign_pos h]

theorem signSq_map {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (y : K) : signSq (e y) = signSq y := by
  have h0 : e y = 0 ↔ y = 0 := map_eq_zero_iff e e.injective
  have hs : IsSquare (e y) ↔ IsSquare y :=
    ⟨fun h => by simpa using h.map e.symm, fun h => h.map e⟩
  unfold signSq
  by_cases hy : y = 0
  · simp [hy]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (mt h0.mp hy)), ite_eq_right_of_eq_false _ _ (eq_false hy)]
    by_cases hq : IsSquare y
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (hs.mpr hq)), ite_eq_left_of_eq_true _ _ (eq_true hq)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (mt hs.mp hq)), ite_eq_right_of_eq_false _ _ (eq_false hq)]

theorem value_hom {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] (f : K →+* L) {n : ℕ}
    (p : Sparse) (x : Fin n → K) : Admission.value n p (fun i => f (x i)) = f (Admission.value n p x) := by
  rw [GPBinding.Real.value_eq, GPBinding.Real.value_eq]
  simp only [GPBinding.Real.evalQ, MvPolynomial.coe_eval₂Hom]
  rw [MvPolynomial.eval₂_comp_left f (Rat.castHom K) x,
    RingHom.ext_rat (f.comp (Rat.castHom K)) (Rat.castHom L)]
  rfl

theorem value_one {n : ℕ} (hn : n = 1) {p : Sparse} (hp : sparseArity 1 p = true) (z : Fin n → ℝ) :
    Admission.value n p z = rv (toD p) (z ⟨0, by omega⟩) := by
  subst hn
  rw [← GPBinding.Real.valueE_eq_value hp, toD, rv_fieldEval (s := 0) rv_zero]
  congr 1
  funext i
  rw [Subsingleton.elim i 0]
  simp [rv_X]

theorem rv_linRoot {p : RAlg.D} {c : ℚ} (h : linRoot p = some c) (x : ℝ) : rv p x = x - c := by
  unfold linRoot at h
  split_ifs at h with h2
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  obtain ⟨hs, h1⟩ := h2
  cases h
  rw [rv_eq_sum, hs]
  simp [Finset.sum_range_succ, h1]
  ring

theorem pos_of_sign {v : ℝ} (h : ((SignType.sign v : SignType) : ℤ) = 1) : 0 < v := by
  rcases lt_trichotomy v 0 with hv | rfl | hv
  · rw [sign_neg hv] at h; simp at h
  · simp at h
  · exact hv

theorem neg_of_sign {v : ℝ} (h : ((SignType.sign v : SignType) : ℤ) = -1) : v < 0 := by
  rcases lt_trichotomy v 0 with hv | rfl | hv
  · exact hv
  · simp at h
  · rw [sign_pos hv] at h; simp at h

/-- An interval atom `x - c` with sign `σ`, at a point of a one-variable system. -/
theorem atom_spec {r : RealSys} {c : ℚ} {σ : ℤ} (h : hasAtom r c σ = true) :
    ∃ a ∈ r.signs, a.2 = σ ∧ sparseArity 1 a.1 = true ∧ linRoot (toD a.1) = some c := by
  unfold hasAtom at h
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨a, ha, ⟨h1, h2⟩, h3⟩ := h
  exact ⟨a, ha, h1, h2, h3⟩

/-! ## Covers over ℝ -/

theorem rootCoverCheck_real {r : RealSys} {bs : List RBranch} {c : RootCoverCert}
    (h : rootCoverCheck r bs c = true) (z : Fin r.vars.length → ℝ) (hz : RealLocus r z) :
    ∃ b ∈ bs, RealLocus (r.branch b) z := by
  unfold rootCoverCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨hn, hlo⟩, hhi⟩, m, hm, hma, hm1⟩, b, hb, hpc⟩ := h
  obtain ⟨y, hye, hyg, hys⟩ : ∃ y : Fin r.vars.length → ℝ,
      (∀ e ∈ r.eqs ++ b.eqs, Admission.value r.vars.length e y = 0) ∧
      (∀ g ∈ r.guards ++ b.guards, Admission.value r.vars.length g y ≠ 0) ∧
      (∀ p ∈ r.signs ++ b.signs,
        ((SignType.sign (Admission.value r.vars.length p.1 y) : SignType) : ℤ) = p.2) :=
    pointCheck_sound_value hpc
  obtain ⟨al, hal, hal1, hal2, hal3⟩ := atom_spec hlo
  obtain ⟨ah, hah, hah1, hah2, hah3⟩ := atom_spec hhi
  have i0 : 0 < r.vars.length := by omega
  -- The parent point and the replayed point are roots of `m` in `(lo, hi)`.
  have zin : z ⟨0, i0⟩ ∈ Ioo (c.lo : ℝ) c.hi := by
    have h1 := hz.2.2 al hal
    have h2 := hz.2.2 ah hah
    rw [signSq_real, hal1] at h1
    rw [signSq_real, hah1] at h2
    have p1 := pos_of_sign h1
    have p2 := neg_of_sign h2
    rw [value_one hn hal2, rv_linRoot hal3] at p1
    rw [value_one hn hah2, rv_linRoot hah3] at p2
    exact ⟨by linarith, by linarith⟩
  have yin : y ⟨0, i0⟩ ∈ Ioo (c.lo : ℝ) c.hi := by
    have h1 := hys al (List.mem_append_left _ hal)
    have h2 := hys ah (List.mem_append_left _ hah)
    rw [hal1] at h1
    rw [hah1] at h2
    have p1 := pos_of_sign h1
    have p2 := neg_of_sign h2
    rw [value_one hn hal2, rv_linRoot hal3] at p1
    rw [value_one hn hah2, rv_linRoot hah3] at p2
    exact ⟨by linarith, by linarith⟩
  have zm : rv (toD m) (z ⟨0, i0⟩) = 0 := by rw [← value_one hn hma]; exact hz.1 m hm
  have ym : rv (toD m) (y ⟨0, i0⟩) = 0 := by
    rw [← value_one hn hma]; exact hye m (List.mem_append_left _ hm)
  have e0 := atMostOneRoot_sound hm1 zin yin zm ym
  have hzy : z = y := by
    funext i
    rw [show i = ⟨0, i0⟩ from Fin.ext (by have := i.isLt; omega)]
    exact e0
  subst hzy
  refine ⟨b, hb, fun e he => hye e (List.mem_append_right _ he),
    fun g hg => hyg g (List.mem_append_right _ hg), fun p hp => ?_⟩
  rw [signSq_real]
  exact hys p (List.mem_append_right _ hp)

/-! ## Transport along ring isomorphisms -/

theorem realLocus_equiv {K : Type*} [Field K] [CharZero K] (e : K ≃+* ℝ) (r : RealSys)
    (x : Fin r.vars.length → K) : RealLocus r x ↔ RealLocus r (fun i => e (x i)) := by
  have hv : ∀ p : Sparse, Admission.value _ p (fun i => e (x i)) = e (Admission.value _ p x) :=
    fun p => value_hom e.toRingHom p x
  have hz : ∀ v : K, e v = 0 ↔ v = 0 := fun v => map_eq_zero_iff e e.injective
  unfold RealLocus
  simp only [hv, hz, ne_eq, signSq_map]

theorem rootCoverCheck_holds {r : RealSys} {bs : List RBranch} {c : RootCoverCert}
    (h : rootCoverCheck r bs c = true) {K : Type*} [Field K] (e : K ≃+* ℝ) : RealCoverHolds K r bs := by
  have := isSemireal_of_equiv_real e
  intro x hx
  obtain ⟨b, hb, hl⟩ := rootCoverCheck_real h _ ((realLocus_equiv e r x).mp hx)
  exact ⟨b, hb, (realLocus_equiv e (r.branch b) x).mpr hl⟩

/-! ## Rational roots -/

/-- **The rational root test is sound** (any degree): no rational number is a root. -/
theorem noRationalRoot_sound {M : RAlg.D} (h : noRationalRoot M = true) (x : ℚ) : M.eval x ≠ 0 := by
  simp only [noRationalRoot, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hden, h0⟩, -⟩, -⟩, hroots⟩ := h
  intro hx
  have hpos : 0 < M.size := by
    by_contra hs; exact h0 (Hex.DensePoly.coeff_eq_zero_of_size_le M (by omega))
  have hden' : ∀ i, (M.coeff i).den = 1 := fun i => by
    by_cases hi : i < M.size
    · exact hden i hi
    · rw [Hex.DensePoly.coeff_eq_zero_of_size_le M (by omega)]; rfl
  have hdeg : (toPolynomial M).natDegree = M.size - 1 := by
    rw [natDegree_toPolynomial, Hex.DensePoly.natDegree_eq_size_sub_one]
  have hlc : M.leadingCoeff ≠ 0 := by
    rw [Hex.DensePoly.leadingCoeff_eq_coeff_last M hpos]
    exact Hex.DensePoly.coeff_last_ne_zero_of_pos_size M hpos
  have hmap := NumberField.intPoly_map hden'
  have haeval : aeval x (NumberField.intPoly M) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq, hmap, eval_toPolynomial]; exact hx
  have hdegZ : (NumberField.intPoly M).natDegree = M.size - 1 := by
    rw [← natDegree_map_eq_of_injective (Int.castRingHom ℚ).injective_int, hmap, hdeg]
  have hnum := num_dvd_of_is_root (A := ℤ) haeval
  have hdenom := den_dvd_of_is_root (A := ℤ) haeval
  rw [NumberField.intPoly_coeff] at hnum
  rw [leadingCoeff, hdegZ, NumberField.intPoly_coeff, ← Hex.DensePoly.leadingCoeff_eq_coeff_last M hpos]
    at hdenom
  have hc0 : (M.coeff 0).num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (mt Rat.num_eq_zero.mp h0)
  have hcn : M.leadingCoeff.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (mt Rat.num_eq_zero.mp hlc)
  have ha := NumberField.mem_divisorsN hc0 (Int.natAbs_dvd_natAbs.mpr hnum)
  have hb := NumberField.mem_divisorsN hcn (Int.natAbs_dvd_natAbs.mpr hdenom)
  obtain ⟨hp, hn⟩ := hroots _ ha _ hb
  have hx' : x = ((IsFractionRing.num ℤ x : ℤ) : ℚ) / ((IsFractionRing.den ℤ x : ℤ) : ℚ) :=
    (IsFractionRing.mk'_num_den' ℤ x).symm
  rcases NumberField.int_div_cases (IsFractionRing.num ℤ x) (IsFractionRing.den ℤ x) with hc | hc <;>
    rw [hc] at hx' <;> rw [hx'] at hx
  · exact hp hx
  · exact hn hx

/-- An accepted rational-root certificate: the order-free EMPTY claim holds in every field
isomorphic to ℚ. -/
theorem ratRootCheck_holds {s : Stmt} (h : ratRootCheck s = true) {K : Type*} [Field K] (e : K ≃+* ℚ) :
    Admission.Holds K s := by
  unfold ratRootCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h
  obtain ⟨⟨hk, hn⟩, m, hm, har, hno⟩ := h
  have := isSemireal_of_equiv_rat e
  unfold Admission.Holds
  rw [hk]
  intro x hx
  have h0 : Admission.value _ m x = 0 := hx.1 m hm
  have hq : Admission.value _ m (fun i => ((e (x i) : ℚ) : ℝ)) = 0 :=
    calc _ = (Rat.castHom ℝ) (Admission.value _ m (fun i => e (x i))) :=
          value_hom (Rat.castHom ℝ) m (fun i => e (x i))
      _ = (Rat.castHom ℝ) (e.toRingHom (Admission.value _ m x)) :=
          congrArg (Rat.castHom ℝ) (value_hom e.toRingHom m x)
      _ = 0 := by simp [h0]
  rw [value_one hn har, rv_ratCast] at hq
  exact noRationalRoot_sound hno _ (by exact_mod_cast hq)

end GPBinding.Real.RootCover
