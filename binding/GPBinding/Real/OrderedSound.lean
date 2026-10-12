import GPBinding.Real.RootCoverSound
import GPProfile.Real.Ordered

/-!
Soundness of the ordered Positivstellensatz checker (`GPProfile.Real.orderedCheck`, C7): an
accepted certificate makes its real system empty in every field isomorphic to ℝ.

At a real point `x` of the system, the replayed identity
`∏ qₖ^aₖ · (∏ g)^(2k) + Σ s·∏ q + Σ cᵢ·eᵢ = 0` evaluates to `M + S + I = 0` with
- `M > 0`: each `qₖ(x) = σₖ·pₖ(x) > 0` because `sign pₖ(x) = σₖ ≠ 0` (signs read through squares,
  `RootCover.signSq_real`), and the guards' product is nonzero, raised to an even power;
- `S ≥ 0`: each cone term is a nonnegatively weighted sum of squares times a product of numbers
  that are positive, or `0` for an out-of-range index;
- `I = 0`: every equation, and every zero sign atom, vanishes at `x`.
With selected guards (`guardSel`) the guard product runs over the selected guards, each a guard
of the system (`selectGuards_sub`), so it is nonzero all the same. A field isomorphic to ℝ carries
the point to ℝ (`RootCover.realLocus_equiv`). The Gram hints are
not used: the checker replays the explicit squares it produced.
-/

noncomputable section

namespace GPBinding.Real.Ordered
open GPProfile GPProfile.Real GPBinding.Admission MvPolynomial HexMvPolyMathlib

/-! ## Unpacking an accepted certificate -/

theorem orderedResidual_spec {r : RealSys} {c : OCert} {R : GPProfile.P r.vars.length Rat}
    (h : orderedResidual r c = .ok R) :
    ∃ T E sg G Q C, (∀ t ∈ T, ∀ u ∈ (t : List (Rat × GPProfile.P r.vars.length Rat) × List Nat).1,
        (0 : Rat) ≤ u.1) ∧
      (r.eqs ++ zeroAtoms r).mapM (toHexQ r.vars.length) = some E ∧
      selectGuards r.guards c.guardSel = some sg ∧
      sg.mapM (toHexQ r.vars.length) = some G ∧
      (strictAtoms r).mapM (posHex r.vars.length) = some Q ∧
      c.cofactors.mapM (toHexQ r.vars.length) = some C ∧
      R = oAssemble E G Q C c.posPow c.guardPow T := by
  unfold orderedResidual at h
  dsimp only at h
  split_ifs at h
  split at h
  · cases h
  · rename_i sg hsg
    split_ifs at h
    split at h
    · cases h
    · rename_i T _
      split_ifs at h with hw
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, decide_eq_true_eq] at hw
      split at h
      · rename_i E G Q C hE hG hQ hC
        cases h
        exact ⟨T, E, sg, G, Q, C, hw, hE, hsg, hG, hQ, hC, rfl⟩
      · cases h

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ b ∈ l', ∃ a ∈ l, R a b
  | [], [], .nil, b, hb => by simp at hb
  | a :: _, _ :: _, .cons hab rest, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hab⟩
    · obtain ⟨a', ha', h'⟩ := forall₂_mem_right rest b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem mapM_mem {α β : Type} {f : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM f = some l') : ∀ b ∈ l', ∃ a ∈ l, f a = some b :=
  forall₂_mem_right (mapM_forall₂ h)

/-! ## Evaluation at a real point -/

/-- A Hex polynomial's value at a real point. -/
def ev {n : ℕ} (x : Fin n → ℝ) (P : GPProfile.P n Rat) : ℝ := evalQ x (toMvPolynomial P)

section
variable {n : ℕ} (x : Fin n → ℝ)

theorem ev_add (P Q : GPProfile.P n Rat) : ev x (P + Q) = ev x P + ev x Q := by
  simp [ev, toMvPolynomial_add]

theorem ev_mul (P Q : GPProfile.P n Rat) : ev x (P * Q) = ev x P * ev x Q := by
  simp [ev, toMvPolynomial_mul]

theorem ev_pow (P : GPProfile.P n Rat) (k : ℕ) : ev x (P ^ k) = ev x P ^ k := by
  simp [ev, toMvPolynomial_pow]

theorem ev_zero : ev x (0 : GPProfile.P n Rat) = 0 := by simp [ev]

theorem ev_C (c : Rat) : ev x (Hex.MvPoly.C c : GPProfile.P n Rat) = (c : ℝ) := by
  simp [ev, evalQ, toMvPolynomial_C]

theorem ev_sum (l : List (GPProfile.P n Rat)) : ev x l.sum = (l.map (ev x)).sum := by
  rw [ev, toMv_list_sum, map_list_sum, List.map_map]; rfl

theorem ev_prod (l : List (GPProfile.P n Rat)) : ev x l.prod = (l.map (ev x)).prod := by
  rw [ev, toMv_list_prod, map_list_prod, List.map_map]; rfl

theorem ev_meaning {p : Sparse} {P : GPProfile.P n Rat} (h : toHexQ n p = some P) :
    ev x P = value n p x := by
  rw [value_eq, meaning_of h]; rfl

theorem ev_zipWith_sum_zero :
    ∀ (A B : List (GPProfile.P n Rat)), (∀ b ∈ B, ev x b = 0) →
      ev x (List.zipWith (· * ·) A B).sum = 0
  | [], _, _ => by simp [ev_zero]
  | _ :: _, [], _ => by simp [ev_zero]
  | a :: A, b :: B, hB => by
    rw [List.zipWith_cons_cons, List.sum_cons, ev_add, ev_mul, hB b List.mem_cons_self, mul_zero,
      zero_add, ev_zipWith_sum_zero A B fun c h => hB c (List.mem_cons_of_mem _ h)]

theorem ev_sqSum_nonneg (sq : List (Rat × GPProfile.P n Rat)) (hw : ∀ u ∈ sq, (0 : Rat) ≤ u.1) :
    0 ≤ ev x (sqSum sq) := by
  rw [sqSum, ev_sum, List.map_map]
  apply List.sum_nonneg
  intro a ha
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
  simp only [Function.comp_apply, ev_mul, ev_C]
  exact mul_nonneg (Rat.cast_nonneg.mpr (hw u hu)) (mul_self_nonneg _)

end

/-! ## Signs over ℝ -/

theorem signSq_zero {y : ℝ} (h : signSq y = 0) : y = 0 := by
  unfold signSq at h
  split_ifs at h with h0 <;> simp_all

theorem signSq_strict {y : ℝ} {σ : ℤ} (hσ : σ ≠ 0) (h : signSq y = σ) : 0 < (σ : ℝ) * y := by
  rw [RootCover.signSq_real] at h
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · rw [sign_neg hy] at h
    subst h
    simp only [SignType.coe_neg_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
    linarith
  · simp at h
    exact absurd h.symm hσ
  · rw [sign_pos hy] at h
    subst h
    simpa using hy

/-! ## Soundness -/

/-- An accepted ordered certificate leaves its system without real points. -/
theorem orderedCheck_real {r : RealSys} {c : OCert} (h : orderedCheck r c = true)
    (x : Fin r.vars.length → ℝ) (hx : RealLocus r x) : False := by
  obtain ⟨he, hg, hs⟩ := hx
  unfold orderedCheck at h
  split at h
  case h_2 => exact absurd h (by simp)
  rename_i R hR
  have hR0 : R = 0 := beq_iff_eq.mp h
  obtain ⟨T, E, sg, G, Q, C, hw, hE, hsg, hG, hQ, hC, rfl⟩ := orderedResidual_spec hR
  have key := congrArg (ev x) hR0
  rw [oAssemble, ev_add, ev_add, ev_mul, ev_zero] at key
  -- The strict positives.
  have hpos : ∀ q ∈ Q, 0 < ev x q := by
    intro q hq
    obtain ⟨a, ha, haq⟩ := mapM_mem hQ q hq
    obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.mp haq
    obtain ⟨ha', hσ⟩ := List.mem_filter.mp ha
    rw [ev_mul, ev_C, ev_meaning x hP]
    have := signSq_strict (by simpa using hσ) (hs a ha')
    simpa using this
  -- The monoid term is positive.
  have hM : 0 < ev x ((Q.zip c.posPow).map fun t => t.1 ^ t.2).prod := by
    rw [ev_prod, List.map_map]
    apply List.prod_pos
    intro a ha
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
    simp only [Function.comp_apply, ev_pow]
    exact pow_pos (hpos _ (List.of_mem_zip ht).1) _
  have hG' : ev x G.prod ≠ 0 := by
    rw [ev_prod]
    intro h0
    rw [List.prod_eq_zero_iff] at h0
    obtain ⟨g, hg', hg0⟩ := List.mem_map.mp h0
    obtain ⟨s, hs', hsg'⟩ := mapM_mem hG g hg'
    rw [ev_meaning x hsg'] at hg0
    exact hg s (selectGuards_sub hsg s hs') hg0
  have hGk : 0 < ev x (guardTerm G c.guardPow) := by
    rw [ev, toMv_guardTerm, ← ev, ev_pow]
    exact (even_two_mul _).pow_pos hG'
  -- The cone is nonnegative.
  have hS : 0 ≤ ev x (T.map (coneHex Q)).sum := by
    rw [ev_sum, List.map_map]
    apply List.sum_nonneg
    intro a ha
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
    simp only [Function.comp_apply, coneHex, ev_mul]
    refine mul_nonneg (ev_sqSum_nonneg x t.1 (hw t ht)) ?_
    rw [ev_prod, List.map_map]
    apply List.prod_nonneg
    intro b hb
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
    simp only [Function.comp_apply, List.getD_eq_getElem?_getD]
    cases hi : Q[i]? with
    | none => simp [ev_zero]
    | some q => exact (hpos q (List.mem_of_getElem? hi)).le
  -- The ideal term vanishes.
  have hI : ev x (List.zipWith (· * ·) C E).sum = 0 := by
    apply ev_zipWith_sum_zero
    intro e heE
    obtain ⟨s, hs', hse⟩ := mapM_mem hE e heE
    rw [ev_meaning x hse]
    rcases List.mem_append.mp hs' with hs' | hs'
    · exact he s hs'
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs'
      obtain ⟨ha', h0⟩ := List.mem_filter.mp ha
      have := hs a ha'
      rw [beq_iff_eq.mp h0] at this
      exact signSq_zero this
  rw [hI, add_zero] at key
  linarith [mul_pos hM hGk]

/-- **C7 soundness.** An accepted ordered certificate makes its system empty in every field
isomorphic to ℝ. -/
theorem orderedCheck_holds {r : RealSys} {c : OCert} (h : orderedCheck r c = true)
    {K : Type*} [Field K] (e : K ≃+* ℝ) : RealHolds K r .empty := by
  have := isSemireal_of_equiv_real e
  intro x hx
  exact orderedCheck_real h _ ((RootCover.realLocus_equiv e r x).mp hx)

theorem orderedCheck_sound {r : RealSys} {c : OCert} (h : orderedCheck r c = true) :
    ∀ (K : Type*) [Field K], Nonempty (K ≃+* ℝ) → RealHolds K r .empty :=
  fun _ _ hK => orderedCheck_holds h (Classical.choice hK)

end GPBinding.Real.Ordered

end
