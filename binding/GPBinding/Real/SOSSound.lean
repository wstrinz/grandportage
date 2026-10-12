import GPBinding.Admission.Semantics
import GPProfile.Real.SOS
import Mathlib.Algebra.Ring.Semireal.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
Soundness of the SOS/Positivstellensatz EMPTY checker (`GPProfile.Real.sosCheck`): an accepted
certificate makes its system empty in every semireal field (3B context note, revision 2026-10-09).

At a point `x` of the locus, the replayed identity
`(∏ guards)^(2k) + Σ wᵢ·pᵢ² + Σ qⱼ·eⱼ = 0` evaluates to `g^(2k) + σ = 0` with `g ≠ 0` and `σ` a
sum of squares (a nonnegative rational `a/b` is `ab·(1/b)²`, and a natural number is a sum of
ones). Then `−1 = σ·(g^k)⁻²` is a sum of squares, which `IsSemireal` forbids. Nothing about LDLᵀ
is used: the checker replays the explicit squares it produced. With selected guards (`guardSel`),
`g` is the product of the selected ones; each is a guard of the system (`selectGuards_sub`), so
`g ≠ 0` all the same.
-/

noncomputable section

namespace GPBinding.Real
open GPProfile GPProfile.Real GPBinding.Admission MvPolynomial HexMvPolyMathlib

/-! ## Unpacking an accepted certificate -/

/-- Selected guards are guards: every entry of a selection is a member of the list. -/
theorem selectGuards_sub {gs sg : List Sparse} :
    ∀ {o : Option (List Nat)}, selectGuards gs o = some sg → ∀ g ∈ sg, g ∈ gs
  | none, h => by
    simp only [selectGuards, Option.some.injEq] at h
    subst h
    exact fun _ hg => hg
  | some idx, h => by
    simp only [selectGuards] at h
    have hf := mapM_forall₂ h
    clear h
    induction hf with
    | nil => simp
    | cons hab _ ih =>
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact List.mem_of_getElem? hab
      · exact ih g hg

/-- The guard term means `(∏ guards)^(2k)`; for `k = 0` the checker skips the product. -/
theorem toMv_guardTerm {n : ℕ} (G : List (GPProfile.P n Rat)) (k : ℕ) :
    toMvPolynomial (guardTerm G k) = toMvPolynomial (G.prod ^ (2 * k)) := by
  unfold guardTerm
  split_ifs with h
  · subst h
    simp [toMvPolynomial_pow]
  · rfl

theorem sosResidual_spec {s : Stmt} {c : PCert} {R : GPProfile.P s.vars.length Rat}
    (h : sosResidual s c = .ok R) :
    s.kind = .empty ∧ ∃ sq eqs sg guards qs, (∀ t ∈ sq, (0 : Rat) ≤ t.1) ∧
      s.eqs.mapM (toHexQ s.vars.length) = some eqs ∧
      selectGuards s.guards c.guardSel = some sg ∧
      sg.mapM (toHexQ s.vars.length) = some guards ∧
      c.cofactors.mapM (toHexQ s.vars.length) = some qs ∧
      R = assemble guards c.guardPow sq qs eqs := by
  unfold sosResidual at h
  dsimp only at h
  split_ifs at h with h1
  simp only [bne_iff_ne, ne_eq, not_not] at h1
  refine ⟨h1, ?_⟩
  split at h
  · cases h
  · rename_i sg hsg
    split_ifs at h
    split at h
    · cases h
    · rename_i sqs _
      split_ifs at h with h5
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, decide_eq_true_eq] at h5
      split at h
      · rename_i eqs guards qs hE hG hQ
        cases h
        exact ⟨sqs.flatten, eqs, sg, guards, qs, h5, hE, hsg, hG, hQ, rfl⟩
      · cases h

/-! ## Evaluation at a point of a characteristic-zero field -/

variable {K : Type*} [Field K]

/-- Evaluation of rational polynomials at `x`, as a ring hom (characteristic zero). -/
abbrev evalQ [CharZero K] {n : ℕ} (x : Fin n → K) : MvPolynomial (Fin n) Rat →+* K :=
  eval₂Hom (Rat.castHom K) x

theorem value_eq [CharZero K] {n : ℕ} (p : Sparse) (x : Fin n → K) :
    value n p x = evalQ x (meaning n p) := by
  have : toK (K := K) (meaning n p) = map (Rat.castHom K) (meaning n p) := by
    ext d
    simp [coeff_toK, coeff_map]
  rw [value, this, eval_map]
  rfl

theorem evalQ_zipWith_sum_zero [CharZero K] {n : ℕ} (x : Fin n → K) :
    ∀ (A B : List (MvPolynomial (Fin n) Rat)), (∀ b ∈ B, evalQ x b = 0) →
      evalQ x (List.zipWith (· * ·) A B).sum = 0
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: A, b :: B, hB => by
    simp only [List.zipWith_cons_cons, List.sum_cons, map_add, map_mul]
    rw [hB b List.mem_cons_self, mul_zero, zero_add,
      evalQ_zipWith_sum_zero x A B fun c h => hB c (List.mem_cons_of_mem _ h)]

theorem evalQ_prod_ne_zero [CharZero K] {n : ℕ} (x : Fin n → K) :
    ∀ (l : List (MvPolynomial (Fin n) Rat)), (∀ g ∈ l, evalQ x g ≠ 0) → evalQ x l.prod ≠ 0
  | [], _ => by simp
  | g :: l, h => by
    rw [List.prod_cons, map_mul]
    exact mul_ne_zero (h g List.mem_cons_self)
      (evalQ_prod_ne_zero x l fun c hc => h c (List.mem_cons_of_mem _ hc))

/-! ## Sums of squares -/

/-- A nonnegative rational is a sum of squares in a field of characteristic zero:
`a/b = (a·b)·(b⁻¹)²`, and a natural number is a sum of ones. -/
theorem isSumSq_ratCast [CharZero K] {w : Rat} (hw : 0 ≤ w) : IsSumSq (w : K) := by
  have hnum : ((w.num.toNat : ℕ) : K) = (w.num : K) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.mpr hw)]
  have hd : (w.den : K) ≠ 0 := Nat.cast_ne_zero.mpr w.den_nz
  have : (w : K) = ((w.num.toNat * w.den : ℕ) : K) * ((w.den : K)⁻¹ * (w.den : K)⁻¹) := by
    rw [Rat.cast_def, Nat.cast_mul, hnum]
    field_simp
  rw [this]
  exact (IsSumSq.natCast _).mul (IsSumSq.mul_self _)

theorem isSumSq_list_sum : ∀ (l : List K), (∀ a ∈ l, IsSumSq a) → IsSumSq l.sum
  | [], _ => by simp [IsSumSq.zero]
  | a :: l, h => by
    rw [List.sum_cons]
    exact (h a List.mem_cons_self).add (isSumSq_list_sum l fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- The SOS part of an accepted certificate evaluates to a sum of squares. -/
theorem isSumSq_sos [CharZero K] {n : ℕ} (x : Fin n → K) (sq : List (Rat × GPProfile.P n Rat))
    (hw : ∀ t ∈ sq, (0 : Rat) ≤ t.1) :
    IsSumSq (evalQ x ((sq.map fun t => Hex.MvPoly.C t.1 * (t.2 * t.2)).map toMvPolynomial).sum) := by
  rw [List.map_map, map_list_sum, List.map_map]
  apply isSumSq_list_sum
  intro a ha
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
  have e : evalQ x (toMvPolynomial (Hex.MvPoly.C t.1 * (t.2 * t.2) : GPProfile.P n Rat)) =
      (t.1 : K) * (evalQ x (toMvPolynomial t.2) * evalQ x (toMvPolynomial t.2)) := by
    rw [toMvPolynomial_mul, toMvPolynomial_mul, toMvPolynomial_C, map_mul, map_mul]
    simp [evalQ]
  simp only [Function.comp_apply]
  rw [e]
  exact (isSumSq_ratCast (hw t ht)).mul (IsSumSq.mul_self _)

/-! ## Soundness -/

/-- An accepted SOS certificate has no point in any semireal field. -/
theorem sosCheck_sound {s : Stmt} {c : PCert} (h : sosCheck s c = true)
    (K : Type*) [Field K] [IsSemireal K] : ¬ ∃ x : Fin s.vars.length → K, Locus (K := K) s x := by
  rintro ⟨x, he, hg⟩
  unfold sosCheck at h
  split at h
  · rename_i R hR
    have hR0 : R = 0 := beq_iff_eq.mp h
    obtain ⟨-, sq, eqs, sg, guards, qs, hw, hE, hsg, hG, hQ, rfl⟩ := sosResidual_spec hR
    have key := congrArg (fun P => evalQ x (toMvPolynomial P)) hR0
    simp only [assemble, toMvPolynomial_add, toMv_guardTerm, toMvPolynomial_pow, toMv_list_prod,
      toMv_list_sum, toMv_zipWith_mul, map_meaning hE, map_meaning hG, map_meaning hQ, toMvPolynomial_zero,
      map_zero, map_add, map_pow] at key
    have hz := evalQ_zipWith_sum_zero x (c.cofactors.map (meaning _)) (s.eqs.map (meaning _))
      (fun b hb => by
        obtain ⟨e, he', rfl⟩ := List.mem_map.mp hb
        rw [← value_eq]; exact he e he')
    have hgz := evalQ_prod_ne_zero x (sg.map (meaning _)) (fun b hb => by
        obtain ⟨g, hg', rfl⟩ := List.mem_map.mp hb
        rw [← value_eq]; exact hg g (selectGuards_sub hsg g hg'))
    have hσ := isSumSq_sos x sq hw
    rw [hz, add_zero] at key
    generalize evalQ x (sg.map (meaning s.vars.length)).prod = g at key hgz
    generalize evalQ x ((sq.map fun t => Hex.MvPoly.C t.1 * (t.2 * t.2)).map toMvPolynomial).sum = σ
      at key hσ
    have hgk : g ^ c.guardPow ≠ 0 := pow_ne_zero _ hgz
    have hneg : (-1 : K) = σ * ((g ^ c.guardPow)⁻¹ * (g ^ c.guardPow)⁻¹) := by
      have hs : σ = -(g ^ c.guardPow * g ^ c.guardPow) := by linear_combination key
      rw [hs]
      field_simp
    exact IsSemireal.not_isSumSq_neg_one K (hneg ▸ hσ.mul (IsSumSq.mul_self _))
  · exact absurd h (by simp)

/-- The same, as the 3a meaning of the EMPTY statement it checks. -/
theorem sosCheck_holds {s : Stmt} {c : PCert} (h : sosCheck s c = true)
    (K : Type*) [Field K] [IsSemireal K] : Holds K s := by
  have hk : s.kind = .empty := by
    unfold sosCheck at h
    split at h
    · exact (sosResidual_spec (by assumption)).1
    · exact absurd h (by simp)
  unfold Holds
  rw [hk]
  exact fun x hx => sosCheck_sound h K ⟨x, hx⟩

end GPBinding.Real

end
