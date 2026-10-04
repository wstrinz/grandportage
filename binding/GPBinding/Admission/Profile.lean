import GPBinding.Admission.Sound
import GPBinding.ContextSpike
import GP50.NarrowingAdmissionProofs
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.CharP.Algebra

/-!
The 3a algebraic profile's semantic half (post-G2 §3.9): contexts are fields (`FieldCtx`, the
§2.5c choice), membership is `ringChar K ∈ ⟦scope⟧`, and `Holds` is statement truth in `K`.
Receipt admission is sound, so the Kernel's generic fold theorem gives held claims their
meaning in every field their scope denotes.
-/

namespace GPBinding.Admission
open GPProfile GP50 GPBinding.Spike

/-- Geometric emptiness puts a power of the guard product in the ideal (Nullstellensatz). -/
theorem guard_pow_mem_of_empty {L : Type} [Field L] [IsAlgClosed L] {v : List String}
    {e g : List Sparse} {kd : Kind} (hempty : ∀ x, ¬ Locus (K := L) ⟨v, e, g, kd⟩ x) :
    ∃ k : ℕ, (g.map fun q => toK (K := L) (meaning v.length q)).prod ^ k ∈
      Ideal.span {f | f ∈ e.map fun q => toK (K := L) (meaning v.length q)} := by
  have hG : (g.map fun q => toK (K := L) (meaning v.length q)).prod ∈
      MvPolynomial.vanishingIdeal L (MvPolynomial.zeroLocus L
        (Ideal.span {f | f ∈ e.map fun q => toK (K := L) (meaning v.length q)})) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    rw [MvPolynomial.mem_zeroLocus_iff] at hx
    by_contra hne
    refine hempty x ⟨fun q hq => hx _ (Ideal.subset_span (List.mem_map.mpr ⟨q, hq, rfl⟩)),
      fun q hq h0 => hne ?_⟩
    rw [MvPolynomial.aeval_eq_eval, map_list_prod]
    exact List.prod_eq_zero (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨q, hq, rfl⟩, h0⟩)
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hG
  exact hG

/-- `kindContra` is sound in each characteristic: the two kinds cannot both hold in every field
of one characteristic. -/
theorem kindContra_sound {v : List String} {e g : List Sparse} {k₁ k₂ : Kind}
    (h : kindContra k₁ k₂ = true) (K : FieldCtx)
    (h₁ : ∀ L : FieldCtx, ringChar L.carrier = ringChar K.carrier → Holds L.carrier ⟨v, e, g, k₁⟩)
    (h₂ : ∀ L : FieldCtx, ringChar L.carrier = ringChar K.carrier → Holds L.carrier ⟨v, e, g, k₂⟩) :
    False := by
  cases k₁ <;> cases k₂ <;> simp only [kindContra, Bool.false_eq_true, beq_iff_eq] at h
  · obtain ⟨x, hx⟩ := h₂ K rfl
    exact h₁ K rfl x hx
  · let L : FieldCtx := ⟨AlgebraicClosure K.carrier⟩
    have hc : ringChar L.carrier = ringChar K.carrier :=
      (Algebra.ringChar_eq K.carrier (AlgebraicClosure K.carrier)).symm
    obtain ⟨k, hk⟩ := guard_pow_mem_of_empty (L := AlgebraicClosure K.carrier) (h₁ L hc)
    exact h₂ L hc ⟨k, Ideal.mul_mem_left _ _ hk⟩
  · subst h
    exact h₂ K rfl (h₁ K rfl)

/-- A witness point of the guarded system refutes VANISHES_ON in the same field. -/
theorem witnessContra_sound {K : Type} [Field K] {v : List String} {e ga gb : List Sparse}
    {ka kb : Kind} (h : witnessContra ⟨v, e, ga, ka⟩ ⟨v, e, gb, kb⟩ = true)
    (ha : Holds K ⟨v, e, ga, ka⟩) (hb : Holds K ⟨v, e, gb, kb⟩) : False := by
  cases ka <;> cases kb <;> simp only [witnessContra, Bool.false_eq_true, beq_iff_eq] at h
  subst h
  obtain ⟨x, hxe, hxg⟩ := hb
  exact hxg _ (List.mem_append_right _ (List.mem_singleton_self _))
    (ha x ⟨hxe, fun g hg => hxg g (List.mem_append_left _ hg)⟩)

/-- The semantic 3a profile over the executable `GPProfile.ops`. A context's truth is truth in
every field of its characteristic: scopes denote characteristics, so `Means` is unchanged
(`means_iff`), and contradictions may pass to the algebraic closure (G3a review §2). -/
noncomputable def profile : Semantic.Profile.{1} where
  toProfileOps := GPProfile.ops
  Ctx := FieldCtx
  mem K sc := Scope.mem K.carrier sc
  Holds s K := ∀ L : FieldCtx, ringChar L.carrier = ringChar K.carrier → Holds L.carrier s
  le_sound a b K h hm := Scope.le_den h hm
  contra_sound a b K h ha hb := by
    obtain ⟨va, ea, ga, ka⟩ := a
    obtain ⟨vb, eb, gb, kb⟩ := b
    change GPProfile.contra _ _ = true at h
    simp only [GPProfile.contra, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    rcases h with (⟨rfl, hk | hk⟩ | hw) | hw
    · exact kindContra_sound hk K ha hb
    · exact kindContra_sound hk K hb ha
    · exact witnessContra_sound hw (ha K rfl) (hb K rfl)
    · exact witnessContra_sound hw (hb K rfl) (ha K rfl)

/-! The executable `contra` table on `{x² = 0}` (G3a review §2), and two non-pairs. -/
section ContraTable
private def sys (k : Kind) (guards : List Sparse := []) : GPProfile.Stmt := ⟨["x"], [[([2], 1)]], guards, k⟩
private def hx : Sparse := [([1], 1)]
example : GPProfile.contra (sys .empty) (sys .nonempty) = true := by decide
example : GPProfile.contra (sys (.inIdeal hx)) (sys (.notInIdeal hx)) = true := by decide
example : GPProfile.contra (sys (.notInIdeal hx)) (sys .empty) = true := by decide
example : GPProfile.contra (sys (.vanishesOn hx)) (sys .nonempty [hx]) = true := by decide
-- x ∈ √(x²) but x ∉ (x²): VANISHES_ON(x) and NOT_IN_IDEAL(x) are compatible.
example : GPProfile.contra (sys (.vanishesOn hx)) (sys (.notInIdeal hx)) = false := by decide
example : GPProfile.contra (sys (.inIdeal hx)) (sys (.notInIdeal [([0], 1)])) = false := by decide
end ContraTable

/-- The Kernel's meaning is truth in every field whose characteristic the scope denotes. -/
theorem means_iff {s : GPProfile.Stmt} {sc : GPProfile.Scope} :
    Semantic.Means profile s sc ↔ ∀ K : FieldCtx, Scope.mem K.carrier sc → Holds K.carrier s := by
  constructor
  · intro h K hK
    exact h K hK K rfl
  · intro h K hK L hL
    exact h L (by unfold Scope.mem; rw [hL]; exact hK)

/-- The executable clauses are the semantic profile's clauses. -/
abbrev SClause := Semantic.Clause profile.toProfileOps

theorem accepts_claim_meaning (clauses : List GPProfile.Clause) (receipts : List Receipt)
    (w : Warrant) (name : String) (accepted : accepts clauses receipts w name = true) :
    Semantic.ClaimMeaning profile clauses w.claim := by
  unfold accepts at accepted
  simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq, decide_eq_true_eq] at accepted
  obtain ⟨wf, c, hc, ⟨⟨hkey, -⟩, -⟩, r, -, hok⟩ := accepted
  have hcheck := hok.2
  have nodup : (clauses.map (·.key)).Nodup := by
    unfold wellFormed at wf
    simp only [Bool.and_eq_true, beq_iff_eq] at wf
    exact nodup_of_eraseDups_length_eq _ (by simpa only [List.length_map] using wf.1)
  have means : Semantic.Means profile c.stmt c.scope := by
    refine means_iff.mpr fun K hK => ?_
    unfold Check.ok at hcheck
    split at hcheck
    · rename_i r' hr'
      exact check_sound hr' hK
    · contradiction
  refine ⟨⟨c, hc, hkey⟩, fun c' hc' hkey' => ?_⟩
  have := key_unique_of_nodup clauses (·.key) nodup c' c hc' hc (hkey'.trans hkey.symm)
  exact this ▸ means

theorem base_validator_sound (clauses : List GPProfile.Clause) (receipts : List Receipt)
    (snapshot : Snapshot) :
    Semantic.BaseValidatorSound profile clauses
      { Admission.refuseAll with receipt := accepts clauses receipts } snapshot := by
  constructor
  · intro w member name accepted
    exact ⟨w, member, rfl, accepts_claim_meaning clauses receipts w name accepted⟩
  · intros; contradiction
  · intros; contradiction

/-- Fold soundness for the 3a profile: a held claim means its registered statement in every
field whose characteristic its scope denotes. -/
theorem fold_held_meaning (clauses : List GPProfile.Clause) (receipts : List Receipt)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (GPProfile.admission clauses receipts) events = .ok state)
    (heldClaim : held state claim = true) :
    (∃ c ∈ clauses, c.key = claim) ∧
    ∀ c ∈ clauses, c.key = claim → ∀ K : FieldCtx, Scope.mem K.carrier c.scope →
      Holds K.carrier c.stmt :=
  have h := Semantic.fold_held_meaning profile clauses _ events state claim
    (base_validator_sound clauses receipts state.snapshot) folded heldClaim
  ⟨h.1, fun c hc hk => means_iff.mp (h.2 c hc hk)⟩

end GPBinding.Admission
