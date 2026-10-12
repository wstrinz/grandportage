import GPBinding.Admission.Profile
import GPProfile.Real.Profile
import GPBinding.Real.NumberFieldSound
import Mathlib.Algebra.Ring.Semireal.Defs
import Mathlib.Data.Real.Basic

/-!
The semantic 3b profile ([3B-PROFILE-DESIGN.md](../../../docs/3B-PROFILE-DESIGN.md)) over the
executable `GPProfile.Real.ops3`. Contexts are 3a's `FieldCtx`.

- `alg s` means what it means in 3a (`GPBinding.Admission.profile`): truth in every field of the
  context's characteristic.
- `orderFree s` means 3a's per-field truth `Admission.Holds` in the context field itself.
- `real r e` means that `r` has no point, or some point, in the context field, where a sign atom
  reads the sign of a value through squares (zero; a nonzero square; otherwise negative). Over ℝ
  that is the usual order.
- `nf p` means `NumberField.NFHolds`: `m` is irreducible over ℚ and, in characteristic 0, the point
  lies on the locus at every root of `m` (and of `r`) in the context field.

- `realCover r bs` means that every point of `r` in the context field is a point of some branch
  (3a's `cover` kind, with sign atoms read through squares).

Scope `semireal` is `IsSemireal`; scope `real` is a field isomorphic to ℝ; scope `ratField` is a
field isomorphic to ℚ.
-/

noncomputable section

namespace GPBinding.Real
open GPProfile GPProfile.Real GPBinding.Admission

/-! ## The real family's truth -/

/-- The sign of a field element read through squares: `0`, `1` for a nonzero square, else `-1`. -/
def signSq {K : Type*} [Field K] (y : K) : Int :=
  open Classical in if y = 0 then 0 else if IsSquare y then 1 else -1

/-- The points of a real system: equations vanish, guards do not, signs are as required. -/
def RealLocus {K : Type*} [Field K] (r : RealSys) (x : Fin r.vars.length → K) : Prop :=
  (∀ e ∈ r.eqs, value _ e x = 0) ∧ (∀ g ∈ r.guards, value _ g x ≠ 0) ∧
    (∀ p ∈ r.signs, signSq (value _ p.1 x) = p.2)

def RealHolds (K : Type*) [Field K] (r : RealSys) : Exist → Prop
  | .empty => ∀ x, ¬ RealLocus (K := K) r x
  | .nonempty => ∃ x, RealLocus (K := K) r x

/-- A real-family cover: every point of `r` is a point of some branch. -/
def RealCoverHolds (K : Type*) [Field K] (r : RealSys) (bs : List RBranch) : Prop :=
  ∀ x : Fin r.vars.length → K, RealLocus r x → ∃ b ∈ bs, RealLocus (r.branch b) x

/-! ## ℝ is semireal, and so is every field isomorphic to it -/

theorem IsSumSq.map_ringHom {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) {s : R}
    (h : IsSumSq s) : IsSumSq (f s) := by
  induction h with
  | zero => simpa using IsSumSq.zero
  | sq_add a _ ih => simpa [map_add, map_mul] using IsSumSq.sq_add (f a) ih

theorem isSemireal_of_equiv_real {K : Type*} [Field K] (e : K ≃+* ℝ) : IsSemireal K := by
  apply IsSemireal.of_not_isSumSq_neg_one
  intro h
  have := IsSumSq.map_ringHom e.toRingHom h
  rw [map_neg, map_one] at this
  exact IsSemireal.not_isSumSq_neg_one ℝ this

/-- ℚ is semireal, and so is every field isomorphic to it. -/
theorem isSemireal_of_equiv_rat {K : Type*} [Field K] (e : K ≃+* ℚ) : IsSemireal K := by
  apply IsSemireal.of_not_isSumSq_neg_one
  intro h
  have := IsSumSq.map_ringHom e.toRingHom h
  rw [map_neg, map_one] at this
  exact IsSemireal.not_isSumSq_neg_one ℚ this

/-! ## The profile -/

/-- Scope membership for a 3b scope. -/
def Scope3.mem (K : Spike.FieldCtx) : Scope3 → Prop
  | .alg sc => Scope.mem K.carrier sc
  | .semireal => IsSemireal K.carrier
  | .real => Nonempty (K.carrier ≃+* ℝ)
  | .ratField => Nonempty (K.carrier ≃+* ℚ)

/-- Truth of a 3b statement at a context. -/
def Holds3 : Stmt3 → Spike.FieldCtx → Prop
  | .alg s, K => Admission.profile.Holds s K
  | .orderFree s, K => Admission.Holds K.carrier s
  | .real r e, K => RealHolds K.carrier r e
  | .nf p, K => NumberField.NFHolds K.carrier p
  | .realCover r bs, K => RealCoverHolds K.carrier r bs

theorem le3_sound (a b : Scope3) (K : Spike.FieldCtx) (h : Scope3.le a b = true) (hm : Scope3.mem K a) :
    Scope3.mem K b := by
  cases a <;> cases b <;> simp only [Scope3.le, Bool.false_eq_true] at h
  · exact Admission.profile.le_sound _ _ K h hm
  · exact hm
  · exact isSemireal_of_equiv_real (Classical.choice hm)
  · exact hm
  · exact isSemireal_of_equiv_rat (Classical.choice hm)
  · exact hm

theorem orderFree_contra {K : Type*} [Field K] {a b : Stmt} (hs : sameSys a b = true)
    (ha : a.kind = .empty) (hb : b.kind = .nonempty) (hA : Admission.Holds K a)
    (hB : Admission.Holds K b) : False := by
  obtain ⟨va, ea, ga, ka⟩ := a
  obtain ⟨vb, eb, gb, kb⟩ := b
  simp only [sameSys, Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hs
  simp only at ha hb
  subst ha hb
  simp only [Admission.Holds] at hA hB
  obtain ⟨x, hx⟩ := hB
  exact hA x hx

theorem contra3_sound (a b : Stmt3) (K : Spike.FieldCtx) (h : Stmt3.contra a b = true)
    (ha : Holds3 a K) (hb : Holds3 b K) : False := by
  cases a with
  | alg a =>
    cases b with
    | alg b => exact Admission.profile.contra_sound a b K h ha hb
    | orderFree _ => simp [Stmt3.contra] at h
    | real _ _ => simp [Stmt3.contra] at h
    | nf _ => simp [Stmt3.contra] at h
    | realCover _ _ => simp [Stmt3.contra] at h
  | orderFree a =>
    cases b with
    | orderFree b =>
      simp only [Stmt3.contra, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      obtain ⟨hs, ⟨hka, hkb⟩ | ⟨hka, hkb⟩⟩ := h
      · exact orderFree_contra hs hka hkb ha hb
      · have hs' : sameSys b a = true := by
          simp only [sameSys, Bool.and_eq_true, beq_iff_eq] at hs ⊢
          exact ⟨⟨hs.1.1.symm, hs.1.2.symm⟩, hs.2.symm⟩
        exact orderFree_contra hs' hkb hka hb ha
    | alg _ => simp [Stmt3.contra] at h
    | real _ _ => simp [Stmt3.contra] at h
    | nf _ => simp [Stmt3.contra] at h
    | realCover _ _ => simp [Stmt3.contra] at h
  | real r e =>
    cases b with
    | real r' e' =>
      simp only [Stmt3.contra, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
      obtain ⟨rfl, hne⟩ := h
      cases e <;> cases e' <;> simp at hne
      · obtain ⟨x, hx⟩ := hb; exact ha x hx
      · obtain ⟨x, hx⟩ := ha; exact hb x hx
    | alg _ => simp [Stmt3.contra] at h
    | orderFree _ => simp [Stmt3.contra] at h
    | nf _ => simp [Stmt3.contra] at h
    | realCover _ _ => simp [Stmt3.contra] at h
  | nf _ => cases b <;> simp [Stmt3.contra] at h
  | realCover _ _ => cases b <;> simp [Stmt3.contra] at h

/-- The semantic 3b profile. -/
def profile3 : GP50.Semantic.Profile.{1} where
  toProfileOps := ops3
  Ctx := Spike.FieldCtx
  mem K sc := Scope3.mem K sc
  Holds s K := Holds3 s K
  le_sound a b K h hm := le3_sound a b K h hm
  contra_sound a b K h ha hb := contra3_sound a b K h ha hb

/-- `Means` for the real family over ℝ-scope: truth in every field isomorphic to ℝ. -/
theorem means_real {r : RealSys} {e : Exist} :
    GP50.Semantic.Means profile3 (Stmt3.real r e) Scope3.real ↔
      ∀ K : Spike.FieldCtx, Nonempty (K.carrier ≃+* ℝ) → RealHolds K.carrier r e := Iff.rfl

end GPBinding.Real
