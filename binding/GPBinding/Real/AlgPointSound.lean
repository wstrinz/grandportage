import GPProfile.Real.AlgPoint
import GPBinding.Binder.Explicit
import GPBinding.Admission.Profile
import HexPolyMathlib
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
Soundness of the `algPoint` receipt (3b): an accepted certificate proves the 3a statement
`NOT_IN_IDEAL(1)` in every field of characteristic 0.

Let `L` have characteristic 0 and `L̄` be its algebraic closure. The defining polynomial `m` is
nonconstant, so it has a root `θ ∈ L̄`; put `y := q(θ)`. Reduction modulo `m` respects
evaluation at `θ`, so every equation vanishes at `y`, and the Bezout identity
`a·ĝ + b·m = 1` gives `a(θ) · g(y) = 1`, so every guard is nonzero at `y`. If
`1 · (∏ guards)^k` lay in the ideal of the equations over `L`, the ring hom
`L[x] → L̄, f ↦ f(y)` would kill it, yet it sends it to `(∏ g(y))^k ≠ 0`.
-/

noncomputable section

namespace GPBinding.Real.AlgPoint
open GPProfile GPProfile.Real GPProfile.Real.RAlg HexPolyMathlib Polynomial
open GPBinding.Admission

variable {F : Type*} [Field F] [CharZero F]

/-- The value at `x : F` of a dense rational polynomial. -/
def fv (p : D) (x : F) : F := (toPolynomial p).eval₂ (Rat.castHom F) x

variable {x : F}

/-! ## Evaluation of dense polynomials -/

@[simp] theorem fv_zero : fv 0 x = 0 := by simp [fv, toPolynomial_zero]
@[simp] theorem fv_one : fv 1 x = 1 := by simp [fv, toPolynomial_one]
@[simp] theorem fv_C (c : ℚ) : fv (RAlg.C c) x = c := by simp [fv, RAlg.C, toPolynomial_C]
@[simp] theorem fv_add (p q : D) : fv (p + q) x = fv p x + fv q x := by
  simp [fv, toPolynomial_add]
@[simp] theorem fv_sub (p q : D) : fv (p - q) x = fv p x - fv q x := by
  simp [fv, toPolynomial_sub]
@[simp] theorem fv_mul (p q : D) : fv (p * q) x = fv p x * fv q x := by
  simp [fv, toPolynomial_mul, eval₂_mul]

/-- Reduction modulo `s` respects evaluation at a root of `s`. -/
theorem fv_mod {p s : D} (hs : fv s x = 0) : fv (p % s) x = fv p x := by
  have h := EuclideanDomain.div_add_mod (toPolynomial p) (toPolynomial s)
  unfold fv at hs ⊢
  rw [toPolynomial_mod]
  conv_rhs => rw [← h]
  rw [eval₂_add, eval₂_mul, hs, zero_mul, zero_add]

theorem eq_zero_of_isZero {p : D} (h : p.isZero = true) : p = 0 :=
  (Hex.DensePoly.size_eq_zero_iff p).mp ((Hex.DensePoly.isZero_eq_true_iff p).mp h)

theorem fv_powMod {b s : D} (hs : fv s x = 0) : ∀ k, fv (powMod b s k) x = fv b x ^ k
  | 0 => by simp [powMod]
  | k + 1 => by rw [powMod, fv_mod hs, fv_mul, fv_powMod hs k, pow_succ]

theorem fv_monoAt {cs : List D} {s : D} {e : List ℕ} (hs : fv s x = 0) :
    ∀ k, fv (monoAt cs s e k) x = ∏ i ∈ Finset.range k, fv (cs.getD i 0) x ^ e.getD i 0
  | 0 => by simp [monoAt]
  | k + 1 => by
    rw [monoAt, fv_mod hs, fv_mul, fv_monoAt hs k, fv_powMod hs, Finset.prod_range_succ]

theorem fv_foldl {α : Type} (G : α → D) (x : F) : ∀ (l : List α) (init : D),
    fv (l.foldl (fun acc a => acc + G a) init) x = fv init x + (l.map fun a => fv (G a) x).sum
  | [], init => by simp
  | a :: l, init => by simp [List.foldl_cons, fv_foldl G x l, add_assoc]

/-- At a root of `s`, the reduced composition is the polynomial at the coordinates. -/
theorem fv_fieldEval {n : ℕ} {cs : List D} {s : D} {f : Sparse} (hs : fv s x = 0) :
    fv (fieldEval n cs s f) x = Binder.valueE F n f (fun i => fv (cs.getD i 0) x) := by
  have hfold := fv_foldl (fun t : List ℕ × ℚ => RAlg.C t.2 * monoAt cs s t.1 n) x f 0
  rw [fieldEval, fv_mod hs, hfold, fv_zero, zero_add, Binder.valueE_eq]
  congr 1
  apply List.map_congr_left
  intro t _
  rw [fv_mul, fv_C, fv_monoAt hs,
    Fin.prod_univ_eq_prod_range (fun i => fv (cs.getD i 0) x ^ t.1.getD i 0)]

/-- A nonconstant defining polynomial has a root in every algebraically closed field of
characteristic 0. -/
theorem exists_root {m : D} (hm : 2 ≤ m.size) (K : Type*) [Field K] [CharZero K]
    [IsAlgClosed K] : ∃ θ : K, fv m θ = 0 := by
  have hc : ((toPolynomial m).map (Rat.castHom K)).coeff (m.size - 1) ≠ 0 := by
    rw [coeff_map, coeff_toPolynomial, eq_ratCast, Rat.cast_ne_zero]
    exact Hex.DensePoly.coeff_last_ne_zero_of_pos_size m (by omega)
  have hpos : 0 < ((toPolynomial m).map (Rat.castHom K)).natDegree :=
    lt_of_lt_of_le (by omega) (le_natDegree_of_ne_zero hc)
  obtain ⟨θ, hθ⟩ := IsAlgClosed.exists_root _ (natDegree_pos_iff_degree_pos.mp hpos).ne'
  exact ⟨θ, by rw [fv, ← eval_map]; exact hθ⟩

/-! ## The 3a meaning in characteristic 0 -/

/-- In characteristic 0 the coefficientwise cast is the ring hom `map (Rat.castHom F)`. -/
theorem toK_eq_map {σ : Type*} (P : MvPolynomial σ ℚ) :
    toK (K := F) P = MvPolynomial.map (Rat.castHom F) P := by
  ext d
  simp [MvPolynomial.coeff_map]

/-- On arity-correct polynomials the explicit value is the 3a `value`. -/
theorem value_eq_valueE {n : ℕ} {p : Sparse} (h : sparseArity n p = true) (y : Fin n → F) :
    value n p y = Binder.valueE F n p y := by
  unfold Binder.valueE value
  rw [Binder.toK_meaning h fun c _ => mem_good.mpr (by exact_mod_cast c.den_nz)]

theorem exists_zip_of_mem {α β : Type} {l : List α} {l' : List β} (hlen : l.length = l'.length)
    {a : α} (ha : a ∈ l) : ∃ b, (a, b) ∈ l.zip l' := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  have hi' : i < (l.zip l').length := by simp [List.length_zip, ← hlen, hi]
  exact ⟨l'[i]'(hlen ▸ hi), by simpa using List.getElem_mem hi'⟩

/-! ## Soundness -/

/-- An accepted certificate asks NOT_IN_IDEAL(1) and gives a point of the locus in every
algebraically closed field of characteristic 0. -/
theorem algPointCheck_point {s : Stmt} {c : AlgPointCert} (h : algPointCheck s c = true)
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] :
    s.kind = .notInIdeal (oneP s.vars.length) ∧ ∃ y : Fin s.vars.length → K, Locus s y := by
  unfold algPointCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hk, hsize⟩, -⟩, harE⟩, harG⟩, hE⟩, hblen⟩, hB⟩ := h
  obtain ⟨θ, hθ⟩ := exists_root hsize K
  refine ⟨hk, fun i => fv ((c.coords.map ofU).getD i 0) θ, fun e he => ?_, fun g hg => ?_⟩
  · rw [value_eq_valueE (harE e he), ← fv_fieldEval hθ, eq_zero_of_isZero (hE e he), fv_zero]
  · obtain ⟨ab, hab⟩ := exists_zip_of_mem hblen hg
    have h1 := congrArg (fv · θ) (eq_zero_of_isZero (hB _ hab))
    simp only [fv_sub, fv_add, fv_mul, fv_one, fv_zero, hθ, mul_zero, add_zero] at h1
    rw [value_eq_valueE (harG g hg), ← fv_fieldEval hθ]
    intro h0
    rw [h0, mul_zero, zero_sub, neg_eq_zero] at h1
    exact one_ne_zero h1

/-- **Soundness.** An accepted `algPoint` certificate proves the statement in every field of
characteristic 0 (3a's per-field truth, `Admission.Holds`). -/
theorem algPointCheck_sound {s : Stmt} {c : AlgPointCert} (h : algPointCheck s c = true)
    (L : Type*) [Field L] [CharZero L] : GPBinding.Admission.Holds L s := by
  obtain ⟨hk, y, hyE, hyG⟩ := algPointCheck_point h (AlgebraicClosure L)
  obtain ⟨v, e, g, kd⟩ := s
  simp only at hk
  subst hk
  unfold Holds
  simp only
  rintro ⟨k, hk⟩
  let φ : MvPolynomial (Fin v.length) L →+* AlgebraicClosure L :=
    MvPolynomial.eval₂Hom (algebraMap L (AlgebraicClosure L)) y
  have hφ : ∀ p : Sparse, φ (toK (meaning v.length p)) = value v.length p y := by
    intro p
    rw [value, toK_eq_map, toK_eq_map, MvPolynomial.eval_map]
    simp only [φ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
    rw [RingHom.ext_rat ((algebraMap L (AlgebraicClosure L)).comp (Rat.castHom L))
      (Rat.castHom (AlgebraicClosure L))]
  have hspan : Ideal.span {f | f ∈ e.map fun q => toK (K := L) (meaning v.length q)} ≤
      RingHom.ker φ :=
    Ideal.span_le.mpr fun f hf => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hf
      exact (RingHom.mem_ker).mpr ((hφ q).trans (hyE q hq))
  have h0 := (RingHom.mem_ker).mp (hspan hk)
  rw [map_mul, Binder.toK_meaning_one, map_one, one_mul, map_pow, map_list_prod,
    List.map_map] at h0
  refine pow_ne_zero k (List.prod_ne_zero fun hz => ?_) h0
  obtain ⟨q, hq, hq0⟩ := List.mem_map.mp hz
  exact hyG q hq ((hφ q).symm.trans hq0)

/-- The corollary at the Kernel: an accepted certificate gives the statement's meaning in 3a's
semantic profile at the characteristic-0 scope. -/
theorem algPointCheck_means {s : Stmt} {c : AlgPointCert} (h : algPointCheck s c = true) :
    GP50.Semantic.Means GPBinding.Admission.profile s Scope.char0Only := by
  refine means_iff.mpr fun K hK => ?_
  have h0 : ringChar K.carrier = 0 := by
    rcases hK with ⟨h0, -⟩ | ⟨-, hm⟩
    · exact h0
    · simp [Scope.char0Only] at hm
  have : CharP K.carrier 0 := ringChar.of_eq h0
  have : CharZero K.carrier := CharP.charP_to_charZero K.carrier
  exact algPointCheck_sound h K.carrier

end GPBinding.Real.AlgPoint
