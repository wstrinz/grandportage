import GPBinding.Matroid.Frame

/-!
The frame theorem (ENCODING-FRAME, post-G3a §4.3). Any realization moves to the standard frame by
the Cramer map of the first basis and nonzero rescalings (`normalize`); with `frame_iff`, a rank-3
matroid is realizable over `K` exactly when the Lean encoder's framed system has a `K`-point.
-/

noncomputable section

namespace GPBinding.Matroid
open GPProfile GPProfile.Matroid GPBinding.Binder GPBinding.Admission MvPolynomial HexMvPolyMathlib

variable {K : Type*} [Field K]

/-- Invertible rows and nonzero rescalings preserve which determinants vanish. -/
theorem realizes_scaled {M : Data} {vec : ℕ → Fin 3 → K} (hR : Realizes M vec) (lam : ℕ → K)
    (hlam : ∀ j, lam j ≠ 0) (r₀ r₁ r₂ : Fin 3 → K) (hr : det3 r₀ r₁ r₂ ≠ 0) :
    Realizes M (fun j => lam j • apply3 r₀ r₁ r₂ (vec j)) := by
  intro t ht
  rw [det3_smul, det3_apply3, ← hR t ht]
  simp [mul_eq_zero, hlam, hr]

theorem colK_const (n : ℕ) (x : Fin n → K) (p q r : ℤ) :
    colK n x (.const p, .const q, .const r) = ![(p : K), (q : K), (r : K)] := by
  simp [colK, entryK]

theorem nonbasis_ne {M : Data} {vec : ℕ → Fin 3 → K} (hR : Realizes M vec) {a b c : ℕ}
    (ha : a < M.n) (hb : b < M.n) (hc : c < M.n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hnb : M.nonbasis (a, b, c) = false) : det3 (vec a) (vec b) (vec c) ≠ 0 := by
  intro h0
  have := (det_zero_iff hR ha hb hc hab hac hbc).mp h0
  rw [hnb] at this
  exact Bool.noConfusion this

theorem nb_eq (M : Data) (a b c x y z : ℕ) (h : ∀ l : List ℕ,
    (l.contains a && l.contains b && l.contains c) = (l.contains x && l.contains y && l.contains z)) :
    M.nonbasis (a, b, c) = M.nonbasis (x, y, z) := by
  simp only [Data.nonbasis]; congr 1; funext l; exact h l

/-- The three Cramer coordinates of `y` against the basis `v₀, v₁, v₂`. -/
theorem apply3_cross (v₀ v₁ v₂ y : Fin 3 → K) (q₀ q₁ q₂ : K) :
    apply3 (q₀ • cross v₁ v₂) (q₁ • cross v₂ v₀) (q₂ • cross v₀ v₁) y =
      ![q₀ * det3 y v₁ v₂, q₁ * det3 v₀ y v₂, q₂ * det3 v₀ v₁ y] := by
  simp only [apply3, dot, cross, det3, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  congr 1
  · ring
  · congr 1
    · ring
    · congr 1; ring

theorem smul_vec3 (q a b c : K) : q • ![a, b, c] = ![q * a, q * b, q * c] := by
  funext i; fin_cases i <;> simp

/-- Every realization moves to one whose frame columns are the encoder's constants. -/
theorem normalize {M : Data} {frame : List Nat} (hf : M.frame = some frame) {vec : ℕ → Fin 3 → K}
    (hR : Realizes M vec) :
    ∃ w : ℕ → Fin 3 → K, Realizes M w ∧
      ∀ j ∈ frame, ∀ n (x : Fin n → K), colK n x (M.columns frame j) = w j := by
  obtain ⟨a, b, c, habc, hnb, hcase⟩ := frame_spec hf
  obtain ⟨hab, hbc, hc⟩ := mem_triples.mp habc
  have hab' : a ≠ b := by omega
  have hac' : a ≠ c := by omega
  have hbc' : b ≠ c := by omega
  have hba : b ≠ a := fun e => hab' e.symm
  have hca : c ≠ a := fun e => hac' e.symm
  have hcb : c ≠ b := fun e => hbc' e.symm
  have hD : det3 (vec a) (vec b) (vec c) ≠ 0 :=
    nonbasis_ne hR (by omega) (by omega) hc hab' hac' hbc' hnb
  have ca : det3 (vec a) (vec a) (vec c) = 0 := det3_self12 _ _
  have cb : det3 (vec a) (vec b) (vec a) = 0 := det3_self13 _ _
  have cc : det3 (vec b) (vec b) (vec c) = 0 := det3_self12 _ _
  have cd : det3 (vec a) (vec b) (vec b) = 0 := det3_self23 _ _
  have ce : det3 (vec c) (vec b) (vec c) = 0 := det3_self13 _ _
  have cf : det3 (vec a) (vec c) (vec c) = 0 := det3_self23 _ _
  rcases hcase with hfr | ⟨f, hfr, hfn, hfa, hfb, hfc, h1, h2, h3⟩
  · subst hfr
    refine ⟨fun j => (if j = a ∨ j = b ∨ j = c then (det3 (vec a) (vec b) (vec c))⁻¹ else 1) •
        apply3 ((1 : K) • cross (vec b) (vec c)) ((1 : K) • cross (vec c) (vec a)) ((1 : K) • cross (vec a) (vec b))
          (vec j),
      realizes_scaled hR _ (fun j => by split_ifs <;> simp [hD]) _ _ _
        (by rw [det3_smul, det3_cross]; simp [hD]), ?_⟩
    intro j hj n x
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with h | h | h <;> rw [h] <;>
      simp only [Data.columns, List.idxOf?, List.findIdx?_cons, beq_iff_eq, hab', hac', hbc', hba, hca, hcb,
        ite_true, ite_false, true_or, or_true, Option.map_some, colK_const, apply3_cross, smul_vec3, ca, cb, cc, cd,
        ce, cf] <;>
      simp [hD]
  · subst hfr
    have hu₀ : det3 (vec f) (vec b) (vec c) ≠ 0 := by
      refine nonbasis_ne hR hfn (by omega) hc hfb hfc hbc' ?_
      rw [nb_eq M f b c b c f (fun l => by
        cases l.contains f <;> cases l.contains b <;> cases l.contains c <;> rfl)]
      exact h3
    have hu₁ : det3 (vec a) (vec f) (vec c) ≠ 0 := by
      refine nonbasis_ne hR (by omega) hfn hc (fun e => hfa e.symm) hac' hfc ?_
      rw [nb_eq M a f c a c f (fun l => by
        cases l.contains f <;> cases l.contains a <;> cases l.contains c <;> rfl)]
      exact h2
    have hu₂ : det3 (vec a) (vec b) (vec f) ≠ 0 :=
      nonbasis_ne hR (by omega) (by omega) hfn hab' (fun e => hfa e.symm) (fun e => hfb e.symm) h1
    have hfa' : a ≠ f := fun e => hfa e.symm
    have hfb' : b ≠ f := fun e => hfb e.symm
    have hfc' : c ≠ f := fun e => hfc e.symm
    refine ⟨fun j => (if j = a then det3 (vec f) (vec b) (vec c) * (det3 (vec a) (vec b) (vec c))⁻¹
          else if j = b then det3 (vec a) (vec f) (vec c) * (det3 (vec a) (vec b) (vec c))⁻¹
          else if j = c then det3 (vec a) (vec b) (vec f) * (det3 (vec a) (vec b) (vec c))⁻¹ else 1) •
        apply3 ((det3 (vec f) (vec b) (vec c))⁻¹ • cross (vec b) (vec c))
          ((det3 (vec a) (vec f) (vec c))⁻¹ • cross (vec c) (vec a))
          ((det3 (vec a) (vec b) (vec f))⁻¹ • cross (vec a) (vec b)) (vec j),
      realizes_scaled hR _ (fun j => by split_ifs <;> simp [hD, hu₀, hu₁, hu₂]) _ _ _
        (by rw [det3_smul, det3_cross]; simp [hD, hu₀, hu₁, hu₂]), ?_⟩
    intro j hj n x
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with h | h | h | h <;> rw [h] <;>
      simp only [Data.columns, List.idxOf?, List.findIdx?_cons, beq_iff_eq, hab', hac', hbc', hba, hca, hcb,
        hfa, hfb, hfc, hfa', hfb', hfc', ite_true, ite_false, Option.map_some, colK_const, apply3_cross, smul_vec3,
        ca, cb, cc, cd, ce, cf] <;>
      field_simp <;> simp

/-- **ENCODING-FRAME.** A rank-3 matroid is realizable over `K` exactly when the Lean encoder's
framed system has a `K`-point. -/
theorem frame_iff {M : Data} {vars : List String} {eqs guards : List Sparse}
    (h : M.system = some (vars, eqs, guards)) :
    (∃ vec : ℕ → Fin 3 → K, Realizes M vec) ↔ ∃ x, LocusE K ⟨vars, eqs, guards, .nonempty⟩ x := by
  constructor
  · rintro ⟨vec, hR⟩
    obtain ⟨frame, hf, hvars, -, -, -⟩ := system_spec h
    obtain ⟨w, hw, hfix⟩ := normalize hf hR
    have hn : 3 * (free M frame).length ≤ vars.length := by rw [hvars, vars_length]
    refine ⟨pointOf M frame w vars.length, locus_of_cols h hf hw _ fun j hj => ?_⟩
    by_cases hjf : j ∈ frame
    · exact hfix j hjf _ _
    · exact col_free w hn hj hjf
  · rintro ⟨x, hx⟩
    exact realizes_of_point h hx

/-- NONEMPTY of the encoder's system is realizability; EMPTY is non-realizability. -/
theorem holdsE_nonempty_iff {M : Data} {vars : List String} {eqs guards : List Sparse}
    (h : M.system = some (vars, eqs, guards)) :
    HoldsE K ⟨vars, eqs, guards, .nonempty⟩ ↔ ∃ vec : ℕ → Fin 3 → K, Realizes M vec := by
  simp only [HoldsE]
  exact (frame_iff h).symm

theorem holdsE_empty_iff {M : Data} {vars : List String} {eqs guards : List Sparse}
    (h : M.system = some (vars, eqs, guards)) :
    HoldsE K ⟨vars, eqs, guards, .empty⟩ ↔ ¬ ∃ vec : ℕ → Fin 3 → K, Realizes M vec := by
  rw [frame_iff h, not_exists]
  exact Iff.rfl

end GPBinding.Matroid
