import GPBinding.Matroid.Eval

/-!
ENCODING-FRAME (post-G3a §4.3; Will 2026-10-05: discharge it in Lean).

A rank-3 matroid `M` is realizable over a field `K` exactly when the Lean encoder's framed system
has a `K`-point (`frame_iff`). One direction reads a realization off the point's columns; the other
moves any realization to the standard frame by an invertible linear map and nonzero rescalings,
which never change whether a determinant vanishes.

The CLI checks that each matroid claim's system is this encoder's output (`gp_ledger` frames), so
the theorem applies to the claim's own statement.
-/

noncomputable section

namespace GPBinding.Matroid
open GPProfile GPProfile.Matroid GPBinding.Binder GPBinding.Admission MvPolynomial HexMvPolyMathlib

variable {K : Type*} [Field K]

/-- `vec` realizes `M` over `K`: a triple's vectors are dependent exactly when it is a non-basis. -/
def Realizes (M : Data) (vec : ℕ → Fin 3 → K) : Prop :=
  ∀ t ∈ triples M.n, det3 (vec t.1) (vec t.2.1) (vec t.2.2) = 0 ↔ M.nonbasis t = true

theorem mem_triples {n a b c : ℕ} : (a, b, c) ∈ triples n ↔ a < b ∧ b < c ∧ c < n := by
  simp only [triples, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    Bool.and_eq_true, decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨a', -, b', -, c', ⟨hc, hab, hbc⟩, rfl, rfl, rfl⟩
    exact ⟨hab, hbc, hc⟩
  · rintro ⟨hab, hbc, hc⟩
    exact ⟨a, by omega, b, by omega, c, ⟨hc, hab, hbc⟩, rfl, rfl, rfl⟩

theorem nonbasis_swap12 (M : Data) (a b c : ℕ) : M.nonbasis (b, a, c) = M.nonbasis (a, b, c) := by
  simp only [Data.nonbasis]
  congr 1; funext l
  cases l.contains a <;> cases l.contains b <;> rfl

theorem nonbasis_swap23 (M : Data) (a b c : ℕ) : M.nonbasis (a, c, b) = M.nonbasis (a, b, c) := by
  simp only [Data.nonbasis]
  congr 1; funext l
  cases l.contains b <;> cases l.contains c <;> simp

/-- Zero-ness of a realization's determinant on any three distinct elements, in any order. -/
theorem det_zero_iff {M : Data} {vec : ℕ → Fin 3 → K} (hR : Realizes M vec) {a b c : ℕ}
    (ha : a < M.n) (hb : b < M.n) (hc : c < M.n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    det3 (vec a) (vec b) (vec c) = 0 ↔ M.nonbasis (a, b, c) = true := by
  rcases Nat.lt_or_gt_of_ne hab with h1 | h1 <;> rcases Nat.lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases Nat.lt_or_gt_of_ne hbc with h3 | h3
  · exact hR (a, b, c) (mem_triples.mpr ⟨h1, h3, hc⟩)
  · have hT := hR (a, c, b) (mem_triples.mpr ⟨h2, h3, hb⟩)
    have hnb : M.nonbasis (a, b, c) = M.nonbasis (a, c, b) := by
      simp only [Data.nonbasis]; congr 1; funext l
      cases l.contains a <;> cases l.contains b <;> cases l.contains c <;> rfl
    have hd : det3 (vec a) (vec b) (vec c) = -det3 (vec a) (vec c) (vec b) := by simp only [det3]; ring
    rw [hnb, ← hT, hd]; exact neg_eq_zero
  · omega
  · have hT := hR (c, a, b) (mem_triples.mpr ⟨h2, h1, hb⟩)
    have hnb : M.nonbasis (a, b, c) = M.nonbasis (c, a, b) := by
      simp only [Data.nonbasis]; congr 1; funext l
      cases l.contains a <;> cases l.contains b <;> cases l.contains c <;> rfl
    have hd : det3 (vec a) (vec b) (vec c) = det3 (vec c) (vec a) (vec b) := by simp only [det3]; ring
    rw [hnb, ← hT, hd]
  · have hT := hR (b, a, c) (mem_triples.mpr ⟨h1, h2, hc⟩)
    have hnb : M.nonbasis (a, b, c) = M.nonbasis (b, a, c) := by
      simp only [Data.nonbasis]; congr 1; funext l
      cases l.contains a <;> cases l.contains b <;> cases l.contains c <;> rfl
    have hd : det3 (vec a) (vec b) (vec c) = -det3 (vec b) (vec a) (vec c) := by simp only [det3]; ring
    rw [hnb, ← hT, hd]; exact neg_eq_zero
  · omega
  · have hT := hR (b, c, a) (mem_triples.mpr ⟨h3, h2, ha⟩)
    have hnb : M.nonbasis (a, b, c) = M.nonbasis (b, c, a) := by
      simp only [Data.nonbasis]; congr 1; funext l
      cases l.contains a <;> cases l.contains b <;> cases l.contains c <;> rfl
    have hd : det3 (vec a) (vec b) (vec c) = det3 (vec b) (vec c) (vec a) := by simp only [det3]; ring
    rw [hnb, ← hT, hd]
  · have hT := hR (c, b, a) (mem_triples.mpr ⟨h3, h1, ha⟩)
    have hnb : M.nonbasis (a, b, c) = M.nonbasis (c, b, a) := by
      simp only [Data.nonbasis]; congr 1; funext l
      cases l.contains a <;> cases l.contains b <;> cases l.contains c <;> rfl
    have hd : det3 (vec a) (vec b) (vec c) = -det3 (vec c) (vec b) (vec a) := by simp only [det3]; ring
    rw [hnb, ← hT, hd]; exact neg_eq_zero

/-! ## Reading the encoder's output -/

theorem system_spec {M : Data} {vars : List String} {eqs guards : List Sparse}
    (h : M.system = some (vars, eqs, guards)) :
    ∃ frame, M.frame = some frame ∧ vars = M.vars frame ∧ M.frameOK frame vars.length = true ∧
      eqs = ((triples M.n).filter fun t => M.nonbasis t && M.det frame vars.length t != 0).map
        (fun t => ofHex (M.det frame vars.length t)) ∧
      guards = ((triples M.n).filter fun t => !M.nonbasis t && !isConst (M.det frame vars.length t)).map
        (fun t => ofHex (M.det frame vars.length t)) := by
  unfold Data.system at h
  cases hf : M.frame with
  | none => simp [hf] at h
  | some frame =>
    simp only [hf, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · simp at h
    · rename_i hok
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨frame, rfl, rfl, by simpa using hok, rfl, rfl⟩

theorem frameOK_at {M : Data} {frame : List Nat} {n : Nat} (h : M.frameOK frame n = true) {t : Nat × Nat × Nat}
    (ht : t ∈ triples M.n) :
    toHexQ n (ofHex (M.det frame n t)) = some (M.det frame n t) ∧
      (ofHex (M.det frame n t)).all (fun x => x.2.den == 1) = true ∧
      (M.nonbasis t = true → M.det frame n t = 0 ∨ isConst (M.det frame n t) = false) ∧
      (M.nonbasis t = false → M.det frame n t ≠ 0 ∧
        (isConst (M.det frame n t) = false ∨ isUnitConst (M.det frame n t) = true)) := by
  have := List.all_eq_true.mp h t ht
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  obtain ⟨⟨hrt, hint⟩, hcase⟩ := this
  refine ⟨hrt, hint, fun hnb => ?_, fun hnb => ?_⟩
  · simp only [hnb, if_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hcase
    exact hcase
  · simp only [hnb, Bool.false_eq_true, if_false, Bool.and_eq_true, bne_iff_ne, ne_eq,
      Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hcase
    exact hcase

theorem toK_C {σ : Type*} (q : ℚ) : toK (K := K) (MvPolynomial.C q : MvPolynomial σ ℚ) = MvPolynomial.C (q : K) := by
  classical
  ext d
  rw [coeff_toK, coeff_C, coeff_C]
  split_ifs <;> simp

/-- The value of a triple's determinant polynomial at a point is the determinant of its columns. -/
theorem det_eval {M : Data} {frame : List Nat} {n : Nat} (x : Fin n → K) (t : Nat × Nat × Nat) :
    eval x (toK (K := K) (toMvPolynomial (M.det frame n t))) =
      det3 (colK n x (M.columns frame t.1)) (colK n x (M.columns frame t.2.1)) (colK n x (M.columns frame t.2.2)) :=
  eval_det3P n x _ _ _

theorem unitConst_eval {n : Nat} {d : GPProfile.P n Rat} (h : isUnitConst d = true) (x : Fin n → K) :
    eval x (toK (K := K) (toMvPolynomial d)) ≠ 0 := by
  simp only [isUnitConst, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;>
    · simp only [HexMvPolyMathlib.toMvPolynomial_C, toK_C, eval_C]
      norm_num

/-! ## A point of the framed system realizes the matroid -/

theorem realizes_of_point {M : Data} {vars : List String} {eqs guards : List Sparse}
    (h : M.system = some (vars, eqs, guards)) {x : Fin vars.length → K}
    (hx : LocusE K ⟨vars, eqs, guards, .nonempty⟩ x) : ∃ vec : ℕ → Fin 3 → K, Realizes M vec := by
  obtain ⟨frame, -, -, hok, heqs, hguards⟩ := system_spec h
  refine ⟨fun j => colK vars.length x (M.columns frame j), fun t ht => ?_⟩
  obtain ⟨hrt, hint, hnbz, hbz⟩ := frameOK_at hok ht
  have hval : valueE K vars.length (ofHex (M.det frame vars.length t)) x =
      det3 (colK vars.length x (M.columns frame t.1)) (colK vars.length x (M.columns frame t.2.1))
        (colK vars.length x (M.columns frame t.2.2)) := by
    rw [valueE_det (K := K) _ hrt hint, det_eval]
  cases hnb : M.nonbasis t with
  | true =>
    simp only [iff_true]
    rcases hnbz hnb with h0 | hnc
    · rw [← det_eval, h0]; simp [toK_zero]
    · by_cases h0 : M.det frame vars.length t = 0
      · rw [← det_eval, h0]; simp [toK_zero]
      · rw [← hval]
        apply hx.1
        rw [heqs]
        exact List.mem_map.mpr ⟨t, List.mem_filter.mpr ⟨ht, by simp [hnb, h0]⟩, rfl⟩
  | false =>
    simp only [Bool.false_eq_true, iff_false]
    obtain ⟨hne, hc | hu⟩ := hbz hnb
    · rw [← hval]
      apply hx.2
      rw [hguards]
      exact List.mem_map.mpr ⟨t, List.mem_filter.mpr ⟨ht, by simp [hnb, hc]⟩, rfl⟩
    · rw [← det_eval]
      exact unitConst_eval hu x

/-! ## Frames, free elements and columns -/

/-- The elements outside the frame, in order: the encoder's free columns. -/
def free (M : Data) (frame : List Nat) : List Nat := (List.range M.n).filter fun i => !frame.contains i

theorem vars_length (M : Data) (frame : List Nat) : (M.vars frame).length = 3 * (free M frame).length := by
  simp only [Data.vars, free, List.length_flatMap, List.length_map, List.length_cons, List.length_nil]
  generalize (List.range M.n).filter (fun i => !frame.contains i) = l
  induction l with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega

theorem frame_spec {M : Data} {frame : List Nat} (h : M.frame = some frame) :
    ∃ a b c, (a, b, c) ∈ triples M.n ∧ M.nonbasis (a, b, c) = false ∧
      (frame = [a, b, c] ∨ ∃ f, frame = [a, b, c, f] ∧ f < M.n ∧ f ≠ a ∧ f ≠ b ∧ f ≠ c ∧
        M.nonbasis (a, b, f) = false ∧ M.nonbasis (a, c, f) = false ∧ M.nonbasis (b, c, f) = false) := by
  unfold Data.frame at h
  cases ht : (triples M.n).find? fun t => !M.nonbasis t with
  | none => simp [ht] at h
  | some t =>
    obtain ⟨a, b, c⟩ := t
    have hmem := List.mem_of_find?_eq_some ht
    have hnb := List.find?_some ht
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hnb
    simp only [ht, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
    refine ⟨a, b, c, hmem, hnb, ?_⟩
    generalize hd : List.find? _ (List.range M.n) = d at h
    cases d with
    | none => left; simpa using h.symm
    | some f =>
      right
      have hf := List.find?_some hd
      have hfm := List.mem_of_find?_eq_some hd
      simp only [Option.toList_some] at h
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hf
      obtain ⟨⟨⟨⟨hfa, hfb, hfc⟩, hab⟩, hac⟩, hbc⟩ := hf
      simp only [Data.isBasis, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not,
        Bool.not_true] at hab hac hbc
      exact ⟨f, h.symm, List.mem_range.mp hfm, fun e => hfa e.symm, fun e => hfb e.symm,
        fun e => hfc e.symm, hab.2, hac.2, hbc.2⟩

/-- The point whose free coordinates are read off the vectors `w`. -/
def pointOf (M : Data) (frame : List Nat) (w : ℕ → Fin 3 → K) (n : ℕ) : Fin n → K :=
  fun i => w ((free M frame).getD (i.val / 3) 0) ⟨i.val % 3, Nat.mod_lt _ (by norm_num)⟩

theorem vec3_ext (v : Fin 3 → K) : ![v 0, v 1, v 2] = v := by
  funext i; fin_cases i <;> rfl

theorem pointOf_var (M : Data) (frame : List Nat) (w : ℕ → Fin 3 → K) (n k m : ℕ) (hm : m < 3)
    (hk : k < (free M frame).length) (h : 3 * k + m < n) :
    pointOf M frame w n ⟨3 * k + m, h⟩ = w ((free M frame)[k]) ⟨m, hm⟩ := by
  have h1 : (3 * k + m) / 3 = k := by omega
  have h2 : (3 * k + m) % 3 = m := by omega
  simp only [pointOf]
  congr 1
  · rw [h1, List.getD_eq_getElem _ _ hk]
  · exact Fin.ext (by simpa using h2)

/-- At the point read off `w`, a free element's column is `w` itself. -/
theorem col_free {M : Data} {frame : List Nat} (w : ℕ → Fin 3 → K) {n : ℕ} (hn : 3 * (free M frame).length ≤ n)
    {j : ℕ} (hj : j < M.n) (hnot : j ∉ frame) :
    colK n (pointOf M frame w n) (M.columns frame j) = w j := by
  have hmem : j ∈ free M frame := List.mem_filter.mpr ⟨List.mem_range.mpr hj, by simpa using hnot⟩
  have hk : (free M frame).idxOf j < (free M frame).length := List.idxOf_lt_length_of_mem hmem
  have hnone : frame.idxOf? j = none := by simpa [List.idxOf?_eq_none_iff] using hnot
  have hcol : M.columns frame j = (.var (3 * (free M frame).idxOf j), .var (3 * (free M frame).idxOf j + 1),
      .var (3 * (free M frame).idxOf j + 2)) := by
    simp only [Data.columns, hnone]; rfl
  have hj' : (free M frame)[(free M frame).idxOf j] = j := List.getElem_idxOf _
  have e0 : entryK n (pointOf M frame w n) (.var (3 * (free M frame).idxOf j)) = w j 0 := by
    simp only [entryK]
    rw [dite_cond_eq_true (eq_true (by omega))]
    have := pointOf_var M frame w n _ 0 (by norm_num) hk (by omega)
    simp only [Nat.add_zero] at this
    rw [this, hj']; rfl
  have e1 : entryK n (pointOf M frame w n) (.var (3 * (free M frame).idxOf j + 1)) = w j 1 := by
    simp only [entryK]
    rw [dite_cond_eq_true (eq_true (by omega)), pointOf_var M frame w _ _ 1 (by norm_num) hk, hj']; rfl
  have e2 : entryK n (pointOf M frame w n) (.var (3 * (free M frame).idxOf j + 2)) = w j 2 := by
    simp only [entryK]
    rw [dite_cond_eq_true (eq_true (by omega)), pointOf_var M frame w _ _ 2 (by norm_num) hk, hj']; rfl
  rw [hcol, ← vec3_ext (w j)]
  simp only [colK, e0, e1, e2]

/-- Where every column is `w` and `w` realizes the matroid, the point lies on the framed system. -/
theorem locus_of_cols {M : Data} {vars : List String} {eqs guards : List Sparse}
    (h : M.system = some (vars, eqs, guards)) {frame : List Nat} (hf : M.frame = some frame)
    {w : ℕ → Fin 3 → K} (hw : Realizes M w) (x : Fin vars.length → K)
    (hcols : ∀ j < M.n, colK vars.length x (M.columns frame j) = w j) :
    LocusE K ⟨vars, eqs, guards, .nonempty⟩ x := by
  obtain ⟨frame', hf', -, hok, heqs, hguards⟩ := system_spec h
  rw [hf] at hf'
  cases hf'
  have hdet : ∀ t ∈ triples M.n, valueE K vars.length (ofHex (M.det frame vars.length t)) x =
      det3 (w t.1) (w t.2.1) (w t.2.2) := by
    intro t ht
    obtain ⟨a, b, c⟩ := t
    obtain ⟨hab, hbc, hc⟩ := mem_triples.mp ht
    obtain ⟨hrt, hint, -, -⟩ := frameOK_at hok ht
    rw [valueE_det (K := K) _ hrt hint, det_eval, hcols a (by omega), hcols b (by omega), hcols c hc]
  refine ⟨fun e he => ?_, fun g hg => ?_⟩
  · rw [heqs] at he
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
    obtain ⟨ht, hsel⟩ := List.mem_filter.mp ht
    simp only [Bool.and_eq_true] at hsel
    rw [hdet t ht]
    exact (hw t ht).mpr hsel.1
  · rw [hguards] at hg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    obtain ⟨ht, hsel⟩ := List.mem_filter.mp ht
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hsel
    rw [hdet t ht]
    intro h0
    have := (hw t ht).mp h0
    rw [hsel.1] at this
    exact Bool.noConfusion this

end GPBinding.Matroid


