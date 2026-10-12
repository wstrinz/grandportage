import GPBinding.Real.OrderedSound
import GPProfile.Real.CaseTree

/-!
Soundness of the refutation case-tree checker (`GPProfile.Real.caseTreeCheck`, G-6): an accepted
tree leaves its real system without points in every field isomorphic to ℝ.

- **P1 in GP's coordinate form** (`rhombus_relation`). Four unit edges `ab, bc, cd, da` with
  `|a − c|² ≠ 0` and `|b − d|² ≠ 0` give `a − b + c − d = 0`. With `u = c − a`, `z = b − d` and
  `w = b + d − a − c`, the edge equations give `z·u = w·u = z·w = 0` (after cancelling 2), and the
  planar Lagrange identity `|u|²(z·w) = (z·u)(w·u) + (z×u)(w×u)` leaves `(z×u)(w×u) = 0`. If
  `z×u = 0` then `|u|²·z = 0`, so `z = 0`, against `|b − d|² ≠ 0`; otherwise `w×u = 0`, so
  `|u|²·w = 0` and `w = 0`. The argument is field-generic (characteristic ≠ 2) because the
  guards are the squared norms, which over ℂ is stronger than distinctness; the checker still
  admits trees at ℝ scope only.
- **L1a leaves** (`collisionOk_real`): every cited fact holds at a point, P1 makes every weighted
  rhombus relation vanish, so `p_u − p_v` vanishes in both coordinates and the cited guard
  `|p_u − p_v|²` is zero.
- **L1b steps** (`unitOk_real`): the weighted relations vanish as in L1a, so
  `p_u − p_v = s·(p_a − p_b)` with `s² = 1`, and the cited edge gives `|p_u − p_v|² = |p_a − p_b|² = 1`:
  the derived equation holds at every real point of the branch, which may then be refuted with it.
- **Ordered leaves** by `Ordered.orderedCheck_real`.
- **Splits**: every real point satisfies `p = 0` or `p ≠ 0`, and has one of the three signs.
-/

noncomputable section

namespace GPBinding.Real.CaseTree
open GPProfile GPProfile.Real GPBinding.Admission GPBinding.Real.Ordered MvPolynomial HexMvPolyMathlib

/-! ## P1: the rhombus relation in coordinates -/

/-- **P1** (rhombus lemma, coordinate form): in any field of characteristic ≠ 2, a 4-cycle of unit
edges whose diagonals have nonzero squared length satisfies `a − b + c − d = 0`. -/
theorem rhombus_relation {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {a1 a2 b1 b2 c1 c2 d1 d2 : K}
    (hab : (a1 - b1) * (a1 - b1) + (a2 - b2) * (a2 - b2) = 1)
    (hbc : (b1 - c1) * (b1 - c1) + (b2 - c2) * (b2 - c2) = 1)
    (hcd : (c1 - d1) * (c1 - d1) + (c2 - d2) * (c2 - d2) = 1)
    (hda : (d1 - a1) * (d1 - a1) + (d2 - a2) * (d2 - a2) = 1)
    (hac : (a1 - c1) * (a1 - c1) + (a2 - c2) * (a2 - c2) ≠ 0)
    (hbd : (b1 - d1) * (b1 - d1) + (b2 - d2) * (b2 - d2) ≠ 0) :
    a1 - b1 + c1 - d1 = 0 ∧ a2 - b2 + c2 - d2 = 0 := by
  -- u = c − a, z = b − d, w = b + d − a − c.
  have half : ∀ t : K, 2 * t = 0 → t = 0 := fun t ht =>
    (mul_eq_zero.mp ht).resolve_left h2
  have zu : (b1 - d1) * (c1 - a1) + (b2 - d2) * (c2 - a2) = 0 :=
    half _ (by linear_combination hab - hbc - hda + hcd)
  have wu : (b1 + d1 - a1 - c1) * (c1 - a1) + (b2 + d2 - a2 - c2) * (c2 - a2) = 0 :=
    half _ (by linear_combination hab - hbc + hda - hcd)
  have zw : (b1 - d1) * (b1 + d1 - a1 - c1) + (b2 - d2) * (b2 + d2 - a2 - c2) = 0 :=
    half _ (by linear_combination hab + hbc - hda - hcd)
  -- The planar Lagrange identity |u|²(z·w) = (z·u)(w·u) + (z×u)(w×u).
  have hQP : ((b2 - d2) * (c1 - a1) - (b1 - d1) * (c2 - a2)) *
      ((b2 + d2 - a2 - c2) * (c1 - a1) - (b1 + d1 - a1 - c1) * (c2 - a2)) = 0 := by
    linear_combination ((a1 - c1) * (a1 - c1) + (a2 - c2) * (a2 - c2)) * zw -
      ((b1 + d1 - a1 - c1) * (c1 - a1) + (b2 + d2 - a2 - c2) * (c2 - a2)) * zu
  rcases mul_eq_zero.mp hQP with hq | hp
  · exfalso
    have z1 : ((a1 - c1) * (a1 - c1) + (a2 - c2) * (a2 - c2)) * (b1 - d1) = 0 := by
      linear_combination (c1 - a1) * zu - (c2 - a2) * hq
    have z2 : ((a1 - c1) * (a1 - c1) + (a2 - c2) * (a2 - c2)) * (b2 - d2) = 0 := by
      linear_combination (c2 - a2) * zu + (c1 - a1) * hq
    have e1 := (mul_eq_zero.mp z1).resolve_left hac
    have e2 := (mul_eq_zero.mp z2).resolve_left hac
    exact hbd (by rw [e1, e2]; ring)
  · have w1 : ((a1 - c1) * (a1 - c1) + (a2 - c2) * (a2 - c2)) * (b1 + d1 - a1 - c1) = 0 := by
      linear_combination (c1 - a1) * wu - (c2 - a2) * hp
    have w2 : ((a1 - c1) * (a1 - c1) + (a2 - c2) * (a2 - c2)) * (b2 + d2 - a2 - c2) = 0 := by
      linear_combination (c2 - a2) * wu + (c1 - a1) * hp
    have e1 := (mul_eq_zero.mp w1).resolve_left hac
    have e2 := (mul_eq_zero.mp w2).resolve_left hac
    exact ⟨by linear_combination -e1, by linear_combination -e2⟩

/-- The control: without the guard on the diagonal `a, c`, P1 fails over ℝ (a = c = 0, b = (1, 0),
d = (0, 1): four unit edges, `|b − d|² = 2`, and `a − b + c − d = (−1, −1)`). The checker
therefore refuses any rhombus whose diagonals are not both cited guards. -/
theorem rhombus_relation_needs_diagonal_guard : ¬ ∀ a1 a2 b1 b2 c1 c2 d1 d2 : ℝ,
    (a1 - b1) * (a1 - b1) + (a2 - b2) * (a2 - b2) = 1 →
    (b1 - c1) * (b1 - c1) + (b2 - c2) * (b2 - c2) = 1 →
    (c1 - d1) * (c1 - d1) + (c2 - d2) * (c2 - d2) = 1 →
    (d1 - a1) * (d1 - a1) + (d2 - a2) * (d2 - a2) = 1 →
    (b1 - d1) * (b1 - d1) + (b2 - d2) * (b2 - d2) ≠ 0 → a1 - b1 + c1 - d1 = 0 := by
  intro h
  have := h 0 0 1 0 0 0 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

/-! ## Evaluating the polynomials L1a builds -/

section
variable {n : ℕ} (x : Fin n → ℝ)

/-- Variable `i`'s value (`0` out of range, as `varP`). -/
def xv (i : ℕ) : ℝ := if h : i < n then x ⟨i, h⟩ else 0

def px (pts : List (ℕ × ℕ)) (i : ℕ) : ℝ := xv x (pts.getD i (0, 0)).1
def py (pts : List (ℕ × ℕ)) (i : ℕ) : ℝ := xv x (pts.getD i (0, 0)).2

theorem ev_sub (P Q : GPProfile.P n Rat) : ev x (P - Q) = ev x P - ev x Q := by
  simp [ev, toMvPolynomial_sub]

theorem ev_varP (i : ℕ) : ev x (varP n i) = xv x i := by
  unfold varP xv
  split_ifs with h
  · simp [ev, evalQ, toMvPolynomial_X]
  · exact ev_zero x

theorem ev_ptX (pts : List (ℕ × ℕ)) (i : ℕ) : ev x (ptX n pts i) = px x pts i := ev_varP x _
theorem ev_ptY (pts : List (ℕ × ℕ)) (i : ℕ) : ev x (ptY n pts i) = py x pts i := ev_varP x _

theorem ev_sqDist (pts : List (ℕ × ℕ)) (i j : ℕ) : ev x (sqDist n pts i j) =
    (px x pts i - px x pts j) * (px x pts i - px x pts j) +
      (py x pts i - py x pts j) * (py x pts i - py x pts j) := by
  simp only [sqDist, ev_add, ev_mul, ev_sub, ev_ptX, ev_ptY]

theorem ev_edgeP (pts : List (ℕ × ℕ)) (i j : ℕ) :
    ev x (edgeP n pts i j) = ev x (sqDist n pts i j) - 1 := by
  rw [edgeP, ev_sub, ev_C, Rat.cast_one]

theorem ev_combo (rel : Rhombus → GPProfile.P n Rat) (ts : List (Rat × Rhombus))
    (h : ∀ t ∈ ts, ev x (rel t.2) = 0) : ev x (combo n rel ts) = 0 := by
  rw [combo, ev_sum, List.map_map]
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
  simp only [Function.comp_apply, ev_mul, ev_C, h t ht, mul_zero]

end

/-! ## Citations -/

theorem cites_mem {n : ℕ} {ps : List Sparse} {k : ℕ} {Q : GPProfile.P n Rat} (h : cites n ps k Q = true) :
    ∃ p ∈ ps, toHexQ n p = some Q := by
  unfold cites at h
  split at h
  · rename_i p hp
    exact ⟨p, List.mem_of_getElem? hp, beq_iff_eq.mp h⟩
  · cases h

theorem cites_eq {r : RealSys} {x : Fin r.vars.length → ℝ} (hx : RealLocus r x) {k : ℕ}
    {Q : GPProfile.P r.vars.length Rat} (h : cites r.vars.length r.eqs k Q = true) : ev x Q = 0 := by
  obtain ⟨p, hp, hpQ⟩ := cites_mem h
  rw [ev_meaning x hpQ]
  exact hx.1 p hp

theorem cites_guard {r : RealSys} {x : Fin r.vars.length → ℝ} (hx : RealLocus r x) {k : ℕ}
    {Q : GPProfile.P r.vars.length Rat} (h : cites r.vars.length r.guards k Q = true) : ev x Q ≠ 0 := by
  obtain ⟨p, hp, hpQ⟩ := cites_mem h
  rw [ev_meaning x hpQ]
  exact hx.2.1 p hp

/-! ## L1a leaves -/

/-- An admitted rhombus instance's relation vanishes at every real point of the branch. -/
theorem rhombusOk_rel {pts : List (ℕ × ℕ)} {r : RealSys} {h : Rhombus}
    (ok : rhombusOk r.vars.length pts r h = true) {x : Fin r.vars.length → ℝ} (hx : RealLocus r x) :
    ev x (relX r.vars.length pts h) = 0 ∧ ev x (relY r.vars.length pts h) = 0 := by
  simp only [rhombusOk, Bool.and_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨hab, hbc⟩, hcd⟩, hda⟩, hac⟩, hbd⟩ := ok
  have edge : ∀ {k i j}, cites r.vars.length r.eqs k (edgeP r.vars.length pts i j) = true →
      ev x (sqDist r.vars.length pts i j) = 1 := fun hc => by
    have := cites_eq hx hc
    rw [ev_edgeP] at this
    linarith
  have := rhombus_relation (two_ne_zero) (by rw [← ev_sqDist]; exact edge hab)
    (by rw [← ev_sqDist]; exact edge hbc) (by rw [← ev_sqDist]; exact edge hcd)
    (by rw [← ev_sqDist]; exact edge hda) (by rw [← ev_sqDist]; exact cites_guard hx hac)
    (by rw [← ev_sqDist]; exact cites_guard hx hbd)
  simp only [relX, relY, ev_add, ev_sub, ev_ptX, ev_ptY]
  exact this

/-- **L1a soundness**: an accepted collision leaf has no real point. -/
theorem collisionOk_real {pts : List (ℕ × ℕ)} {r : RealSys} {c : Collision}
    (h : collisionOk r.vars.length pts r c = true) (x : Fin r.vars.length → ℝ) (hx : RealLocus r x) :
    False := by
  simp only [collisionOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hall, hX⟩, hY⟩, hg⟩ := h
  have rel := fun t ht => rhombusOk_rel (hall t ht) hx
  have sx := ev_combo x _ c.rhombi fun t ht => (rel t ht).1
  have sy := ev_combo x _ c.rhombi fun t ht => (rel t ht).2
  rw [hX, ev_sub, ev_ptX, ev_ptX] at sx
  rw [hY, ev_sub, ev_ptY, ev_ptY] at sy
  apply cites_guard hx hg
  rw [ev_sqDist, sx, sy]
  ring

/-! ## L1b steps -/

/-- **L1b soundness**: the equation an accepted unit step derives holds at every real point of its
branch. -/
theorem unitOk_real {pts : List (ℕ × ℕ)} {r : RealSys} {d : UnitStep}
    (h : unitOk r.vars.length pts r d = true) {x : Fin r.vars.length → ℝ} (hx : RealLocus r x) :
    value r.vars.length (unitEq r.vars.length pts d) x = 0 := by
  simp only [unitOk, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hall, hs⟩, hX⟩, hY⟩, he⟩, hrt⟩ := h
  have rel := fun t ht => rhombusOk_rel (hall t ht) hx
  have sx := ev_combo x _ d.rhombi fun t ht => (rel t ht).1
  have sy := ev_combo x _ d.rhombi fun t ht => (rel t ht).2
  rw [hX] at sx
  rw [hY] at sy
  simp only [unitRel, ev_sub, ev_mul, ev_C, ev_ptX, ev_ptY] at sx sy
  have hab := cites_eq hx he
  rw [ev_edgeP, ev_sqDist] at hab
  rw [← ev_meaning x hrt, ev_edgeP, ev_sqDist]
  have hs2 : (((d.sign : ℤ) : ℚ) : ℝ) * (((d.sign : ℤ) : ℚ) : ℝ) = 1 := by
    rcases hs with hs | hs <;> simp [hs]
  linear_combination (px x pts d.u - px x pts d.v +
      (((d.sign : ℤ) : ℚ) : ℝ) * (px x pts d.a - px x pts d.b)) * sx +
    (py x pts d.u - py x pts d.v + (((d.sign : ℤ) : ℚ) : ℝ) * (py x pts d.a - py x pts d.b)) * sy +
    (((d.sign : ℤ) : ℚ) : ℝ) * (((d.sign : ℤ) : ℚ) : ℝ) * hab + hs2

/-! ## Splits -/

theorem locus_addEq {K : Type*} [Field K] {r : RealSys} {x : Fin r.vars.length → K} (hx : RealLocus r x)
    {p : Sparse} (hp : value _ p x = 0) : RealLocus (r.addEq p) x := by
  refine ⟨fun e he => ?_, hx.2.1, hx.2.2⟩
  rcases List.mem_append.mp he with he | he
  · exact hx.1 e he
  · rw [List.mem_singleton.mp he]; exact hp

theorem locus_addGuard {K : Type*} [Field K] {r : RealSys} {x : Fin r.vars.length → K}
    (hx : RealLocus r x) {p : Sparse} (hp : value _ p x ≠ 0) : RealLocus (r.addGuard p) x := by
  refine ⟨hx.1, fun g hg => ?_, hx.2.2⟩
  rcases List.mem_append.mp hg with hg | hg
  · exact hx.2.1 g hg
  · rw [List.mem_singleton.mp hg]; exact hp

theorem locus_addSign {K : Type*} [Field K] {r : RealSys} {x : Fin r.vars.length → K}
    (hx : RealLocus r x) {p : Sparse} {σ : ℤ} (hp : signSq (value _ p x) = σ) :
    RealLocus (r.addSign p σ) x := by
  refine ⟨hx.1, hx.2.1, fun q hq => ?_⟩
  rcases List.mem_append.mp hq with hq | hq
  · exact hx.2.2 q hq
  · rw [List.mem_singleton.mp hq]; exact hp

theorem signSq_cases {K : Type*} [Field K] (y : K) : signSq y = -1 ∨ signSq y = 0 ∨ signSq y = 1 := by
  unfold signSq
  split_ifs <;> simp

/-! ## Soundness -/

/-- Every accepted subtree refutes its branch system over ℝ. -/
theorem caseTreeGo_real (pts : List (ℕ × ℕ)) :
    ∀ (t : CaseTree) (r : RealSys), caseTreeGo pts r t = true →
      ∀ x : Fin r.vars.length → ℝ, ¬ RealLocus r x := by
  intro t
  induction t with
  | collision c => intro r h x hx; exact collisionOk_real h x hx
  | unit d t iht =>
    intro r h x hx
    simp only [caseTreeGo, Bool.and_eq_true] at h
    exact iht _ h.2 x (locus_addEq hx (unitOk_real h.1 hx))
  | ordered c => intro r h x hx; exact orderedCheck_real h x hx
  | zero p t f iht ihf =>
    intro r h x hx
    simp only [caseTreeGo, Bool.and_eq_true] at h
    by_cases hp : value _ p x = 0
    · exact iht _ h.1 x (locus_addEq hx hp)
    · exact ihf _ h.2 x (locus_addGuard hx hp)
  | sign p n z q ihn ihz ihq =>
    intro r h x hx
    simp only [caseTreeGo, Bool.and_eq_true] at h
    rcases signSq_cases (value _ p x) with hs | hs | hs
    · exact ihn _ h.1.1 x (locus_addSign hx hs)
    · exact ihz _ h.1.2 x (locus_addSign hx hs)
    · exact ihq _ h.2 x (locus_addSign hx hs)

/-- An accepted case tree leaves its system without real points. -/
theorem caseTreeCheck_real {r : RealSys} {c : CaseTreeCert} (h : caseTreeCheck r c = true)
    (x : Fin r.vars.length → ℝ) : ¬ RealLocus r x := by
  simp only [caseTreeCheck, Bool.and_eq_true] at h
  exact caseTreeGo_real c.points c.tree r h.2 x

theorem caseTreeCheck_holds {r : RealSys} {c : CaseTreeCert} (h : caseTreeCheck r c = true)
    {K : Type*} [Field K] (e : K ≃+* ℝ) : RealHolds K r .empty := by
  have := isSemireal_of_equiv_real e
  intro x hx
  exact caseTreeCheck_real h _ ((RootCover.realLocus_equiv e r x).mp hx)

/-- **G-6 soundness.** An accepted case tree makes its system empty in every field isomorphic to
ℝ. -/
theorem caseTreeCheck_sound {r : RealSys} {c : CaseTreeCert} (h : caseTreeCheck r c = true) :
    ∀ (K : Type*) [Field K], Nonempty (K ≃+* ℝ) → RealHolds K r .empty :=
  fun _ _ hK => caseTreeCheck_holds h (Classical.choice hK)

end GPBinding.Real.CaseTree

end
