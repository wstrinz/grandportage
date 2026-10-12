import GPProfile.Real.NumberField
import GPBinding.Real.AlgPointSound
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
Soundness of the number-field point checker (`GPProfile.Real.nfCheck`, C4 and C5): an accepted
certificate proves `NFHolds`, the meaning of the statement in every field.

- **Irreducibility.** The rational-root test: a root `x ∈ ℚ` of the integer polynomial `m` is
  `num/den` with `num ∣ m₀` and `den ∣ lc m` (Mathlib's rational root theorem), so it is one of the
  enumerated `±a/b`, none of which is a root; a polynomial of degree 2 or 3 with no root is
  irreducible.
- **Points.** Every operation on elements of `R = K[Z]/(r)` respects evaluation at `(θ, z)` with
  `m(θ) = 0` and `r(θ, z) = 0` (`evR_*`): reduction modulo `m` by `fv_mod`, reduction modulo `r`
  subtracts multiples of `Z^k · r`. So an equation that reduces to 0 vanishes at the point, and a
  guard `g` with `u · g ≡ 1` has `u(θ, z) · g(θ, z) = 1`.
-/

noncomputable section

namespace GPBinding.Real.NumberField
open GPProfile GPProfile.Real GPProfile.Real.NF GPProfile.Real.RAlg HexPolyMathlib Polynomial
open GPBinding.Admission GPBinding.Real.AlgPoint

/-! ## Meaning -/

/-- The value of an element of `R` at `(θ, z)`: `Σ aⱼ(θ) zʲ`. -/
def evR {F : Type*} [Field F] [CharZero F] (θ z : F) : List D → F
  | [] => 0
  | a :: f => fv a θ + z * evR θ z f

/-- The meaning of a number-field point statement in a field `L`: `m` is irreducible over ℚ and,
when `L` has characteristic 0, for every root `θ` of `m` and every root `z` of `r(θ, Z)` in `L`,
the coordinates at `(θ, z)` lie on the locus. -/
def NFHolds (L : Type*) [Field L] (p : NFPoint) : Prop :=
  Irreducible (toPolynomial (ofU p.m)) ∧
  ∀ [CharZero L], ∀ θ z : L, fv (ofU p.m) θ = 0 → evR θ z (p.r.map ofU) = 0 →
    let y : Fin p.vars.length → L := fun i => evR θ z ((p.coords.getD i []).map ofU)
    (∀ e ∈ p.eqs, value _ e y = 0) ∧ (∀ g ∈ p.guards, value _ g y ≠ 0)

/-! ## Irreducibility -/

theorem mem_divisorsN {n d : ℕ} (hn : n ≠ 0) (hd : d ∣ n) : d ∈ divisorsN n := by
  have hd0 : d ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd hd)
  simp only [divisorsN, List.mem_filter, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq]
  exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd), hd0, Nat.mod_eq_zero_of_dvd hd⟩

/-- `m` with its (integer) coefficients as an integer polynomial. -/
def intPoly (m : D) : ℤ[X] := ∑ i ∈ Finset.range m.size, monomial i (m.coeff i).num

theorem intPoly_coeff (m : D) (i : ℕ) : (intPoly m).coeff i = (m.coeff i).num := by
  rw [intPoly, finset_sum_coeff]
  simp only [coeff_monomial]
  by_cases hi : i < m.size
  · rw [Finset.sum_eq_single i (fun j _ hj => if_neg hj) (fun h => absurd (Finset.mem_range.mpr hi) h),
      if_pos rfl]
  · rw [Finset.sum_eq_zero fun j hj => if_neg (by rintro rfl; exact hi (Finset.mem_range.mp hj)),
      Hex.DensePoly.coeff_eq_zero_of_size_le m (by omega)]
    rfl

theorem intPoly_map {m : D} (hden : ∀ i, (m.coeff i).den = 1) :
    (intPoly m).map (Int.castRingHom ℚ) = toPolynomial m := by
  ext i
  rw [coeff_map, intPoly_coeff, coeff_toPolynomial, eq_intCast]
  exact Rat.coe_int_num_of_den_eq_one (hden i)

theorem int_div_cases (a b : ℤ) : ((a : ℚ) / b = (a.natAbs : ℚ) / b.natAbs) ∨
    ((a : ℚ) / b = -((a.natAbs : ℚ) / b.natAbs)) := by
  obtain ⟨na, rfl | rfl⟩ := Int.eq_nat_or_neg a <;> obtain ⟨nb, rfl | rfl⟩ := Int.eq_nat_or_neg b <;>
    simp [neg_div, div_neg]

/-- **The rational-root test is sound.** -/
theorem rrtOk_irreducible {m : D} (h : rrtOk m = true) : Irreducible (toPolynomial m) := by
  simp only [rrtOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hsize, hden⟩, h0⟩, -⟩, -⟩, hroots⟩ := h
  have hpos : 0 < m.size := by omega
  have hden' : ∀ i, (m.coeff i).den = 1 := fun i => by
    by_cases hi : i < m.size
    · exact hden i hi
    · rw [Hex.DensePoly.coeff_eq_zero_of_size_le m (by omega)]; rfl
  have hdeg : (toPolynomial m).natDegree = m.size - 1 := by
    rw [natDegree_toPolynomial, Hex.DensePoly.natDegree_eq_size_sub_one]
  have hlc : m.leadingCoeff ≠ 0 := by
    rw [Hex.DensePoly.leadingCoeff_eq_coeff_last m hpos]
    exact Hex.DensePoly.coeff_last_ne_zero_of_pos_size m hpos
  apply irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg, Finset.mem_Icc]; omega)
  intro x hx
  have hmap := intPoly_map hden'
  have haeval : aeval x (intPoly m) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, algebraMap_int_eq, hmap]; exact hx
  have hdegZ : (intPoly m).natDegree = m.size - 1 := by
    rw [← natDegree_map_eq_of_injective (Int.castRingHom ℚ).injective_int, hmap, hdeg]
  have hnum := num_dvd_of_is_root (A := ℤ) haeval
  have hdenom := den_dvd_of_is_root (A := ℤ) haeval
  rw [intPoly_coeff] at hnum
  rw [leadingCoeff, hdegZ, intPoly_coeff, ← Hex.DensePoly.leadingCoeff_eq_coeff_last m hpos] at hdenom
  have hc0 : (m.coeff 0).num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (mt Rat.num_eq_zero.mp h0)
  have hcn : m.leadingCoeff.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (mt Rat.num_eq_zero.mp hlc)
  have ha := mem_divisorsN hc0 (Int.natAbs_dvd_natAbs.mpr hnum)
  have hb := mem_divisorsN hcn (Int.natAbs_dvd_natAbs.mpr hdenom)
  obtain ⟨hp, hn⟩ := hroots _ ha _ hb
  have hx' : x = ((IsFractionRing.num ℤ x : ℤ) : ℚ) / ((IsFractionRing.den ℤ x : ℤ) : ℚ) :=
    (IsFractionRing.mk'_num_den' ℤ x).symm
  have hev : (toPolynomial m).eval x = 0 := hx
  rw [eval_toPolynomial] at hev
  rcases int_div_cases (IsFractionRing.num ℤ x) (IsFractionRing.den ℤ x) with hc | hc <;>
    rw [hc] at hx' <;> rw [hx'] at hev
  · exact hp hev
  · exact hn hev

/-! ## Arithmetic in `R` respects evaluation -/

section Eval
variable {F : Type*} [Field F] [CharZero F] {θ z : F}

@[simp] theorem evR_nil : evR θ z [] = 0 := rfl
@[simp] theorem evR_cons (a : D) (f : List D) : evR θ z (a :: f) = fv a θ + z * evR θ z f := rfl

theorem fv_neg (p : D) : fv (-p) θ = -fv p θ := by simp [fv, toPolynomial_neg]

theorem evR_addR : ∀ f g : List D, evR θ z (addR f g) = evR θ z f + evR θ z g
  | [], g => by simp [addR]
  | a :: f, [] => by simp [addR]
  | a :: f, b :: g => by simp only [addR, evR_cons, fv_add, evR_addR f g]; ring

theorem evR_smulR {m : D} (hm : fv m θ = 0) (c : D) :
    ∀ f : List D, evR θ z (smulR m c f) = fv c θ * evR θ z f
  | [] => by simp [smulR]
  | a :: f => by simp only [smulR, evR_cons, fv_mod hm, fv_mul, evR_smulR hm c f]; ring

theorem evR_negR : ∀ f : List D, evR θ z (negR f) = -evR θ z f
  | [] => by simp [negR]
  | a :: f => by simp only [negR, evR_cons, fv_neg, evR_negR f]; ring

theorem evR_mulRaw {m : D} (hm : fv m θ = 0) :
    ∀ f g : List D, evR θ z (mulRaw m f g) = evR θ z f * evR θ z g
  | [], g => by simp [mulRaw]
  | a :: f, g => by
    simp only [mulRaw, evR_addR, evR_smulR hm, evR_cons, fv_zero, evR_mulRaw hm f g]; ring

theorem evR_shiftN : ∀ (k : ℕ) (f : List D), evR θ z (shiftN k f) = z ^ k * evR θ z f
  | 0, f => by simp [shiftN]
  | k + 1, f => by simp only [shiftN, evR_cons, fv_zero, evR_shiftN k f]; ring

theorem evR_trimR : ∀ f : List D, evR θ z (trimR f) = evR θ z f
  | [] => rfl
  | a :: f => by
    have ih := evR_trimR f
    unfold trimR
    split
    · rename_i h0
      rw [h0, evR_nil] at ih
      split
      · rename_i ha
        rw [evR_nil, evR_cons, eq_zero_of_isZero ha, fv_zero, ← ih]; ring
      · rw [evR_cons, evR_cons, evR_nil, ← ih]
    · rename_i b t h0
      rw [evR_cons a f, ← ih, h0]
      simp

theorem evR_redStep {m li : D} {r : List D} (hm : fv m θ = 0) (hr : evR θ z r = 0) (l : List D) :
    evR θ z (redStep m li r l) = evR θ z l := by
  rw [redStep, evR_trimR, evR_addR, evR_negR, evR_smulR hm, evR_shiftN, hr]; ring

theorem evR_redR {m li : D} {r : List D} (hm : fv m θ = 0) (hr : evR θ z r = 0) :
    ∀ (n : ℕ) (l : List D), evR θ z (redR m li r n l) = evR θ z l
  | 0, l => rfl
  | n + 1, l => by
    unfold redR
    split
    · rfl
    · rw [evR_redR hm hr n, evR_redStep hm hr]

theorem evR_mulR {m li : D} {r : List D} (hm : fv m θ = 0) (hr : evR θ z r = 0) (f g : List D) :
    evR θ z (mulR m li r f g) = evR θ z f * evR θ z g := by
  rw [mulR, evR_redR hm hr, evR_trimR, evR_mulRaw hm]

theorem evR_one : evR θ z [(1 : D)] = 1 := by simp

theorem evR_powR {m li : D} {r : List D} (hm : fv m θ = 0) (hr : evR θ z r = 0) (x : List D) :
    ∀ k, evR θ z (powR m li r x k) = evR θ z x ^ k
  | 0 => by simp [powR]
  | k + 1 => by rw [powR, evR_mulR hm hr, evR_powR hm hr x k, pow_succ]

/-- A table of powers of `x`. -/
def TableOk (θ z : F) (tab : List (List D)) (x : List D) : Prop :=
  ∀ j p, tab[j]? = some p → evR θ z p = evR θ z x ^ j

theorem powTable_length {m li : D} {r x : List D} : ∀ k, (powTable m li r x k).length = k + 1
  | 0 => rfl
  | k + 1 => by simp [powTable, powTable_length k]

theorem powTable_ok {m li : D} {r : List D} (hm : fv m θ = 0) (hr : evR θ z r = 0) (x : List D) :
    ∀ k, TableOk θ z (powTable m li r x k) x
  | 0 => by
    intro j p hp
    cases j with
    | zero => simp [powTable] at hp; subst hp; simp
    | succ j => simp [powTable] at hp
  | k + 1 => by
    intro j p hp
    have ih := powTable_ok (li := li) hm hr x k
    have hlen := powTable_length (m := m) (li := li) (r := r) (x := x) k
    simp only [powTable] at hp
    rcases Nat.lt_or_ge j (k + 1) with hj | hj
    · rw [List.getElem?_append_left (by omega)] at hp
      exact ih j p hp
    · rw [List.getElem?_append_right (by omega)] at hp
      have hj' : j = k + 1 := by
        by_contra hne
        rw [List.getElem?_eq_none (by simp; omega)] at hp
        cases hp
      subst hj'
      simp only [hlen, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hp
      subst hp
      have hlast : (powTable m li r x k).getLastD [1] = (powTable m li r x k)[k]'(by omega) := by
        rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
        simp only [hlen, Nat.add_sub_cancel]
        rw [List.getElem?_eq_getElem (by omega)]
        rfl
      rw [evR_mulR hm hr, hlast, ih k _ (List.getElem?_eq_getElem _), pow_succ]

theorem evR_powAt {m li : D} {r : List D} (hm : fv m θ = 0) (hr : evR θ z r = 0) {tab : List (List D)}
    {x : List D} (ht : TableOk θ z tab x) (k : ℕ) : evR θ z (powAt m li r tab x k) = evR θ z x ^ k := by
  unfold powAt
  split
  · rename_i p hp; exact ht k p hp
  · exact evR_powR hm hr x k

theorem tables_ok {m li : D} {r : List D} (hm : fv m θ = 0) (hr : evR θ z r = 0) (ps : List Sparse)
    (xs : List (List D)) (i : ℕ) : TableOk θ z ((tables m li r ps xs).getD i []) (xs.getD i []) := by
  unfold tables
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hi : i < xs.length
  · rw [List.getElem?_range hi]; exact powTable_ok hm hr _ _
  · rw [List.getElem?_eq_none (by simpa using hi)]; intro j p hp; simp at hp

theorem evR_monoR {m li : D} {r : List D} (hm : fv m θ = 0) (hr : evR θ z r = 0)
    {tabs : List (List (List D))} {xs : List (List D)} (ht : ∀ i, TableOk θ z (tabs.getD i []) (xs.getD i []))
    (e : List ℕ) : ∀ k, evR θ z (monoR m li r tabs xs e k) =
      ∏ i ∈ Finset.range k, evR θ z (xs.getD i []) ^ e.getD i 0
  | 0 => by simp [monoR]
  | k + 1 => by
    rw [Finset.prod_range_succ, ← evR_monoR hm hr ht e k]
    simp only [monoR]
    split
    · rename_i h0; rw [beq_iff_eq.mp h0, pow_zero, mul_one]
    · rw [evR_mulR hm hr, evR_powAt hm hr (ht k)]

theorem isZeroR_ev {l : List D} (h : isZeroR l = true) : evR θ z l = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [isZeroR, List.all_cons, Bool.and_eq_true] at h
    rw [evR_cons, eq_zero_of_isZero h.1, fv_zero, ih h.2]; ring

theorem evR_termR {m li : D} {r : List D} (hm : fv m θ = 0) (hr : evR θ z r = 0) {n : ℕ}
    {tabs : List (List (List D))} {xs : List (List D)} (ht : ∀ i, TableOk θ z (tabs.getD i []) (xs.getD i []))
    (e : List ℕ) : evR θ z (termR m li r n tabs xs e) =
      ∏ i ∈ Finset.range n, evR θ z (xs.getD i []) ^ e.getD i 0 := by
  unfold termR
  split
  · rename_i hz
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq] at hz
    obtain ⟨i, hi, he, hx⟩ := hz
    rw [evR_nil, eq_comm]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hi) (by rw [isZeroR_ev hx, zero_pow he])
  · exact evR_monoR hm hr ht e n

theorem evR_foldl {m : D} (hm : fv m θ = 0) (T : List ℕ → List D) :
    ∀ (f : Sparse) (init : List D),
      evR θ z (f.foldl (fun acc t => addR acc (smulR m (RAlg.C t.2) (T t.1))) init) =
        evR θ z init + (f.map fun t => (t.2 : F) * evR θ z (T t.1)).sum
  | [], init => by simp
  | t :: f, init => by
    rw [List.foldl_cons, evR_foldl hm T f, evR_addR, evR_smulR hm, fv_C, List.map_cons, List.sum_cons]
    ring

/-- At a point of `R`, the reduced evaluation is the polynomial at the coordinates. -/
theorem evR_evalS {m li : D} {r : List D} (hm : fv m θ = 0) (hr : evR θ z r = 0) {n : ℕ}
    {tabs : List (List (List D))} {xs : List (List D)} (ht : ∀ i, TableOk θ z (tabs.getD i []) (xs.getD i []))
    (f : Sparse) : evR θ z (evalS m li r n tabs xs f) = Binder.valueE F n f (fun i => evR θ z (xs.getD i [])) := by
  rw [evalS, evR_trimR, evR_foldl hm, evR_nil, zero_add, Binder.valueE_eq]
  congr 1
  apply List.map_congr_left
  intro t _
  rw [evR_termR hm hr ht, Fin.prod_univ_eq_prod_range (fun i => evR θ z (xs.getD i []) ^ t.1.getD i 0)]

end Eval

/-! ## Soundness -/

/-- **Soundness.** An accepted certificate proves the statement in every field. -/
theorem nfCheck_holds {p : NFPoint} {c : NFCert} (h : nfCheck p c = true) (L : Type*) [Field L] :
    NFHolds L p := by
  simp only [nfCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hrrt, hlen⟩, harE⟩, harG⟩, hglen⟩, -⟩, hE⟩, hG⟩ := h
  refine ⟨rrtOk_irreducible hrrt, fun θ z hm hr => ?_⟩
  set d := p.data c with hd
  have hm' : fv d.m θ = 0 := hm
  have hr' : evR θ z d.r = 0 := hr
  have ht : ∀ i, TableOk θ z (d.tabs.getD i []) (d.xs.getD i []) := tables_ok hm' hr' _ _
  have hxs : ∀ i, d.xs.getD i [] = (p.coords.getD i []).map ofU := fun i => by
    simp only [hd, NFPoint.data, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases p.coords[i]? <;> rfl
  have hev : ∀ q : Sparse, sparseArity p.vars.length q = true →
      value p.vars.length q (fun i => evR θ z ((p.coords.getD i []).map ofU)) =
        evR θ z (d.eval p.vars.length q) := fun q hq => by
    rw [value_eq_valueE hq, NFData.eval, evR_evalS hm' hr' ht]
    simp only [hxs]
  refine ⟨fun e he => ?_, fun g hg => ?_⟩
  · rw [hev e (harE e he)]
    exact isZeroR_ev (hE e he)
  · obtain ⟨u, hu⟩ := exists_zip_of_mem hglen hg
    have h1 := isZeroR_ev (θ := θ) (z := z) (hG _ hu)
    rw [evR_addR, evR_mulR hm' hr', evR_cons, evR_nil, fv_C] at h1
    rw [hev g (harG g hg)]
    intro h0
    rw [h0] at h1
    norm_num at h1

end GPBinding.Real.NumberField
