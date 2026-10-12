import GPProfile.Real.RealPoint
import GPBinding.Binder.Explicit
import HexPolyMathlib
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Sign.Basic

/-!
Soundness over ℝ of the real-algebraic-point checker (3b, "ℝ first").

The proof never uses isolation or root uniqueness. `replayAll` fixes one real root `θ` of the
square-free part `s` — the rational `r` of an `.exact r` anchor, or, by the intermediate value
theorem, a root of the anchor's `t ∣ s` in `(c, d)` — and every replayed sign is a fact about
that same `θ`: `t ∣ g` gives `g(θ) = 0`; a one-signed Möbius transform (Descartes count 0)
gives no root of `g` in `(c, d)`, so `g(θ)` has the sign of `g(c)`, again by the IVT.
Reduction modulo `s` respects evaluation at a root of `s`.
-/

noncomputable section

namespace GPBinding.Real.RAlg
open GPProfile GPProfile.Real GPProfile.Real.RAlg HexPolyMathlib Polynomial Set

/-- The value at a real point of a dense rational polynomial. -/
def rv (p : D) (x : ℝ) : ℝ := (toPolynomial p).eval₂ (Rat.castHom ℝ) x

/-- The sign of a real number as an integer. -/
def rsgn (v : ℝ) : ℤ := ((SignType.sign v : SignType) : ℤ)

variable {x : ℝ}

/-! ## Evaluation -/

@[simp] theorem rv_zero : rv 0 x = 0 := by simp [rv, toPolynomial_zero]
@[simp] theorem rv_one : rv 1 x = 1 := by simp [rv, toPolynomial_one]
@[simp] theorem rv_C (c : ℚ) : rv (RAlg.C c) x = c := by simp [rv, RAlg.C, toPolynomial_C]
@[simp] theorem rv_X : rv RAlg.X x = x := by simp [rv, RAlg.X, toPolynomial_monomial]
@[simp] theorem rv_add (p q : D) : rv (p + q) x = rv p x + rv q x := by
  simp [rv, toPolynomial_add]
@[simp] theorem rv_mul (p q : D) : rv (p * q) x = rv p x * rv q x := by
  simp [rv, toPolynomial_mul, eval₂_mul]

theorem rv_powD (p : D) : ∀ k, rv (powD p k) x = rv p x ^ k
  | 0 => by simp [powD]
  | k + 1 => by simp [powD, rv_powD p k, pow_succ]

/-- Reduction modulo `s` respects evaluation at a root of `s`. -/
theorem rv_mod {p s : D} (hs : rv s x = 0) : rv (p % s) x = rv p x := by
  have h := EuclideanDomain.div_add_mod (toPolynomial p) (toPolynomial s)
  unfold rv at hs ⊢
  rw [toPolynomial_mod]
  conv_rhs => rw [← h]
  rw [eval₂_add, eval₂_mul, hs, zero_mul, zero_add]

theorem rv_ratCast (p : D) (q : ℚ) : rv p q = (evalQ p q : ℝ) := by
  unfold rv evalQ
  rw [← eval_toPolynomial]
  exact eval₂_at_apply (Rat.castHom ℝ) q

theorem rv_eq_sum (p : D) (x : ℝ) : rv p x = ∑ i ∈ Finset.range p.size, (p.coeff i : ℝ) * x ^ i :=
  eval₂_toPolynomial _ p x

theorem rv_continuous (p : D) : Continuous (rv p) := by
  have : rv p = fun x => ((toPolynomial p).map (Rat.castHom ℝ)).eval x := by
    funext x; rw [eval_map]; rfl
  rw [this]
  exact Polynomial.continuous _

theorem eq_zero_of_isZero {p : D} (h : p.isZero = true) : p = 0 :=
  (Hex.DensePoly.size_eq_zero_iff p).mp ((Hex.DensePoly.isZero_eq_true_iff p).mp h)

/-- `dvd t p` is sound at every root of `t`. -/
theorem rv_dvd {t p : D} (h : dvd t p = true) (ht : rv t x = 0) : rv p x = 0 := by
  rw [← rv_mod (p := p) ht, eq_zero_of_isZero h, rv_zero]

/-! ## Signs -/

theorem rsgn_ratCast (q : ℚ) : rsgn (q : ℝ) = sgn q := by
  unfold rsgn sgn
  rcases lt_trichotomy q 0 with h | rfl | h
  · have h' : (q : ℝ) < 0 := by exact_mod_cast h
    simp [sign_neg h', h, not_lt.mpr h.le]
  · simp
  · have h' : (0 : ℝ) < q := by exact_mod_cast h
    simp [sign_pos h', h]

theorem sgn_mul_neg {a b : ℚ} (h : sgn a * sgn b < 0) : (a < 0 ∧ 0 < b) ∨ (0 < a ∧ b < 0) := by
  unfold sgn at h
  split_ifs at h <;> first
    | omega
    | (left; exact ⟨by assumption, by assumption⟩)
    | (right; exact ⟨by assumption, by assumption⟩)

theorem rsgn_eq_zero {v : ℝ} : rsgn v = 0 ↔ v = 0 := by
  unfold rsgn
  rcases lt_trichotomy v 0 with h | rfl | h
  · simp [sign_neg h, h.ne]
  · simp
  · simp [sign_pos h, h.ne']

/-- A sign change of `t` on `[c, d]` gives a root in `(c, d)` (IVT). -/
theorem root_of_sign_change {t : D} {c d : ℚ} (hcd : c < d)
    (h : sgn (evalQ t c) * sgn (evalQ t d) < 0) : ∃ θ : ℝ, (c : ℝ) < θ ∧ θ < d ∧ rv t θ = 0 := by
  have hcd' : (c : ℝ) ≤ d := by exact_mod_cast hcd.le
  have hcont := (rv_continuous t).continuousOn (s := Icc (c : ℝ) d)
  rcases sgn_mul_neg h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h0 : (0 : ℝ) ∈ Ioo (rv t c) (rv t d) := by
      rw [rv_ratCast, rv_ratCast]; constructor <;> exact_mod_cast (by assumption)
    obtain ⟨θ, ⟨hθ1, hθ2⟩, hθ⟩ := intermediate_value_Ioo hcd' hcont h0
    exact ⟨θ, hθ1, hθ2, hθ⟩
  · have h0 : (0 : ℝ) ∈ Ioo (rv t d) (rv t c) := by
      rw [rv_ratCast, rv_ratCast]; constructor <;> exact_mod_cast (by assumption)
    obtain ⟨θ, ⟨hθ1, hθ2⟩, hθ⟩ := intermediate_value_Ioo' hcd' hcont h0
    exact ⟨θ, hθ1, hθ2, hθ⟩

/-- Without a root in `(c, d)`, `g` keeps the sign of `g(c) ≠ 0` there (IVT). -/
theorem rsgn_const {g : D} {c d θ : ℝ} (hno : ∀ y ∈ Ioo c d, rv g y ≠ 0) (hc : rv g c ≠ 0)
    (hθ : θ ∈ Ioo c d) : rsgn (rv g θ) = rsgn (rv g c) := by
  have hcθ : c ≤ θ := hθ.1.le
  have hcont := (rv_continuous g).continuousOn (s := Icc c θ)
  have hθ0 := hno θ hθ
  have sub : ∀ y ∈ Ioo c θ, y ∈ Ioo c d := fun y hy => ⟨hy.1, hy.2.trans hθ.2⟩
  unfold rsgn
  rcases lt_or_gt_of_ne hc with hc' | hc' <;> rcases lt_or_gt_of_ne hθ0 with hθ' | hθ'
  · rw [sign_neg hc', sign_neg hθ']
  · obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo hcθ hcont ⟨hc', hθ'⟩
    exact absurd hy0 (hno y (sub y hy))
  · obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo' hcθ hcont ⟨hθ', hc'⟩
    exact absurd hy0 (hno y (sub y hy))
  · rw [sign_pos hc', sign_pos hθ']

/-! ## Descartes count 0 -/

theorem mem_coeffs {p : D} {q : ℚ} : q ∈ coeffs p ↔ ∃ i < p.size, p.coeff i = q := by
  simp only [RAlg.coeffs, List.mem_map, List.mem_range]

theorem sum_pos_aux (f : ℕ → ℚ) (N : ℕ) {t : ℝ} (ht : 0 < t) (hnn : ∀ i < N, 0 ≤ f i)
    (hne : ∃ i < N, f i ≠ 0) : 0 < ∑ i ∈ Finset.range N, (f i : ℝ) * t ^ i := by
  obtain ⟨j, hj, hj0⟩ := hne
  apply Finset.sum_pos'
  · intro i hi
    have := hnn i (Finset.mem_range.mp hi)
    exact mul_nonneg (by exact_mod_cast this) (pow_nonneg ht.le _)
  · refine ⟨j, Finset.mem_range.mpr hj, mul_pos ?_ (pow_pos ht _)⟩
    exact_mod_cast lt_of_le_of_ne (hnn j hj) (Ne.symm hj0)

theorem rv_ne_zero_of_oneSigned {M : D} {t : ℝ} (ht : 0 < t)
    (hs : (∀ i < M.size, 0 ≤ M.coeff i) ∨ (∀ i < M.size, M.coeff i ≤ 0))
    (hne : ∃ i < M.size, M.coeff i ≠ 0) : rv M t ≠ 0 := by
  rw [rv_eq_sum]
  rcases hs with hs | hs
  · exact (sum_pos_aux _ _ ht hs hne).ne'
  · have h := sum_pos_aux (fun i => -M.coeff i) M.size ht (fun i hi => by simpa using hs i hi)
      (by obtain ⟨j, hj, h0⟩ := hne; exact ⟨j, hj, by simpa using h0⟩)
    simp only [Rat.cast_neg, neg_mul, Finset.sum_neg_distrib] at h
    exact (neg_pos.mp h).ne

theorem rv_mobiusGo (g L O : D) (t : ℝ) (m : ℕ) : ∀ k,
    rv (mobiusGo g L O m k) t = ∑ i ∈ Finset.range k, (g.coeff i : ℝ) * rv L t ^ i * rv O t ^ (m - i)
  | 0 => by simp [mobiusGo]
  | k + 1 => by simp [mobiusGo, rv_mobiusGo g L O t m k, Finset.sum_range_succ, rv_powD]

/-- Descartes count 0 is sound: a one-signed nonzero Möbius transform leaves `g` without a
root in `(c, d)`. -/
theorem rv_noRoot {g : D} {c d : ℚ} (h : noRootOn g c d = true) :
    ∀ y ∈ Ioo (c : ℝ) d, rv g y ≠ 0 := by
  rintro y ⟨hy1, hy2⟩ hy0
  unfold noRootOn at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true, List.any_eq_true,
    decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨hs, hne⟩ := h
  have hu : (0 : ℝ) < d - y := by linarith
  have hk : (0 : ℝ) < (d - c) / (d - y) := div_pos (by linarith) hu
  have ht : (0 : ℝ) < (y - c) / (d - y) := div_pos (by linarith) hu
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
  have key : rv (mobius g c d) t = k ^ (g.size - 1) * rv g y := by
    rw [mobius, rv_mobiusGo, hL, hO, rv_eq_sum g y, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ g.size - 1 := by have := Finset.mem_range.mp hi; omega
    rw [mul_pow, show k ^ (g.size - 1) = k ^ i * k ^ (g.size - 1 - i) by
      rw [← pow_add, Nat.add_sub_cancel' hi']]
    ring
  refine rv_ne_zero_of_oneSigned ht ?_ ?_ (by rw [key, hy0, mul_zero])
  · rcases hs with hs | hs
    · exact Or.inl fun i hi => hs _ (mem_coeffs.mpr ⟨i, hi, rfl⟩)
    · exact Or.inr fun i hi => hs _ (mem_coeffs.mpr ⟨i, hi, rfl⟩)
  · obtain ⟨q, hq, hq0⟩ := hne
    obtain ⟨i, hi, rfl⟩ := mem_coeffs.mp hq
    exact ⟨i, hi, hq0⟩

/-! ## The shared anchor -/

/-- Replay is sound without uniqueness: one real root `θ` of `s` (and of `m`) in `[lo, hi]`
at which every replayed sign holds. -/
theorem replayAll_sound {m s : D} {lo hi : ℚ} {a : Anchor} {gs : List D}
    {ws : List (ℤ × SignWhy)} (h : replayAll m s lo hi a gs ws = true) :
    ∃ θ : ℝ, (lo : ℝ) ≤ θ ∧ θ ≤ hi ∧ rv m θ = 0 ∧ rv s θ = 0 ∧
      ∀ p ∈ gs.zip ws, rsgn (rv p.1 θ) = p.2.1 := by
  unfold replayAll at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hsm, ha⟩, -⟩, hall⟩ := h
  cases a with
  | exact r =>
    simp only [anchorOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ha
    obtain ⟨⟨hlo, hhi⟩, hr⟩ := ha
    have hs : rv s r = 0 := by rw [rv_ratCast, hr, Rat.cast_zero]
    refine ⟨r, by exact_mod_cast hlo, by exact_mod_cast hhi, rv_dvd hsm hs, hs, ?_⟩
    rintro ⟨g, σ, why⟩ hp
    have hw := hall _ hp
    cases why <;> simp only [replaySign, beq_iff_eq, Bool.false_eq_true] at hw
    show rsgn (rv g r) = σ
    rw [rv_ratCast, rsgn_ratCast, hw]
  | bracket t c d =>
    simp only [anchorOk, Bool.and_eq_true, decide_eq_true_eq] at ha
    obtain ⟨⟨⟨⟨hlo, hcd⟩, hhi⟩, hts⟩, hch⟩ := ha
    obtain ⟨θ, h1, h2, hθ⟩ := root_of_sign_change hcd hch
    have hs := rv_dvd hts hθ
    have hlo' : (lo : ℝ) ≤ c := by exact_mod_cast hlo
    have hhi' : (d : ℝ) ≤ hi := by exact_mod_cast hhi
    refine ⟨θ, by linarith, by linarith, rv_dvd hsm hs, hs, ?_⟩
    rintro ⟨g, σ, why⟩ hp
    have hw := hall _ hp
    show rsgn (rv g θ) = σ
    cases why
    · simp [replaySign] at hw
    · simp only [replaySign, Bool.and_eq_true, beq_iff_eq] at hw
      obtain ⟨rfl, hdv⟩ := hw
      exact rsgn_eq_zero.mpr (rv_dvd hdv hθ)
    · simp only [replaySign, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hw
      obtain ⟨⟨hσ, hgc⟩, hno⟩ := hw
      have hc0 : rv g c ≠ 0 := by
        intro h0
        apply hσ
        rw [← hgc, ← rsgn_ratCast, ← rv_ratCast, h0]
        exact rsgn_eq_zero.mpr rfl
      rw [rsgn_const (rv_noRoot hno) hc0 ⟨h1, h2⟩, rv_ratCast, rsgn_ratCast, hgc]

/-! ## Evaluation in `ℚ[θ]/(s)` -/

theorem rv_powMod {b s : D} (hs : rv s x = 0) : ∀ k, rv (powMod b s k) x = rv b x ^ k
  | 0 => by simp [powMod]
  | k + 1 => by rw [powMod, rv_mod hs, rv_mul, rv_powMod hs k, pow_succ]

theorem rv_monoAt {cs : List D} {s : D} {e : List ℕ} (hs : rv s x = 0) :
    ∀ k, rv (monoAt cs s e k) x = ∏ i ∈ Finset.range k, rv (cs.getD i 0) x ^ e.getD i 0
  | 0 => by simp [monoAt]
  | k + 1 => by
    rw [monoAt, rv_mod hs, rv_mul, rv_monoAt hs k, rv_powMod hs, Finset.prod_range_succ]

theorem rv_foldl {α : Type} (F : α → D) (x : ℝ) : ∀ (l : List α) (init : D),
    rv (l.foldl (fun acc a => acc + F a) init) x = rv init x + (l.map fun a => rv (F a) x).sum
  | [], init => by simp
  | a :: l, init => by simp [List.foldl_cons, rv_foldl F x l, add_assoc]

/-- At a root of `s`, the reduced obligation is the obligation at the coordinates. -/
theorem rv_fieldEval {n : ℕ} {cs : List D} {s : D} {f : Sparse} (hs : rv s x = 0) :
    rv (fieldEval n cs s f) x = Binder.valueE ℝ n f (fun i => rv (cs.getD i 0) x) := by
  have hfold := rv_foldl (fun t : List ℕ × ℚ => RAlg.C t.2 * monoAt cs s t.1 n) x f 0
  rw [fieldEval, rv_mod hs, hfold, rv_zero, zero_add, Binder.valueE_eq]
  congr 1
  apply List.map_congr_left
  intro t _
  rw [rv_mul, rv_C, rv_monoAt hs,
    Fin.prod_univ_eq_prod_range (fun i => rv (cs.getD i 0) x ^ t.1.getD i 0)]

/-- A univariate sign claim holds at some root of `m` in `[lo, hi]` (the selected root, by
isolation; soundness does not need that uniqueness). -/
theorem signClaim_sound {m g : D} {lo hi : ℚ} {σ : ℤ} (h : signClaim m lo hi g σ = true) :
    ∃ θ : ℝ, (lo : ℝ) ≤ θ ∧ θ ≤ hi ∧ rv m θ = 0 ∧ rsgn (rv g θ) = σ := by
  unfold signClaim at h
  split at h
  · exact absurd h Bool.false_ne_true
  · split at h
    · rename_i w _
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hσ, hr⟩ := h
      obtain ⟨θ, h1, h2, h3, -, h4⟩ := replayAll_sound hr
      refine ⟨θ, h1, h2, h3, ?_⟩
      rw [← hσ]
      exact h4 (g, w) (by simp)
    · exact absurd h Bool.false_ne_true

end GPBinding.Real.RAlg

namespace GPBinding.Real
open GPProfile GPProfile.Real GPProfile.Real.RAlg GPBinding.Real.RAlg

/-- A real point satisfies a real system: equations vanish, guards do not, signs as required. -/
def RealSat (sys : RealSys) (x : Fin sys.vars.length → ℝ) : Prop :=
  (∀ e ∈ sys.eqs, Binder.valueE ℝ sys.vars.length e x = 0) ∧
  (∀ g ∈ sys.guards, Binder.valueE ℝ sys.vars.length g x ≠ 0) ∧
  (∀ p ∈ sys.signs, ((SignType.sign (Binder.valueE ℝ sys.vars.length p.1 x) : SignType) : ℤ) = p.2)

theorem exists_zip_of_mem {α β : Type} {l : List α} {l' : List β} (hlen : l.length = l'.length)
    {a : α} (ha : a ∈ l) : ∃ b, (a, b) ∈ l.zip l' := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  have hi' : i < (l.zip l').length := by simp [List.length_zip, ← hlen, hi]
  exact ⟨l'[i]'(hlen ▸ hi), by simpa using List.getElem_mem hi'⟩

/-- Replay of a point certificate is sound over ℝ: the anchored root `θ` of the generator
in `[lo, hi]`, with the coordinates evaluated at `θ`, satisfies the system. -/
theorem pointReplay_sound {sys : RealSys} {w : RealWitness} {s : D} {a : Anchor}
    {ws : List (ℤ × SignWhy)} (h : pointReplay sys w s a ws = true) :
    (∀ o ∈ sys.obligations, sparseArity sys.vars.length o.1 = true) ∧
    ∃ θ : ℝ, (w.lo : ℝ) ≤ θ ∧ θ ≤ w.hi ∧ rv (ofU w.m) θ = 0 ∧
      RealSat sys (fun i => rv ((w.coords.map ofU).getD i 0) θ) := by
  unfold pointReplay at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨-, har⟩, hlen⟩, hreq⟩, hrep⟩ := h
  refine ⟨har, ?_⟩
  obtain ⟨θ, hlo, hhi, hm, hs, hsig⟩ := replayAll_sound hrep
  refine ⟨θ, hlo, hhi, hm, ?_⟩
  have key : ∀ o ∈ sys.obligations, ∃ σ : ℤ, o.2.ok σ = true ∧
      rsgn (Binder.valueE ℝ sys.vars.length o.1
        (fun i => rv ((w.coords.map ofU).getD i 0) θ)) = σ := by
    intro o ho
    obtain ⟨wv, hw⟩ := exists_zip_of_mem hlen ho
    refine ⟨wv.1, hreq _ hw, ?_⟩
    have hmem : (fieldEval sys.vars.length (w.coords.map ofU) s o.1, wv) ∈
        (sys.obligations.map fun o => fieldEval sys.vars.length (w.coords.map ofU) s o.1).zip ws := by
      rw [List.zip_map_left]
      exact List.mem_map.mpr ⟨(o, wv), hw, rfl⟩
    have h1 := hsig _ hmem
    dsimp only at h1
    rwa [rv_fieldEval hs] at h1
  refine ⟨fun e he => ?_, fun g hg => ?_, fun p hp => ?_⟩
  · obtain ⟨σ, hok, hσ⟩ := key (e, .zero) (by simp [RealSys.obligations, he])
    simp only [Req.ok, beq_iff_eq] at hok
    subst hok
    exact rsgn_eq_zero.mp hσ
  · obtain ⟨σ, hok, hσ⟩ := key (g, .nonzero) (by simp [RealSys.obligations, hg])
    simp only [Req.ok, bne_iff_ne, ne_eq] at hok
    intro h0
    apply hok
    rw [← hσ, rsgn_eq_zero.mpr h0]
  · obtain ⟨q, τ⟩ := p
    obtain ⟨σ, hok, hσ⟩ := key (q, .sign τ) (by
      simp only [RealSys.obligations, List.mem_append, List.mem_map]
      exact Or.inr ⟨(q, τ), hp, rfl⟩)
    simp only [Req.ok, beq_iff_eq] at hok
    subst hok
    exact hσ

/-- An accepted point: a root `θ` of the witness generator in `[lo, hi]` whose coordinates
satisfy the system. -/
theorem pointCheck_point {s : RealSys} {w : RealWitness} (h : pointCheck s w = true) :
    ∃ θ : ℝ, (w.lo : ℝ) ≤ θ ∧ θ ≤ w.hi ∧ rv (ofU w.m) θ = 0 ∧
      RealSat s (fun i => rv ((w.coords.map ofU).getD i 0) θ) := by
  unfold pointCheck at h
  split at h
  · exact (pointReplay_sound h).2
  · exact absurd h Bool.false_ne_true

/-- **Soundness over ℝ.** An accepted point check exhibits a real point satisfying the
system. -/
theorem pointCheck_sound {s : RealSys} {w : RealWitness} (h : pointCheck s w = true) :
    ∃ x : Fin s.vars.length → ℝ,
      (∀ e ∈ s.eqs, Binder.valueE ℝ s.vars.length e x = 0) ∧
      (∀ g ∈ s.guards, Binder.valueE ℝ s.vars.length g x ≠ 0) ∧
      (∀ p ∈ s.signs,
        ((SignType.sign (Binder.valueE ℝ s.vars.length p.1 x) : SignType) : ℤ) = p.2) := by
  obtain ⟨θ, -, -, -, hx⟩ := pointCheck_point h
  exact ⟨_, hx⟩

/-- On arity-correct polynomials the explicit value is the Kernel-facing `value`. -/
theorem valueE_eq_value {n : ℕ} {p : Sparse} (h : sparseArity n p = true) (x : Fin n → ℝ) :
    Binder.valueE ℝ n p x = Admission.value n p x := by
  unfold Binder.valueE Admission.value
  rw [Binder.toK_meaning h fun c _ => Admission.mem_good.mpr (by exact_mod_cast c.den_nz)]

/-- The same, stated with the 3a semantics `Admission.value` (pointCheck checks arity). -/
theorem pointCheck_sound_value {s : RealSys} {w : RealWitness} (h : pointCheck s w = true) :
    ∃ x : Fin s.vars.length → ℝ,
      (∀ e ∈ s.eqs, Admission.value s.vars.length e x = 0) ∧
      (∀ g ∈ s.guards, Admission.value s.vars.length g x ≠ 0) ∧
      (∀ p ∈ s.signs,
        ((SignType.sign (Admission.value s.vars.length p.1 x) : SignType) : ℤ) = p.2) := by
  have har : ∀ o ∈ s.obligations, sparseArity s.vars.length o.1 = true := by
    unfold pointCheck at h
    split at h
    · exact (pointReplay_sound h).1
    · exact absurd h Bool.false_ne_true
  obtain ⟨θ, -, -, -, he, hg, hsg⟩ := pointCheck_point h
  refine ⟨fun i => rv ((w.coords.map ofU).getD i 0) θ, fun e hm => ?_, fun g hm => ?_,
    fun p hm => ?_⟩
  · rw [← valueE_eq_value (har (e, .zero) (by simp [RealSys.obligations, hm]))]
    exact he e hm
  · rw [← valueE_eq_value (har (g, .nonzero) (by simp [RealSys.obligations, hm]))]
    exact hg g hm
  · rw [← valueE_eq_value (har (p.1, .sign p.2) (by
      simp only [RealSys.obligations, List.mem_append, List.mem_map]
      exact Or.inr ⟨p, hm, rfl⟩))]
    exact hsg p hm

end GPBinding.Real
