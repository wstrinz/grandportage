import GPBinding.Admission.Semantics

/-!
The explicit polynomial of a sparse polynomial (`elabK`): the sum of its monomials with
`Rat.cast` coefficients. On arity-correct input it agrees with the checkers' Hex-based meaning
(`toK_meaning`). Shared by the rule soundness proofs and the binder's explicit statements.
-/

noncomputable section

namespace GPBinding.Binder
open GPProfile GPBinding.Admission MvPolynomial HexMvPolyMathlib

variable {K : Type*} [Field K]

/-- An exponent list as a monomial exponent. -/
def expF (n : ℕ) (e : List ℕ) : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => e.getD i.val 0

/-- The explicit polynomial of a sparse polynomial, over `K`. -/
def elabK (K : Type*) [Field K] (n : ℕ) (p : Sparse) : MvPolynomial (Fin n) K :=
  (p.map fun t => monomial (expF n t.1) ((t.2 : Rat) : K)).sum

/-- The explicit polynomial over ℚ. -/
def elabQ (n : ℕ) (p : Sparse) : MvPolynomial (Fin n) Rat :=
  (p.map fun t => monomial (expF n t.1) t.2).sum

/-- Every exponent list has the statement's arity. -/
def arityOk (n : ℕ) (p : Sparse) : Bool := p.all fun t => t.1.length == n

theorem monoEquiv_mono {n : ℕ} {e : List ℕ} {m : Hex.Mono n} (h : mono? n e = some m) :
    monoEquiv m = expF n e := by
  unfold mono? at h
  split_ifs at h with hl
  simp only [Option.some.injEq] at h
  subst h
  ext i
  have hi : i.val < e.length := by simpa using hl ▸ i.2
  rw [monoEquiv_apply]
  show (Vector.mk e.toArray hl)[i] = e.getD i.val 0
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem foldl_add_map {α M : Type*} [AddCommMonoid M] (f : α → M) :
    ∀ (l : List α) (a : M), l.foldl (fun acc t => acc + f t) a = a + (l.map f).sum
  | [], a => by simp
  | t :: l, a => by simp [foldl_add_map f l, add_assoc]

theorem meaning_eq_elabQ {n : ℕ} {p : Sparse} (h : arityOk n p = true) : meaning n p = elabQ n p := by
  have key : ∀ q : Sparse, arityOk n q = true →
      ∃ ts, q.mapM (fun x => (mono? n x.1).bind fun a => some (a, x.2)) = some ts ∧
        ts.map (fun term => monomial (monoEquiv term.1) term.2) =
          q.map (fun t => monomial (expF n t.1) t.2) := by
    intro q hq
    induction q with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons t q ih =>
      simp only [arityOk, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hq
      obtain ⟨ts, hts, hmap⟩ := ih (by simpa [arityOk] using hq.2)
      have hm : mono? n t.1 = some ⟨t.1.toArray, by simpa using hq.1⟩ := by simp [mono?, hq.1]
      refine ⟨(⟨t.1.toArray, by simpa using hq.1⟩, t.2) :: ts, by simp [List.mapM_cons, hm, hts], ?_⟩
      simp only [List.map_cons, hmap, monoEquiv_mono hm]
  obtain ⟨ts, hts, hmap⟩ := key p h
  have hq : toHexQ n p = some (Hex.MvPoly.ofTerms ts) := by
    simp [toHexQ, toHex, hts]
  rw [meaning_of hq, toMvPolynomial_ofTerms, foldl_add_map, zero_add, hmap]
  rfl

theorem toK_monomial (d : Fin n →₀ ℕ) (c : Rat) :
    toK (K := K) (monomial d c : MvPolynomial (Fin n) Rat) = monomial d (c : K) := by
  ext d'
  rw [coeff_toK, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

theorem toK_meaning {n : ℕ} {p : Sparse} (h : arityOk n p = true)
    (hg : ∀ c ∈ p.coeffs, c ∈ Good K) : toK (K := K) (meaning n p) = elabK K n p := by
  rw [meaning_eq_elabQ h, elabQ, toK_list_sum]
  · simp only [List.map_map, elabK]
    congr 1
    apply List.map_congr_left
    intro t _
    exact toK_monomial _ _
  · intro P hP
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hP
    exact mem_goodPoly.mpr fun d => by
      rw [coeff_monomial]
      split_ifs
      · exact hg _ (List.mem_map.mpr ⟨t, ht, rfl⟩)
      · exact (Good K).zero_mem

theorem expF_replicate_zero (n : ℕ) : expF n (List.replicate n 0) = 0 := by
  ext i
  simp [expF, List.getD_eq_getElem?_getD]

/-- The constant `oneP n` means 1. -/
theorem toK_meaning_one (n : ℕ) : toK (K := K) (meaning n (oneP n)) = 1 := by
  rw [toK_meaning (by simp [arityOk, oneP]) (fun c hc => by
    simp only [oneP, Sparse.coeffs, List.map_cons, List.map_nil, List.mem_singleton] at hc
    subst hc; exact (Good K).one_mem)]
  simp [elabK, oneP, expF_replicate_zero]

end GPBinding.Binder
