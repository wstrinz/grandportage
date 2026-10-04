import GPBinding.Admission.Bridge

/-!
Meaning of 3a statements and scopes in a field `K` (post-G2 §3.1–3.2). A rational coefficient
means its `Rat.cast`; well-formedness keeps every denominator a unit in `K`.
-/

noncomputable section

namespace GPBinding.Admission
open GPProfile MvPolynomial

variable {K : Type*} [Field K]

/-- The value of a sparse polynomial at a point of `Kⁿ`. -/
def value (n : ℕ) (p : Sparse) (x : Fin n → K) : K := eval x (toK (meaning n p))

/-- The locus `{x | eqs(x) = 0, guards(x) ≠ 0}`. -/
def Locus (s : Stmt) (x : Fin s.vars.length → K) : Prop :=
  (∀ e ∈ s.eqs, value _ e x = 0) ∧ (∀ g ∈ s.guards, value _ g x ≠ 0)

variable (K) in
/-- Truth of a 3a statement in `K`. IN_IDEAL is ideal membership in `K[x][1/∏ guards]`:
some `h·(∏ guards)^k` lies in the ideal of the equations. -/
def Holds (s : Stmt) : Prop :=
  match s.kind with
  | .empty => ∀ x, ¬ Locus (K := K) s x
  | .nonempty => ∃ x, Locus (K := K) s x
  | .vanishesOn h => ∀ x, Locus (K := K) s x → value _ h x = 0
  | .inIdeal h => ∃ k : ℕ,
      toK (K := K) (meaning s.vars.length h) *
          (s.guards.map fun g => toK (K := K) (meaning s.vars.length g)).prod ^ k ∈
        Ideal.span {f | f ∈ s.eqs.map fun e => toK (K := K) (meaning s.vars.length e)}
  | .notInIdeal h => ¬ ∃ k : ℕ,
      toK (K := K) (meaning s.vars.length h) *
          (s.guards.map fun g => toK (K := K) (meaning s.vars.length g)).prod ^ k ∈
        Ideal.span {f | f ∈ s.eqs.map fun e => toK (K := K) (meaning s.vars.length e)}
  | .cover bs => ∀ x, Locus (K := K) s x → ∃ b ∈ bs,
      (∀ e ∈ b.1, value s.vars.length e x = 0) ∧ (∀ g ∈ b.2, value s.vars.length g x ≠ 0)

/-- The characteristics a scope denotes. -/
def _root_.GPProfile.Scope.den (sc : Scope) : Set ℕ :=
  {c | (c = 0 ∧ sc.char0 = true) ∨
    (c.Prime ∧ match sc.primes with
      | .finite ps => c ∈ ps
      | .cofinite e => c ∉ e)}

variable (K) in
def _root_.GPProfile.Scope.mem (sc : Scope) : Prop := ringChar K ∈ sc.den

/-! ## Scope inclusion is sound -/

theorem _root_.GPProfile.Scope.le_den {a b : Scope} (h : a.le b = true) : a.den ⊆ b.den := by
  intro c hc
  unfold Scope.le at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h0, hp⟩ := h
  rcases hc with ⟨rfl, hc⟩ | ⟨prime, hm⟩
  · left; refine ⟨rfl, ?_⟩; simp_all
  · right; refine ⟨prime, ?_⟩
    have hpr : isPrime c = true := (isPrime_iff c).mpr prime
    rcases ha : a.primes with xs | ea <;> rcases hb : b.primes with ys | eb <;>
      simp only [ha, hb] at hp hm ⊢
    · have := List.all_eq_true.mp hp c hm; simpa [hpr] using this
    · have := List.all_eq_true.mp hp c hm; simpa [hpr] using this
    · simp at hp
    · intro mem; have := List.all_eq_true.mp hp c mem; simp [hpr] at this; exact hm this

/-! ## Excluded primes make coefficients good -/

/-- `ringChar K` is `0`, or a prime outside `bad`. -/
def Avoids (K : Type*) [Field K] (bad : List ℕ) : Prop :=
  ringChar K = 0 ∨ ((ringChar K).Prime ∧ ringChar K ∉ bad)

theorem mem_outside {bad : List ℕ} (h : (Scope.outside bad).mem K) : Avoids K bad := by
  rcases h with ⟨h0, -⟩ | ⟨hp, hm⟩
  · exact Or.inl h0
  · exact Or.inr ⟨hp, hm⟩

theorem mem_only {p : ℕ} (h : (Scope.only p).mem K) : ringChar K = p := by
  rcases h with ⟨-, h⟩ | ⟨-, hm⟩
  · simp [Scope.only] at h
  · simpa [Scope.only] using hm

theorem Avoids.mono {a b : List ℕ} (h : Avoids K b) (hab : ∀ x ∈ a, x ∈ b) : Avoids K a := by
  rcases h with h | ⟨hp, hm⟩
  · exact Or.inl h
  · exact Or.inr ⟨hp, fun ha => hm (hab _ ha)⟩

theorem Avoids.ne {bad : List ℕ} (h : Avoids K bad) {p : ℕ} (hp : p.Prime) (hb : p ∈ bad) :
    ringChar K ≠ p := by
  rcases h with h | ⟨-, hm⟩
  · rw [h]; exact (Nat.Prime.ne_zero hp).symm
  · rintro rfl; exact hm hb

theorem good_of_avoids {cs : List Rat} (h : Avoids K (denominatorPrimes cs)) {c : Rat}
    (hc : c ∈ cs) : c ∈ Good K :=
  den_ne_zero_of_primes fun _ hp hd => h.ne hp (mem_denominatorPrimes hc hp hd)

theorem prime_good {cs : List Rat} {p : ℕ} (hK : ringChar K = p)
    (hp : p ∉ denominatorPrimes cs) {c : Rat} (hc : c ∈ cs) : c ∈ Good K :=
  den_ne_zero_of_primes fun q hq hd hqp => hp (hK ▸ hqp ▸ mem_denominatorPrimes hc hq hd)

/-! ## A nonzero coefficient is a stored term -/

theorem mem_terms_of_coeff_ne {n : ℕ} (P : GPProfile.P n Rat) (m : Hex.Mono n)
    (h : Hex.MvPoly.coeff m P ≠ 0) : (m, Hex.MvPoly.coeff m P) ∈ P.termsList := by
  unfold Hex.MvPoly.termsList
  apply Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr
  unfold Hex.MvPoly.coeff Hex.MvPoly.coeff? at *
  cases hc : P.termsInternal[m]? with
  | none => simp [hc] at h
  | some c => simp [hc]

end GPBinding.Admission

end
