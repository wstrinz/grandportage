import GPBinding.Admission.RuleSound

/-!
The explicit form of a 3a statement, for theorem warrants (A4, G1 decision 2). A sparse
polynomial means the sum of its monomials with `Rat.cast` coefficients; on well-formed
statements this agrees with the checkers' Hex-based meaning, so a theorem about the explicit
form yields the Kernel's `Means`. Nothing here evaluates Hex code in the kernel.
-/

noncomputable section

namespace GPBinding.Binder
open GPProfile GPBinding.Admission MvPolynomial HexMvPolyMathlib

variable {K : Type*} [Field K]

/-! ## Explicit semantics and warrants -/

def valueE (K : Type*) [Field K] (n : ℕ) (p : Sparse) (x : Fin n → K) : K := eval x (elabK K n p)

def LocusE (K : Type*) [Field K] (s : Stmt) (x : Fin s.vars.length → K) : Prop :=
  (∀ e ∈ s.eqs, valueE K s.vars.length e x = 0) ∧ (∀ g ∈ s.guards, valueE K s.vars.length g x ≠ 0)

/-- Statement truth in `K`, written with explicit polynomials. -/
def HoldsE (K : Type*) [Field K] (s : Stmt) : Prop :=
  let n := s.vars.length
  let G := (s.guards.map fun g => elabK K n g).prod
  let I := Ideal.span {f | f ∈ s.eqs.map fun e => elabK K n e}
  match s.kind with
  | .empty => ∀ x, ¬ LocusE K s x
  | .nonempty => ∃ x, LocusE K s x
  | .vanishesOn h => ∀ x, LocusE K s x → valueE K n h x = 0
  | .inIdeal h => ∃ k : ℕ, elabK K n h * G ^ k ∈ I
  | .notInIdeal h => ¬ ∃ k : ℕ, elabK K n h * G ^ k ∈ I
  | .cover bs => ∀ x, LocusE K s x → ∃ b ∈ bs,
      (∀ e ∈ b.1, valueE K n e x = 0) ∧ (∀ g ∈ b.2, valueE K n g x ≠ 0)

/-- Every polynomial of the statement has the statement's arity. -/
def stmtArityOk (s : Stmt) : Bool := s.polys.all (arityOk s.vars.length)

open GPBinding.Spike in
/-- A theorem warrant's type: the explicit statement in every field of the scope. -/
def Warranted (s : GPProfile.Stmt) (scope : GPProfile.Scope) : Prop :=
  ∀ K : FieldCtx, Scope.mem K.carrier scope → HoldsE K.carrier s

theorem holds_iff_holdsE {s : Stmt} (harity : stmtArityOk s = true)
    (hgood : ∀ p ∈ s.polys, ∀ c ∈ p.coeffs, c ∈ Good K) : Holds K s ↔ HoldsE K s := by
  have hm : ∀ p ∈ s.polys, toK (K := K) (meaning s.vars.length p) = elabK K s.vars.length p :=
    fun p hp => toK_meaning (List.all_eq_true.mp harity p hp) (hgood p hp)
  have inE : ∀ e ∈ s.eqs, e ∈ s.polys := fun e he => by simp [Stmt.polys, he]
  have inG : ∀ g ∈ s.guards, g ∈ s.polys := fun g hg => by simp [Stmt.polys, hg]
  have inH : ∀ h, s.kind.target? = some h → h ∈ s.polys := fun h hh => by simp [Stmt.polys, hh]
  have inB : ∀ b ∈ s.kind.branchPolys, b ∈ s.polys := fun b hb => by simp [Stmt.polys, hb]
  have eqsMap : s.eqs.map (fun e => toK (K := K) (meaning s.vars.length e)) =
      s.eqs.map (fun e => elabK K s.vars.length e) := List.map_congr_left fun e he => hm e (inE e he)
  have guardsMap : s.guards.map (fun g => toK (K := K) (meaning s.vars.length g)) =
      s.guards.map (fun g => elabK K s.vars.length g) := List.map_congr_left fun g hg => hm g (inG g hg)
  have locus : ∀ x, Locus (K := K) s x ↔ LocusE K s x := by
    intro x
    unfold Locus LocusE value valueE
    constructor
    · rintro ⟨he, hg⟩
      exact ⟨fun e h => hm e (inE e h) ▸ he e h, fun g h => hm g (inG g h) ▸ hg g h⟩
    · rintro ⟨he, hg⟩
      exact ⟨fun e h => (hm e (inE e h)).symm ▸ he e h, fun g h => (hm g (inG g h)).symm ▸ hg g h⟩
  obtain ⟨v, e, g, k⟩ := s
  unfold Holds HoldsE
  simp only at eqsMap guardsMap locus hm
  cases k <;> simp only at hm inH ⊢
  case empty => exact forall_congr' fun x => not_congr (locus x)
  case nonempty => exact exists_congr fun x => locus x
  case vanishesOn h =>
    have hh := hm h (inH h rfl)
    exact forall_congr' fun x => imp_congr (locus x) (by unfold value valueE; rw [hh])
  case inIdeal h => rw [hm h (inH h rfl), eqsMap, guardsMap]
  case notInIdeal h => rw [hm h (inH h rfl), eqsMap, guardsMap]
  case cover bs =>
    refine forall_congr' fun x => imp_congr (locus x) (exists_congr fun b => and_congr_right fun hb => ?_)
    have hbp : ∀ p ∈ b.1 ++ b.2, p ∈ Stmt.polys ⟨v, e, g, .cover bs⟩ := fun p hp =>
      inB p (List.mem_flatMap.mpr ⟨b, hb, hp⟩)
    unfold value valueE
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun p h => hm p (hbp p (List.mem_append_left _ h)) ▸ h1 p h,
        fun p h => hm p (hbp p (List.mem_append_right _ h)) ▸ h2 p h⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun p h => (hm p (hbp p (List.mem_append_left _ h))).symm ▸ h1 p h,
        fun p h => (hm p (hbp p (List.mem_append_right _ h))).symm ▸ h2 p h⟩

open GP50 GPBinding.Spike in
/-- A warrant theorem for a well-formed statement gives the Kernel's meaning. -/
theorem means_of_warranted {s : GPProfile.Stmt} {scope : GPProfile.Scope} (harity : stmtArityOk s = true)
    (hav : scope.avoids s.primes = true) (h : Warranted s scope) :
    Semantic.Means profile s scope := by
  refine means_iff.mpr fun K hK => ?_
  exact (holds_iff_holdsE harity (stmt_good (avoids_mem hav hK))).mpr (h K hK)

/-! ## Evaluation of explicit polynomials (simp set for warrant proofs) -/

@[simp] theorem eval_monomial_expF {n : ℕ} (x : Fin n → K) (e : List ℕ) (c : K) :
    eval x (monomial (expF n e) c) = c * ∏ i : Fin n, x i ^ e.getD i.val 0 := by
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero (x i))]
  rfl

@[simp] theorem valueE_eq {n : ℕ} (x : Fin n → K) (p : Sparse) :
    valueE K n p x = (p.map fun t => ((t.2 : Rat) : K) * ∏ i : Fin n, x i ^ t.1.getD i.val 0).sum := by
  unfold valueE elabK
  induction p with
  | nil => simp
  | cons t p ih => simp [ih]

/-- A denominator is nonzero in every field of a scope that avoids its prime factors. -/
theorem natCast_ne_zero_of_scope {sc : Scope} (hK : sc.mem K) {D : ℕ} (hD0 : D ≠ 0)
    (hD : sc.avoids (primeFactors D) = true) : (D : K) ≠ 0 := by
  have hav := avoids_mem hD hK
  intro hz
  have hdvd : ringChar K ∣ D := (ringChar.spec K D).mp hz
  rcases hav with h0 | ⟨hp, hm⟩
  · rw [h0] at hdvd
    exact hD0 (Nat.eq_zero_of_zero_dvd hdvd)
  · exact hm (mem_primeFactors hp (Nat.pos_of_ne_zero hD0) hdvd)

/-- The same, from an explicit prime factorization (no prime-factor search in the kernel). -/
theorem natCast_ne_zero_of_factors {sc : Scope} (hK : sc.mem K) (fs : List ℕ)
    (hp : ∀ p ∈ fs, p.Prime) {D : ℕ} (hprod : fs.prod = D) (hav : sc.avoids fs = true) :
    (D : K) ≠ 0 := by
  have hA := avoids_mem hav hK
  subst hprod
  rw [Nat.cast_list_prod]
  refine List.prod_ne_zero ?_
  intro hz
  obtain ⟨p, hpf, hpz⟩ := List.mem_map.mp hz
  have hdvd : ringChar K ∣ p := (ringChar.spec K p).mp hpz
  rcases (Nat.dvd_prime (hp p hpf)).mp hdvd with h1 | h2
  · exact CharP.ringChar_ne_one h1
  · rcases hA with h0 | ⟨-, hm⟩
    · rw [h0] at h2; exact (hp p hpf).ne_zero h2.symm
    · exact hm (h2 ▸ hpf)

end GPBinding.Binder

end
