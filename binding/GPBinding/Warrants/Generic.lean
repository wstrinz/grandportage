import GPBinding.Binder.Explicit
import GPBinding.Admission.Sound

/-!
Generic theorem warrants (post-G3a decision 9: the certificate-to-Lean emitter). Each theorem is
proved once; an emitted warrant applies one of them to a held claim's data, with side conditions
that are small structural computations the kernel checks by `decide`. Primality is never decided
in the kernel: the emitter supplies prime factorizations, `norm_num` proves their primes prime,
and `decide` only multiplies and tests list membership. No Hex code is evaluated in the kernel,
and nothing here uses `native_decide`.

- `warranted_point`: NONEMPTY from an integer point, over ℚ or mod p.
- `warranted_bridge`: a point gives NOT_IN_IDEAL(1) on the same system.
- `warranted_properCoeff`: NOT_IN_IDEAL(1) of one unguarded equation from a coefficient that is
  nonzero in every field of the scope, at a non-constant monomial.
- `Warranted.mono`: a warrant holds on every narrower scope.
-/

noncomputable section

namespace GPBinding.Warrants
open GPProfile GPBinding.Binder GPBinding.Admission MvPolynomial

variable {K : Type*} [Field K]

/-! ## Integer evaluation -/

/-- Every coefficient is an integer. -/
def intCoeffs (p : Sparse) : Bool := p.all fun t => t.2.den == 1

/-- The value of a sparse polynomial at an integer point, over ℤ. -/
def evalZ (n : ℕ) (p : Sparse) (a : List ℤ) : ℤ :=
  (p.map fun t => t.2.num * ((List.finRange n).map fun i => a.getD i.val 0 ^ t.1.getD i.val 0).prod).sum

theorem cast_of_den_one {q : ℚ} (h : q.den = 1) : ((q : ℚ) : K) = ((q.num : ℤ) : K) :=
  (congrArg (fun r : ℚ => (r : K)) (Rat.coe_int_num_of_den_eq_one h).symm).trans (Rat.cast_intCast _)

theorem valueE_int (n : ℕ) (p : Sparse) (a : List ℤ) (hp : intCoeffs p = true) :
    valueE K n p (fun i => ((a.getD i.val 0 : ℤ) : K)) = ((evalZ n p a : ℤ) : K) := by
  rw [valueE_eq]
  unfold evalZ
  rw [Int.cast_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t ht
  have hden : t.2.den = 1 := by simpa [intCoeffs] using List.all_eq_true.mp hp t ht
  simp only [Function.comp, Int.cast_mul, Int.cast_list_prod, List.map_map, Fin.prod_univ_def]
  congr 1
  · exact cast_of_den_one hden
  · congr 1
    apply List.map_congr_left
    intro i _
    simp

/-! ## Values that vanish, or do not, in every field of a scope -/

/-- `v` is zero in every field of the scope: it is 0, or the scope is a finite set of primes
dividing it. -/
def zeroIn (sc : Scope) (v : ℤ) : Bool :=
  v == 0 || (!sc.char0 && match sc.primes with
    | .finite ps => ps.all fun p => v % (p : ℤ) == 0
    | .cofinite _ => false)

theorem zero_of_zeroIn {sc : Scope} (hK : sc.mem K) {v : ℤ} (h : zeroIn sc v = true) : (v : K) = 0 := by
  unfold zeroIn at h
  rcases Bool.or_eq_true_iff.mp h with h0 | h1
  · rw [beq_iff_eq.mp h0, Int.cast_zero]
  · obtain ⟨c0, ps⟩ := sc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
    obtain ⟨hc0, hps⟩ := h1
    rcases hK with ⟨-, h⟩ | ⟨hp, hm⟩
    · simp_all
    · cases ps with
      | cofinite _ => simp at hps
      | finite ps =>
        simp only [List.all_eq_true, beq_iff_eq] at hps
        have hd : ((ringChar K : ℕ) : ℤ) ∣ v := Int.dvd_of_emod_eq_zero (hps _ hm)
        exact (CharP.intCast_eq_zero_iff K (ringChar K) v).mpr hd

/-- The scope's characteristics all avoid the primes `fs`, by list membership only. -/
def avoidsS (sc : Scope) (fs : List ℕ) : Bool :=
  match sc.primes with
  | .finite ps => fs.all fun f => !ps.contains f
  | .cofinite e => fs.all e.contains

/-- A nonzero integer whose prime factorization `fs` the scope avoids is nonzero in its fields. -/
theorem ne_zero_of_factors {sc : Scope} (hK : sc.mem K) {v : ℤ} (fs : List ℕ) (hp : ∀ p ∈ fs, p.Prime)
    (hv : v ≠ 0) (hprod : fs.prod = v.natAbs) (hav : avoidsS sc fs = true) : (v : K) ≠ 0 := by
  intro hz
  have hd : ((ringChar K : ℕ) : ℤ) ∣ v := (CharP.intCast_eq_zero_iff K (ringChar K) v).mp hz
  have hdn : ringChar K ∣ fs.prod := hprod ▸ Int.natCast_dvd.mp hd
  rcases hK with ⟨h0, -⟩ | ⟨hc, hm⟩
  · rw [h0, Nat.cast_zero, zero_dvd_iff] at hd
    exact hv hd
  · obtain ⟨f, hf, hcf⟩ := (Prime.dvd_prod_iff (Nat.Prime.prime hc)).mp hdn
    have hcf' : ringChar K = f := (Nat.prime_dvd_prime_iff_eq hc (hp f hf)).mp hcf
    obtain ⟨c0, ps⟩ := sc
    cases ps with
    | finite ps =>
      simp only [avoidsS, List.all_eq_true] at hav
      have hnot : ¬ f ∈ ps := by simpa using hav f hf
      exact hnot (hcf' ▸ hm)
    | cofinite e =>
      simp only [avoidsS, List.all_eq_true, List.contains_iff_mem] at hav
      exact hm (hcf' ▸ hav f hf)

/-- Scope inclusion by list membership only; it implies `Scope.le` and needs no primality test. -/
def leS (a b : Scope) : Bool :=
  (!a.char0 || b.char0) && match a.primes, b.primes with
    | .finite xs, .finite ys => xs.all ys.contains
    | .finite xs, .cofinite e => xs.all fun x => !e.contains x
    | .cofinite _, .finite _ => false
    | .cofinite ea, .cofinite eb => eb.all ea.contains

theorem den_sub_of_leS {a b : Scope} (h : leS a b = true) : a.den ⊆ b.den := by
  intro c hc
  obtain ⟨ca, pa⟩ := a
  obtain ⟨cb, pb⟩ := b
  simp only [leS, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h0, hp⟩ := h
  rcases hc with ⟨rfl, hc⟩ | ⟨prime, hm⟩
  · left; refine ⟨rfl, ?_⟩; simp_all
  · right; refine ⟨prime, ?_⟩
    cases pa with
    | finite xs =>
      cases pb with
      | finite ys =>
        simp only [List.all_eq_true, List.contains_iff_mem] at hp
        exact hp c hm
      | cofinite e =>
        simp only [List.all_eq_true] at hp
        simpa using hp c hm
    | cofinite ea =>
      cases pb with
      | finite ys => simp at hp
      | cofinite eb =>
        simp only [List.all_eq_true, List.contains_iff_mem] at hp
        exact fun h => hm (hp c h)

/-! ## The warrant theorems -/

theorem Warranted.mono {s : Stmt} {a b : Scope} (h : Warranted s b) (hle : leS a b = true) : Warranted s a :=
  fun K hK => h K (den_sub_of_leS hle hK)

/-- Every guard's value at the point is nonzero, with a prime factorization the scope avoids. -/
def guardsOK (s : Stmt) (sc : Scope) (a : List ℤ) (primes : List ℕ) (fss : List (List ℕ)) : Bool :=
  s.guards.length == fss.length && (s.guards.zip fss).all fun (g, fs) =>
    intCoeffs g && evalZ s.vars.length g a != 0 && fs.prod == (evalZ s.vars.length g a).natAbs &&
      fs.all primes.contains && avoidsS sc fs

theorem warranted_point {s : Stmt} {sc : Scope} (a : List ℤ) (primes : List ℕ) (fss : List (List ℕ))
    (hk : s.kind = .nonempty) (hp : ∀ p ∈ primes, p.Prime)
    (hE : s.eqs.all (fun e => intCoeffs e && zeroIn sc (evalZ s.vars.length e a)) = true)
    (hG : guardsOK s sc a primes fss = true) :
    Warranted s sc := by
  intro K hK
  simp only [HoldsE, hk]
  refine ⟨fun i => ((a.getD i.val 0 : ℤ) : K.carrier), fun e he => ?_, fun g hg => ?_⟩
  · have h := List.all_eq_true.mp hE e he
    simp only [Bool.and_eq_true] at h
    rw [valueE_int _ _ _ h.1]
    exact zero_of_zeroIn hK h.2
  · unfold guardsOK at hG
    simp only [Bool.and_eq_true, beq_iff_eq] at hG
    obtain ⟨hlen, hall⟩ := hG
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    have hmem : (s.guards[i], fss[i]'(hlen ▸ hi)) ∈ s.guards.zip fss :=
      List.mem_iff_getElem.mpr ⟨i, by rw [List.length_zip, ← hlen, Nat.min_self]; exact hi, by simp⟩
    have h := List.all_eq_true.mp hall _ hmem
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at h
    obtain ⟨⟨⟨⟨hint, hv⟩, hprod⟩, hsub⟩, hav⟩ := h
    rw [valueE_int _ _ _ hint]
    exact ne_zero_of_factors hK _ (fun p hpf => hp p (hsub p hpf)) hv hprod hav

theorem elabK_oneP (n : ℕ) : elabK K n (oneP n) = 1 := by
  simp [elabK, oneP, expF_replicate_zero]

/-- A point of the locus refutes `1 · (∏ guards)^k ∈ (equations)`. -/
theorem warranted_bridge {v : List String} {e g : List Sparse} {sc : Scope}
    (h : Warranted ⟨v, e, g, .nonempty⟩ sc) : Warranted ⟨v, e, g, .notInIdeal (oneP v.length)⟩ sc := by
  intro K hK
  obtain ⟨x, hE, hG⟩ := h K hK
  simp only [HoldsE]
  rintro ⟨k, hk⟩
  rw [elabK_oneP, one_mul] at hk
  have hz := eval_span_zero' (x := x) hk (fun q hq => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact hE p hp)
  rw [map_pow, map_list_prod, List.map_map] at hz
  have hne : ((g.map ((eval x) ∘ fun q => elabK K.carrier v.length q))).prod ≠ 0 := by
    refine List.prod_ne_zero fun hz0 => ?_
    obtain ⟨q, hq, hq0⟩ := List.mem_map.mp hz0
    exact hG q hq hq0
  exact hne (pow_eq_zero_iff'.mp hz).1

/-! ## A coefficient that is nonzero -/

/-- The coefficient of the exponent list `mono` in `p`, over ℤ. -/
def coeffZ (p : Sparse) (mono : List ℕ) : ℤ := ((p.filter fun t => t.1 == mono).map (·.2.num)).sum

theorem expF_inj {n : ℕ} {a b : List ℕ} (ha : a.length = n) (hb : b.length = n) (h : expF n a = expF n b) :
    a = b := by
  apply List.ext_getElem (ha.trans hb.symm)
  intro i hia hib
  have := congrArg (fun f => f ⟨i, ha ▸ hia⟩) h
  simpa [expF, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hia, List.getElem?_eq_getElem hib] using this

theorem coeff_elabK (n : ℕ) (p : Sparse) (mono : List ℕ) (harity : arityOk n p = true)
    (hlen : mono.length = n) (hint : intCoeffs p = true) :
    (elabK K n p).coeff (expF n mono) = ((coeffZ p mono : ℤ) : K) := by
  unfold elabK coeffZ
  induction p with
  | nil => simp
  | cons t p ih =>
    simp only [arityOk, List.all_cons, Bool.and_eq_true, beq_iff_eq] at harity
    simp only [intCoeffs, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hint
    simp only [List.map_cons, List.sum_cons, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_monomial,
      List.filter_cons]
    rw [ih harity.2 hint.2]
    by_cases ht : t.1 = mono
    · subst ht
      simp [cast_of_den_one hint.1]
    · have hne : expF n t.1 ≠ expF n mono := fun h => ht (expF_inj harity.1 hlen h)
      simp [hne, ht]

theorem warranted_properCoeff {v : List String} {e : Sparse} {sc : Scope} (mono : List ℕ) (fs : List ℕ)
    (hp : ∀ p ∈ fs, p.Prime)
    (harity : arityOk v.length e = true) (hlen : mono.length = v.length) (hne : mono.any (· != 0) = true)
    (hint : intCoeffs e = true)
    (hc : (coeffZ e mono != 0 && fs.prod == (coeffZ e mono).natAbs && avoidsS sc fs) = true) :
    Warranted ⟨v, [e], [], .notInIdeal (oneP v.length)⟩ sc := by
  intro K hK
  simp only [HoldsE]
  rintro ⟨k, hk⟩
  simp only [List.map_nil, List.prod_nil, one_pow, mul_one, elabK_oneP, List.map_cons,
    List.mem_singleton, Set.ofPred_eq_eq_singleton] at hk
  have hu : IsUnit (elabK K.carrier v.length e) := isUnit_of_dvd_one (Ideal.mem_span_singleton.mp hk)
  obtain ⟨c, -, hcC⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
  have hm : expF v.length mono ≠ 0 := by
    intro h0
    obtain ⟨x, hx, hx0⟩ := List.any_eq_true.mp hne
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := congrArg (fun f => f ⟨i, hlen ▸ hi⟩) h0
    simp [expF, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at this
    simp [this] at hx0
  have hcoeff := coeff_elabK (K := K.carrier) v.length e mono harity hlen hint
  rw [hcC, coeff_C, ite_eq_right_of_eq_false _ _ (eq_false fun h => hm h.symm)] at hcoeff
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
  exact ne_zero_of_factors hK fs hp hc.1.1 hc.1.2 hc.2 hcoeff.symm

end GPBinding.Warrants
