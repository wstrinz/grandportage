import GPBinding.Admission.Semantics
import GPBinding.Binder.Elab
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
Reach soundness for C1/C2/C3 (post-G2 §3.3): when `reach s c = some r`, the statement holds
in every field whose characteristic `r` denotes. Q replays and F_p replays (a rational residual
vanishing mod p) share one proof.
-/

noncomputable section

namespace GPBinding.Admission
open GPProfile MvPolynomial HexMvPolyMathlib

variable {K : Type*} [Field K]

/-! ## List helpers -/

theorem toK_zipWith_mul {σ : Type*} :
    ∀ (A B : List (MvPolynomial σ Rat)), (∀ P ∈ A, P ∈ GoodPoly K σ) → (∀ P ∈ B, P ∈ GoodPoly K σ) →
      (List.zipWith (· * ·) A B).map (toK (K := K)) =
        List.zipWith (· * ·) (A.map (toK (K := K))) (B.map (toK (K := K)))
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | a :: A, b :: B, hA, hB => by
    simp only [List.zipWith_cons_cons, List.map_cons]
    rw [toK_mul (hA a List.mem_cons_self) (hB b List.mem_cons_self),
      toK_zipWith_mul A B (fun P h => hA P (List.mem_cons_of_mem _ h))
        (fun P h => hB P (List.mem_cons_of_mem _ h))]

theorem zipWith_mul_good {σ : Type*} :
    ∀ (A B : List (MvPolynomial σ Rat)), (∀ P ∈ A, P ∈ GoodPoly K σ) → (∀ P ∈ B, P ∈ GoodPoly K σ) →
      ∀ P ∈ List.zipWith (· * ·) A B, P ∈ GoodPoly K σ
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | a :: A, b :: B, hA, hB => by
    intro P hP
    simp only [List.zipWith_cons_cons, List.mem_cons] at hP
    rcases hP with rfl | hP
    · exact (GoodPoly K σ).mul_mem (hA a List.mem_cons_self) (hB b List.mem_cons_self)
    · exact zipWith_mul_good A B (fun P h => hA P (List.mem_cons_of_mem _ h))
        (fun P h => hB P (List.mem_cons_of_mem _ h)) P hP

theorem eval_zipWith_sum_zero {n : ℕ} (x : Fin n → K) :
    ∀ (A B : List (MvPolynomial (Fin n) K)), (∀ b ∈ B, eval x b = 0) →
      eval x (List.zipWith (· * ·) A B).sum = 0
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | a :: A, b :: B, hB => by
    simp only [List.zipWith_cons_cons, List.sum_cons, map_add, map_mul]
    rw [hB b List.mem_cons_self, mul_zero, zero_add,
      eval_zipWith_sum_zero x A B fun c h => hB c (List.mem_cons_of_mem _ h)]

theorem eval_prod_ne_zero {n : ℕ} (x : Fin n → K) :
    ∀ (l : List (MvPolynomial (Fin n) K)), (∀ g ∈ l, eval x g ≠ 0) → eval x l.prod ≠ 0
  | [], _ => by simp
  | g :: l, h => by
    rw [List.prod_cons, map_mul]
    exact mul_ne_zero (h g List.mem_cons_self)
      (eval_prod_ne_zero x l fun c hc => h c (List.mem_cons_of_mem _ hc))

theorem zipWith_sum_mem_span {R : Type*} [CommRing R] :
    ∀ (A B : List R), (List.zipWith (· * ·) A B).sum ∈ Ideal.span {f | f ∈ B}
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: A, b :: B => by
    simp only [List.zipWith_cons_cons, List.sum_cons]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span List.mem_cons_self)) ?_
    exact Ideal.span_mono (fun f hf => List.mem_cons_of_mem _ hf) (zipWith_sum_mem_span A B)

/-! ## The identity in `K[x]` -/

/-- Every coefficient of every listed sparse polynomial is good in `K`. -/
def AllGood (K : Type*) [Field K] (ps : List Sparse) : Prop := ∀ p ∈ ps, ∀ c ∈ p.coeffs, c ∈ Good K

theorem identity_in_K {n : ℕ} {s : Stmt} {qs : List Sparse} {h : Sparse} {m k : ℕ}
    {R : GPProfile.P n Rat} (hR : residual n s qs h m k = some R)
    (hgood : AllGood K (s.eqs ++ s.guards ++ qs ++ [h]))
    (hzero : toK (K := K) (toMvPolynomial R) = 0) :
    qs.length = s.eqs.length ∧
      (List.zipWith (· * ·) (qs.map fun q => toK (K := K) (meaning n q))
        (s.eqs.map fun e => toK (K := K) (meaning n e))).sum =
        toK (meaning n h) ^ m * (s.guards.map fun g => toK (K := K) (meaning n g)).prod ^ k := by
  obtain ⟨hlen, hR'⟩ := residual_meaning hR
  refine ⟨hlen, ?_⟩
  have good : ∀ p ∈ s.eqs ++ s.guards ++ qs ++ [h], meaning n p ∈ GoodPoly K (Fin n) :=
    fun p hp => meaning_good (hgood p hp)
  have gE : ∀ P ∈ s.eqs.map (meaning n), P ∈ GoodPoly K (Fin n) := by
    intro P hP; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hP; exact good p (by simp [hp])
  have gG : ∀ P ∈ s.guards.map (meaning n), P ∈ GoodPoly K (Fin n) := by
    intro P hP; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hP; exact good p (by simp [hp])
  have gQ : ∀ P ∈ qs.map (meaning n), P ∈ GoodPoly K (Fin n) := by
    intro P hP; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hP; exact good p (by simp [hp])
  have gH : meaning n h ∈ GoodPoly K (Fin n) := good h (by simp)
  have gS := (GoodPoly K (Fin n)).list_sum_mem (zipWith_mul_good _ _ gQ gE)
  have gP := (GoodPoly K (Fin n)).mul_mem ((GoodPoly K (Fin n)).pow_mem gH m)
    ((GoodPoly K (Fin n)).pow_mem ((GoodPoly K (Fin n)).list_prod_mem gG) k)
  rw [hR', toK_sub gS gP, sub_eq_zero, toK_list_sum _ (zipWith_mul_good _ _ gQ gE),
    toK_zipWith_mul _ _ gQ gE, toK_mul ((GoodPoly K (Fin n)).pow_mem gH m)
      ((GoodPoly K (Fin n)).pow_mem ((GoodPoly K (Fin n)).list_prod_mem gG) k),
    toK_pow gH, toK_pow ((GoodPoly K (Fin n)).list_prod_mem gG), toK_list_prod _ gG,
    List.map_map, List.map_map, List.map_map] at hzero
  exact hzero

/-- A rational residual that vanishes mod `ringChar K` maps to zero. -/
theorem toK_residual_zero_mod {n : ℕ} {R : GPProfile.P n Rat} {p : ℕ} (hK : ringChar K = p)
    (h : R.termsList.all (fun t => zeroMod p t.2) = true) : toK (K := K) (toMvPolynomial R) = 0 := by
  ext d
  obtain ⟨m, rfl⟩ := (monoEquiv (n := n)).surjective d
  rw [coeff_toK, coeff_toMvPolynomial, coeff_zero]
  by_cases hc : Hex.MvPoly.coeff m R = 0
  · rw [hc, Rat.cast_zero]
  · have hz := List.all_eq_true.mp h _ (mem_terms_of_coeff_ne R m hc)
    simp only [zeroMod, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hz
    apply cast_eq_zero_of_dvd_num
    rw [hK]
    exact Int.dvd_of_emod_eq_zero hz.2

/-! ## Goodness from avoided primes -/

theorem allGood_of_avoids {ps : List Sparse} {bad : List ℕ} (h : Avoids K bad)
    (hsub : ∀ x ∈ denominatorPrimes (ps.flatMap Sparse.coeffs), x ∈ bad) : AllGood K ps :=
  fun p hp c hc => good_of_avoids (h.mono hsub) (List.mem_flatMap.mpr ⟨p, hp, hc⟩)

theorem mem_denominatorPrimes_flatMap {ps qs : List Sparse} (hsub : ∀ p ∈ ps, p ∈ qs) {x : ℕ}
    (hx : x ∈ denominatorPrimes (ps.flatMap Sparse.coeffs)) :
    x ∈ denominatorPrimes (qs.flatMap Sparse.coeffs) := by
  obtain ⟨c, hc, h⟩ := mem_denominatorPrimes_iff.mp hx
  obtain ⟨p, hp, hc⟩ := List.mem_flatMap.mp hc
  exact mem_denominatorPrimes_iff.mpr ⟨c, List.mem_flatMap.mpr ⟨p, hsub p hp, hc⟩, h⟩

/-! ## Reach soundness -/

theorem reach_ideal_spec {s : Stmt} {field : Field} {qs : List Sparse}
    {m k : ℕ} {r : Scope} (hr : reach s (.ideal field qs m k) = some r) (hK : r.mem K) :
    ∃ h R, idealTarget s m = some h ∧ residual s.vars.length s qs h m k = some R ∧
      Avoids K (union s.primes (denominatorPrimes (qs.flatMap Sparse.coeffs))) ∧
      toK (K := K) (toMvPolynomial R) = 0 := by
  simp only [reach, reachBase, Cert.primes] at hr
  split_ifs at hr with h1
  cases ht : idealTarget s m with
  | none => simp [ht] at hr
  | some h =>
    simp only [ht, Option.bind_eq_bind, Option.bind_some] at hr
    split_ifs at hr with h2
    cases hres : residual s.vars.length s qs h m k with
    | none => simp [hres] at hr
    | some R =>
      simp only [hres, Option.bind_some] at hr
      cases field with
      | rat =>
        dsimp only at hr
        split_ifs at hr with h3
        simp only [Option.some.injEq] at hr
        subst hr
        refine ⟨h, R, rfl, hres, mem_outside hK, ?_⟩
        rw [beq_iff_eq.mp h3]
        simp [toK_zero]
      | prime p =>
        simp at hr
        obtain ⟨⟨hpr, hnb⟩, hz, rfl⟩ := hr
        have hc := mem_only hK
        refine ⟨h, R, rfl, hres, Or.inr ⟨hc ▸ (isPrime_iff p).mp hpr, hc ▸ hnb⟩, ?_⟩
        exact toK_residual_zero_mod hc (List.all_eq_true.mpr fun t ht => hz t.1 t.2 ht)

theorem stmt_poly_primes {s : Stmt} {bad : List ℕ}
    (hsub : ∀ x ∈ s.primes, x ∈ bad) {p : Sparse} (hp : p ∈ s.polys) {c : Rat}
    (hc : c ∈ p.coeffs) {x : ℕ} (hx : x ∈ primeFactors c.den) : x ∈ bad :=
  hsub x (mem_denominatorPrimes_iff.mpr ⟨c, List.mem_flatMap.mpr ⟨p, hp, hc⟩, hx⟩)

/-- The identity an accepted ideal certificate establishes in `K[x]`. -/
theorem reach_ideal_identity {s : Stmt} {field : Field} {qs : List Sparse}
    {m k : ℕ} {r : Scope} (hr : reach s (.ideal field qs m k) = some r) (hK : r.mem K) :
    ∃ h, idealTarget s m = some h ∧
      (List.zipWith (· * ·) (qs.map fun q => toK (K := K) (meaning s.vars.length q))
        (s.eqs.map fun e => toK (K := K) (meaning s.vars.length e))).sum =
        toK (meaning s.vars.length h) ^ m *
          (s.guards.map fun g => toK (K := K) (meaning s.vars.length g)).prod ^ k := by
  obtain ⟨h, R, ht, hres, havoid, hzero⟩ := reach_ideal_spec hr hK
  have hS : ∀ x ∈ s.primes, x ∈ union s.primes (denominatorPrimes (qs.flatMap Sparse.coeffs)) :=
    fun x hx => mem_union_left hx
  have hgood : AllGood K (s.eqs ++ s.guards ++ qs ++ [h]) := by
    apply allGood_of_avoids havoid
    intro x hx
    obtain ⟨c, hc, hxc⟩ := mem_denominatorPrimes_iff.mp hx
    obtain ⟨p, hp, hcp⟩ := List.mem_flatMap.mp hc
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with ((hp | hp) | hp) | rfl
    · exact stmt_poly_primes hS (by simp [Stmt.polys, hp]) hcp hxc
    · exact stmt_poly_primes hS (by simp [Stmt.polys, hp]) hcp hxc
    · exact mem_union_right (mem_denominatorPrimes_iff.mpr ⟨c, List.mem_flatMap.mpr ⟨p, hp, hcp⟩, hxc⟩)
    · unfold idealTarget at ht
      cases hk : s.kind with
      | empty =>
        simp only [hk] at ht
        split_ifs at ht
        simp only [Option.some.injEq] at ht
        subst ht
        simp only [Sparse.coeffs, List.map_cons, List.map_nil, List.mem_singleton] at hcp
        subst hcp
        simp [primeFactors_one] at hxc
      | nonempty | notInIdeal _ | cover _ => simp [hk] at ht
      | inIdeal h0 =>
        simp only [hk] at ht; split_ifs at ht; simp only [Option.some.injEq] at ht; subst ht
        exact stmt_poly_primes hS (by simp [Stmt.polys, hk, Kind.target?]) hcp hxc
      | vanishesOn h0 =>
        simp only [hk] at ht; split_ifs at ht; simp only [Option.some.injEq] at ht; subst ht
        exact stmt_poly_primes hS (by simp [Stmt.polys, hk, Kind.target?]) hcp hxc
  exact ⟨h, ht, (identity_in_K hres hgood hzero).2⟩

theorem reach_ideal_sound {s : Stmt} {field : Field} {qs : List Sparse}
    {m k : ℕ} {r : Scope} (hr : reach s (.ideal field qs m k) = some r) (hK : r.mem K) :
    Holds K s := by
  obtain ⟨h, ht, I⟩ := reach_ideal_identity hr hK
  have locusEval : ∀ x, Locus (K := K) s x →
      eval x (List.zipWith (· * ·) (qs.map fun q => toK (K := K) (meaning _ q))
        (s.eqs.map fun e => toK (K := K) (meaning _ e))).sum = 0 ∧
      eval x (s.guards.map fun g => toK (K := K) (meaning _ g)).prod ≠ 0 := by
    intro x ⟨he, hg⟩
    refine ⟨eval_zipWith_sum_zero x _ _ ?_, eval_prod_ne_zero x _ ?_⟩
    · intro b hb; obtain ⟨e, heq, rfl⟩ := List.mem_map.mp hb; exact he e heq
    · intro b hb; obtain ⟨g, hgq, rfl⟩ := List.mem_map.mp hb; exact hg g hgq
  unfold idealTarget at ht
  unfold Holds
  cases hk : s.kind with
  | empty =>
    simp only [hk] at ht; split_ifs at ht with hm
    simp only [beq_iff_eq] at hm; subst hm
    intro x hx
    obtain ⟨h0, hG⟩ := locusEval x hx
    rw [I, map_mul, map_pow, map_pow, pow_zero, one_mul] at h0
    exact hG (pow_eq_zero_iff'.mp h0).1
  | nonempty | notInIdeal _ | cover _ => simp [hk] at ht
  | inIdeal h0 =>
    simp only [hk] at ht; split_ifs at ht with hm
    simp only [beq_iff_eq] at hm; subst hm
    simp only [Option.some.injEq] at ht; subst ht
    refine ⟨k, ?_⟩
    rw [← pow_one (toK (meaning _ h0)), ← I]
    exact zipWith_sum_mem_span _ _
  | vanishesOn h0 =>
    simp only [hk] at ht; split_ifs at ht with hm
    simp only [Option.some.injEq] at ht; subst ht
    intro x hx
    obtain ⟨h0, hG⟩ := locusEval x hx
    rw [I, map_mul, map_pow, map_pow] at h0
    rcases mul_eq_zero.mp h0 with hv | hv
    · exact pow_eq_zero_iff (by omega) |>.mp hv
    · exact absurd (pow_eq_zero_iff'.mp hv).1 hG

/-- An accepted EMPTY certificate is ideal-level in every field of its reach: a power of the guard
product lies in the ideal of the equations (EMPTY ≡ IN_IDEAL(1) by certificate). -/
theorem reach_empty_ideal {s : Stmt} {c : Cert} {r : Scope} (hs : s.kind = .empty)
    (hr : reach s c = some r) (hK : r.mem K) :
    ∃ k : ℕ, (s.guards.map fun g => toK (K := K) (meaning s.vars.length g)).prod ^ k ∈
      Ideal.span {f | f ∈ s.eqs.map fun e => toK (K := K) (meaning s.vars.length e)} := by
  cases c with
  | point f vs => simp [reach, reachBase, hs] at hr
  | proper f a b => simp [reach, reachBase, hs] at hr
  | cover t => simp [reach, hs] at hr
  | ideal field qs m k =>
    obtain ⟨h, ht, I⟩ := reach_ideal_identity hr hK
    simp only [idealTarget, hs] at ht
    split_ifs at ht with hm
    simp only [beq_iff_eq] at hm
    subst hm
    refine ⟨k, ?_⟩
    have e : (s.guards.map fun g => toK (K := K) (meaning s.vars.length g)).prod ^ k =
        toK (meaning s.vars.length h) ^ 0 *
          (s.guards.map fun g => toK (K := K) (meaning s.vars.length g)).prod ^ k := by
      rw [pow_zero, one_mul]
    rw [e, ← I]
    exact zipWith_sum_mem_span _ _

/-- An accepted VANISHES_ON(h) certificate is ideal-level: `h^m·(∏ guards)^k` lies in the ideal. -/
theorem reach_vanishes_ideal {s : Stmt} {c : Cert} {r : Scope} {h : Sparse}
    (hs : s.kind = .vanishesOn h) (hr : reach s c = some r) (hK : r.mem K) :
    ∃ m k : ℕ, toK (K := K) (meaning s.vars.length h) ^ m *
        (s.guards.map fun g => toK (K := K) (meaning s.vars.length g)).prod ^ k ∈
      Ideal.span {f | f ∈ s.eqs.map fun e => toK (K := K) (meaning s.vars.length e)} := by
  cases c with
  | point f vs => simp [reach, reachBase, hs] at hr
  | proper f a b => simp [reach, reachBase, hs] at hr
  | cover t => simp [reach, hs] at hr
  | ideal field qs m k =>
    obtain ⟨h', ht, I⟩ := reach_ideal_identity hr hK
    simp only [idealTarget, hs] at ht
    split_ifs at ht
    simp only [Option.some.injEq] at ht
    subst ht
    exact ⟨m, k, I ▸ zipWith_sum_mem_span _ _⟩

theorem eval_toK_cast {n : ℕ} {P : MvPolynomial (Fin n) Rat}
    (hP : P ∈ GoodPoly K (Fin n)) {a : Fin n → Rat} (ha : ∀ i, a i ∈ Good K) :
    eval (fun i => ((a i : Rat) : K)) (toK P) = ((eval a P : Rat) : K) ∧ eval a P ∈ Good K := by
  obtain ⟨P', rfl, hPK⟩ := toK_lift hP
  let a' : Fin n → Good K := fun i => ⟨a i, ha i⟩
  have hx : (fun i => ((a i : Rat) : K)) = castGood K ∘ a' := rfl
  have hq : a = (Good K).subtype ∘ a' := rfl
  have hv : eval a (MvPolynomial.map (Good K).subtype P') = ((eval a' P' : Good K) : Rat) := by
    rw [eval_map, hq, ← eval₂_comp]; rfl
  rw [hPK, hx, eval_map, ← eval₂_comp, hv]
  exact ⟨rfl, (eval a' P').2⟩

theorem reachBase_point_spec {s : Stmt} {field : Field} {vs : List Rat}
    {r : Scope} (hr : reachBase s (.point field vs) = some r) (hK : r.mem K) :
    s.kind = .nonempty ∧ ∃ ev gv, pointValues s.vars.length s vs = some (ev, gv) ∧
      Avoids K (union s.primes (denominatorPrimes vs)) ∧
      (∀ v ∈ ev, (v : K) = 0) ∧ (∀ v ∈ gv, v ∈ Good K → (v : K) ≠ 0) := by
  simp only [reachBase, Cert.primes] at hr
  split_ifs at hr with h1
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at h1
  cases hv : pointValues s.vars.length s vs with
  | none => simp [hv] at hr
  | some evgv =>
    obtain ⟨ev, gv⟩ := evgv
    simp only [hv, Option.bind_eq_bind, Option.bind_some] at hr
    refine ⟨h1.1, ev, gv, rfl, ?_⟩
    cases field with
    | rat =>
      simp at hr
      obtain ⟨⟨hev, hgv⟩, rfl⟩ := hr
      have hL := mem_outside hK
      have hbad : Avoids K (union s.primes (denominatorPrimes vs)) :=
        hL.mono fun x hx => (mem_foldl_union_iff _ _).mpr (Or.inl hx)
      refine ⟨hbad, fun v h => by rw [hev v h, Rat.cast_zero], fun v h hg => ?_⟩
      rw [Rat.cast_def]
      refine div_ne_zero (intCast_ne_zero_of_primes (Rat.num_ne_zero.mpr (hgv v h)) ?_) hg
      intro q hq hd
      exact hL.ne hq ((mem_foldl_union_iff _ _).mpr
        (Or.inr ⟨v, h, mem_primeFactors hq (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr (hgv v h))) hd⟩))
    | prime p =>
      simp at hr
      obtain ⟨⟨hpr, hnb⟩, ⟨hev, hgv⟩, rfl⟩ := hr
      have hc := mem_only hK
      refine ⟨Or.inr ⟨hc ▸ (isPrime_iff p).mp hpr, hc ▸ hnb⟩, fun v h => ?_, fun v h _ => ?_⟩
      · have hz := hev v h
        simp only [zeroMod, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hz
        apply cast_eq_zero_of_dvd_num
        rw [hc]; exact Int.dvd_of_emod_eq_zero hz.2
      · have hu := hgv v h
        simp only [unitMod, Bool.and_eq_true, bne_iff_ne, ne_eq] at hu
        rw [Rat.cast_def]
        refine div_ne_zero ?_ ?_
        · intro hn
          have := (CharP.intCast_eq_zero_iff K (ringChar K) v.num).mp hn
          rw [hc] at this
          exact hu.2 (Int.emod_eq_zero_of_dvd this)
        · intro hd
          have := (ringChar.spec K v.den).mp hd
          rw [hc] at this
          exact hu.1 (Nat.mod_eq_zero_of_dvd this)

theorem reachBase_point_sound {s : Stmt} {field : Field} {vs : List Rat}
    {r : Scope} (hr : reachBase s (.point field vs) = some r) (hK : r.mem K) : Holds K s := by
  obtain ⟨hk, ev, gv, hv, havoid, hev, hgv⟩ := reachBase_point_spec hr hK
  obtain ⟨hev', hgv'⟩ := pointValues_meaning hv
  have ha : ∀ i, pointFn vs s.vars.length i ∈ Good K := by
    intro i
    unfold pointFn
    by_cases hi : i.val < vs.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact good_of_avoids (havoid.mono fun x hx => mem_union_right hx) (List.getElem_mem hi)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
      exact (Good K).zero_mem
  have hS : Avoids K (denominatorPrimes (s.polys.flatMap Sparse.coeffs)) :=
    havoid.mono fun x hx => mem_union_left hx
  have meaningGood : ∀ p ∈ s.polys, meaning s.vars.length p ∈ GoodPoly K (Fin s.vars.length) :=
    fun p hp => meaning_good fun c hc => good_of_avoids hS (List.mem_flatMap.mpr ⟨p, hp, hc⟩)
  unfold Holds
  rw [hk]
  refine ⟨fun i => ((pointFn vs _ i : Rat) : K), ?_, ?_⟩
  · intro e he
    obtain ⟨h1, -⟩ := eval_toK_cast (meaningGood e (by simp [Stmt.polys, he])) ha
    unfold value
    rw [h1]
    apply hev
    rw [hev']
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := eval_toK_cast (meaningGood g (by simp [Stmt.polys, hg])) ha
    unfold value
    rw [h1]
    apply hgv _ _ h2
    rw [hgv']
    exact List.mem_map.mpr ⟨g, hg, rfl⟩

theorem reachBase_proper_spec {s : Stmt} {field : Field} {a b : List Rat}
    {r : Scope} (hr : reachBase s (.proper field a b) = some r) (hK : r.mem K) :
    s.kind = .notInIdeal (oneP s.vars.length) ∧ s.guards = [] ∧
      ∃ va vb ga gb, pointValues s.vars.length s a = some ([va], ga) ∧
        pointValues s.vars.length s b = some ([vb], gb) ∧
        Avoids K (union s.primes (denominatorPrimes (a ++ b))) ∧
        (va - vb ∈ Good K → ((va - vb : Rat) : K) ≠ 0) := by
  simp only [reachBase, Cert.primes] at hr
  split_ifs at hr with h1
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at h1
  obtain ⟨⟨⟨hk, hg⟩, -⟩, -⟩ := h1
  split at hr
  · rename_i va ga vb gb hA hB
    refine ⟨hk, by simpa using hg, va, vb, ga, gb, hA, hB, ?_⟩
    cases field with
    | rat =>
      simp only at hr
      split_ifs at hr with hd
      simp only [bne_iff_ne, ne_eq] at hd
      simp only [Option.some.injEq] at hr
      subst hr
      have hL := mem_outside hK
      refine ⟨hL.mono fun x hx => mem_union_left hx, fun hgd => ?_⟩
      rw [Rat.cast_def]
      refine div_ne_zero (intCast_ne_zero_of_primes (Rat.num_ne_zero.mpr hd) ?_) hgd
      intro q hq hdq
      exact hL.ne hq (mem_union_right (mem_primeFactors hq
        (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hd)) hdq))
    | prime p =>
      simp at hr
      obtain ⟨⟨hpr, hnb⟩, hu, rfl⟩ := hr
      have hc := mem_only hK
      refine ⟨Or.inr ⟨hc ▸ (isPrime_iff p).mp hpr, hc ▸ hnb⟩, fun _ => ?_⟩
      simp only [unitMod, Bool.and_eq_true, bne_iff_ne, ne_eq] at hu
      rw [Rat.cast_def]
      refine div_ne_zero ?_ ?_
      · intro hn
        have := (CharP.intCast_eq_zero_iff K (ringChar K) (va - vb).num).mp hn
        rw [hc] at this
        exact hu.2 (Int.emod_eq_zero_of_dvd this)
      · intro hd
        have := (ringChar.spec K (va - vb).den).mp hd
        rw [hc] at this
        exact hu.1 (Nat.mod_eq_zero_of_dvd this)
  · simp at hr

theorem pointFn_good {vs : List Rat} {n : ℕ} {bad : List ℕ} (havoid : Avoids K bad)
    (hsub : ∀ x ∈ denominatorPrimes vs, x ∈ bad) : ∀ i, pointFn vs n i ∈ Good K := by
  intro i
  unfold pointFn
  by_cases hi : i.val < vs.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact good_of_avoids (havoid.mono hsub) (List.getElem_mem hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
    exact (Good K).zero_mem

/-- A `proper` certificate: the equation is non-constant in `K`, so it is not a unit and `(m)` is a
proper ideal: NOT_IN_IDEAL(1), geometric nonemptiness. -/
theorem reach_proper_sound {s : Stmt} {field : Field} {a b : List Rat}
    {r : Scope} (hr : reach s (.proper field a b) = some r) (hK : r.mem K) : Holds K s := by
  simp only [reach] at hr
  obtain ⟨hk, hg, va, vb, ga, gb, hA, hB, havoid, hd⟩ := reachBase_proper_spec hr hK
  obtain ⟨ea, -⟩ := pointValues_meaning hA
  obtain ⟨eb, -⟩ := pointValues_meaning hB
  obtain ⟨v, e, g, kd⟩ := s
  simp only at hk hg ea eb havoid
  subst hk hg
  cases e with
  | nil => simp at ea
  | cons m rest =>
    cases rest with
    | cons _ _ => simp at ea
    | nil =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at ea eb
      have hS : Avoids K (denominatorPrimes ((Stmt.polys ⟨v, [m], [], .notInIdeal (oneP v.length)⟩).flatMap
          Sparse.coeffs)) := havoid.mono fun x hx => mem_union_left hx
      have mGood : meaning v.length m ∈ GoodPoly K (Fin v.length) :=
        meaning_good fun c hc => good_of_avoids hS (List.mem_flatMap.mpr ⟨m, by simp [Stmt.polys], hc⟩)
      have ha := pointFn_good (n := v.length) havoid fun x hx =>
        mem_union_right (by
          obtain ⟨c, hc, h⟩ := mem_denominatorPrimes_iff.mp hx
          exact mem_denominatorPrimes_iff.mpr ⟨c, List.mem_append_left _ hc, h⟩)
      have hb := pointFn_good (n := v.length) havoid fun x hx =>
        mem_union_right (by
          obtain ⟨c, hc, h⟩ := mem_denominatorPrimes_iff.mp hx
          exact mem_denominatorPrimes_iff.mpr ⟨c, List.mem_append_right _ hc, h⟩)
      obtain ⟨hA', gA⟩ := eval_toK_cast mGood ha
      obtain ⟨hB', gB⟩ := eval_toK_cast mGood hb
      unfold Holds
      rintro ⟨k, hk'⟩
      simp only [List.map_nil, List.prod_nil, one_pow, mul_one, GPBinding.Binder.toK_meaning_one,
        List.map_cons, List.mem_singleton, Set.ofPred_eq_eq_singleton] at hk'
      have hu : IsUnit (toK (K := K) (meaning v.length m)) :=
        isUnit_of_dvd_one (Ideal.mem_span_singleton.mp hk')
      obtain ⟨c, -, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
      have heq : eval (fun i => ((pointFn a v.length i : Rat) : K)) (toK (meaning v.length m)) =
          eval (fun i => ((pointFn b v.length i : Rat) : K)) (toK (meaning v.length m)) := by
        rw [hc, eval_C, eval_C]
      rw [hA', hB', ← ea, ← eb] at heq
      have gA' : va ∈ Good K := by rw [ea]; exact gA
      have gB' : vb ∈ Good K := by rw [eb]; exact gB
      apply hd ((Good K).sub_mem gA' gB')
      have hsub : ((va - vb : Rat) : K) = (va : K) - (vb : K) :=
        map_sub (castGood K) (⟨va, gA'⟩ : Good K) ⟨vb, gB'⟩
      rw [hsub, heq, sub_self]

theorem eval_span_zero' {n : ℕ} {x : Fin n → K} {l : List (MvPolynomial (Fin n) K)}
    {f : MvPolynomial (Fin n) K} (hf : f ∈ Ideal.span {g | g ∈ l}) (hl : ∀ g ∈ l, eval x g = 0) :
    eval x f = 0 := by
  have hle : Ideal.span {g | g ∈ l} ≤ RingHom.ker (eval x) :=
    Ideal.span_le.mpr fun g hg => (RingHom.mem_ker).mpr (hl g hg)
  exact (RingHom.mem_ker).mp (hle hf)

/-- Point certificates support NONEMPTY only (G3a review §2). -/
theorem reach_point_sound {s : Stmt} {field : Field} {vs : List Rat}
    {r : Scope} (hr : reach s (.point field vs) = some r) (hK : r.mem K) : Holds K s := by
  simp only [reach] at hr
  exact reachBase_point_sound hr hK

/-! ## C4 inclusion and covers -/

theorem forall₂_exists_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ a ∈ l, ∃ b ∈ l', R a b
  | [], [], .nil, _, ha => by simp at ha
  | _ :: _, b :: _, .cons hab rest, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b, List.mem_cons_self, hab⟩
    · obtain ⟨b', hb', h⟩ := forall₂_exists_right rest a ha
      exact ⟨b', List.mem_cons_of_mem _ hb', h⟩

theorem mem_zip_of_mem {α β : Type} {l : List α} {l' : List β} (hlen : l.length = l'.length)
    {a : α} (ha : a ∈ l) : ∃ b, (a, b) ∈ l.zip l' := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  exact ⟨l'[i]'(hlen ▸ hi), List.mem_iff_getElem.mpr ⟨i, by simp [hi, hlen ▸ hi], by simp⟩⟩

theorem inclusion_locus {T L : Stmt} {eqCerts guardCerts : List Cert} {obs : List (Stmt × Cert)}
    (h : inclusionObligations T L eqCerts guardCerts = some obs)
    (hobs : ∀ o ∈ obs, Holds K o.1) :
    T.vars = L.vars ∧ ∀ x, Locus (K := K) T x →
      (∀ e ∈ L.eqs, value T.vars.length e x = 0) ∧ (∀ g ∈ L.guards, value T.vars.length g x ≠ 0) := by
  unfold inclusionObligations at h
  split_ifs at h with hc
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at hc
  obtain ⟨⟨hv, he⟩, hg⟩ := hc
  simp only [Option.some.injEq] at h
  subst h
  refine ⟨hv, fun x hx => ⟨fun e heq => ?_, fun g hgq => ?_⟩⟩
  · obtain ⟨c, hc⟩ := mem_zip_of_mem he.symm heq
    have := hobs _ (List.mem_append_left _ (List.mem_map.mpr ⟨(e, c), hc, rfl⟩))
    exact this x hx
  · obtain ⟨c, hc⟩ := mem_zip_of_mem hg.symm hgq
    have := hobs _ (List.mem_append_right _ (List.mem_map.mpr ⟨(g, c), hc, rfl⟩))
    intro hz
    apply this x
    refine ⟨fun e' he' => ?_, hx.2⟩
    rcases List.mem_append.mp he' with he' | he'
    · exact hx.1 e' he'
    · rw [List.mem_singleton.mp he']; exact hz

theorem meet_den {a b : Scope} {c : ℕ}
    (h : c ∈ (⟨a.char0 && b.char0, meetPrimes a.primes b.primes⟩ : Scope).den) :
    c ∈ a.den ∧ c ∈ b.den := by
  obtain ⟨ca, pa⟩ := a
  obtain ⟨cb, pb⟩ := b
  rcases h with ⟨rfl, h0⟩ | ⟨hp, hm⟩
  · simp only [Bool.and_eq_true] at h0
    exact ⟨Or.inl ⟨rfl, h0.1⟩, Or.inl ⟨rfl, h0.2⟩⟩
  · cases pa <;> cases pb <;> simp_all [meetPrimes, Scope.den, List.mem_filter, mem_union]

theorem foldl_meet_den :
    ∀ (rs : List Scope) (a : Scope) {c : ℕ},
      c ∈ (rs.foldl (fun a b => (⟨a.char0 && b.char0, meetPrimes a.primes b.primes⟩ : Scope)) a).den →
      c ∈ a.den ∧ ∀ r ∈ rs, c ∈ r.den
  | [], _, _, h => ⟨h, by simp⟩
  | r :: rs, a, c, h => by
    obtain ⟨h1, h2⟩ := foldl_meet_den rs _ h
    obtain ⟨ha, hr⟩ := meet_den h1
    exact ⟨ha, fun r' hr' => (List.mem_cons.mp hr').elim (fun e => e ▸ hr) (h2 r')⟩

theorem inclusion_certs_ideal {T L : Stmt} {eqCerts guardCerts : List IdealCert}
    {obs : List (Stmt × Cert)}
    (h : inclusionObligations T L (eqCerts.map IdealCert.toCert) (guardCerts.map IdealCert.toCert) = some obs) :
    ∀ o ∈ obs, ∃ c : IdealCert, o.2 = c.toCert := by
  unfold inclusionObligations at h
  split_ifs at h
  simp only [Option.some.injEq] at h
  subst h
  intro o ho
  rcases List.mem_append.mp ho with h' | h'
  · obtain ⟨⟨e', c⟩, hc, rfl⟩ := List.mem_map.mp h'
    obtain ⟨c', -, rfl⟩ := List.mem_map.mp (List.of_mem_zip hc).2
    exact ⟨c', rfl⟩
  · obtain ⟨⟨g', c⟩, hc, rfl⟩ := List.mem_map.mp h'
    obtain ⟨c', -, rfl⟩ := List.mem_map.mp (List.of_mem_zip hc).2
    exact ⟨c', rfl⟩

theorem treeObligations_ideal {v : List String} {bs : List (List Sparse × List Sparse)} :
    ∀ (t : SplitTree) {E G : List Sparse} {obs : List (Stmt × Cert)},
      treeObligations v bs E G t = some obs → ∀ o ∈ obs, ∃ c : IdealCert, o.2 = c.toCert
  | .leaf i eqC gC, E, G, obs, h => by
    simp only [treeObligations] at h
    cases hb : bs[i]? with
    | none => simp [hb] at h
    | some b =>
      simp only [hb, Option.bind_eq_bind, Option.bind_some] at h
      exact inclusion_certs_ideal h
  | .empty c, E, G, obs, h => by
    simp only [treeObligations, Option.some.injEq] at h
    subst h
    intro o ho
    rw [List.mem_singleton.mp ho]
    exact ⟨c, rfl⟩
  | .split h t₀ t₁, E, G, obs, hh => by
    simp only [treeObligations] at hh
    cases h₀ : treeObligations v bs (E ++ [h]) G t₀ with
    | none => simp [h₀] at hh
    | some a =>
      cases h₁ : treeObligations v bs E (G ++ [h]) t₁ with
      | none => simp [h₀, h₁] at hh
      | some b =>
        simp only [h₀, h₁, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at hh
        subst hh
        intro o ho
        rcases List.mem_append.mp ho with ho | ho
        · exact treeObligations_ideal t₀ h₀ o ho
        · exact treeObligations_ideal t₁ h₁ o ho

/-- A split tree whose obligations hold puts every point of the subsystem in some branch. -/
theorem tree_locus {v : List String} {bs : List (List Sparse × List Sparse)} :
    ∀ (t : SplitTree) {E G : List Sparse} {obs : List (Stmt × Cert)},
      treeObligations v bs E G t = some obs → (∀ o ∈ obs, Holds K o.1) →
      ∀ x, Locus (K := K) (⟨v, E, G, .empty⟩ : Stmt) x → ∃ b ∈ bs,
        (∀ e ∈ b.1, value v.length e x = 0) ∧ (∀ g ∈ b.2, value v.length g x ≠ 0)
  | .leaf i eqC gC, E, G, obs, h, hobs, x, hx => by
    simp only [treeObligations] at h
    cases hb : bs[i]? with
    | none => simp [hb] at h
    | some b =>
      simp only [hb, Option.bind_eq_bind, Option.bind_some] at h
      obtain ⟨-, hloc⟩ := inclusion_locus h hobs
      exact ⟨b, List.mem_of_getElem? hb, hloc x hx⟩
  | .empty c, E, G, obs, h, hobs, x, hx => by
    simp only [treeObligations, Option.some.injEq] at h
    subst h
    exact absurd hx (hobs _ List.mem_cons_self x)
  | .split h t₀ t₁, E, G, obs, hh, hobs, x, hx => by
    simp only [treeObligations] at hh
    cases h₀ : treeObligations v bs (E ++ [h]) G t₀ with
    | none => simp [h₀] at hh
    | some a =>
      cases h₁ : treeObligations v bs E (G ++ [h]) t₁ with
      | none => simp [h₀, h₁] at hh
      | some b =>
        simp only [h₀, h₁, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at hh
        subst hh
        by_cases hz : value v.length h x = 0
        · refine tree_locus t₀ h₀ (fun o ho => hobs o (List.mem_append_left _ ho)) x
            ⟨fun e he => ?_, hx.2⟩
          rcases List.mem_append.mp he with he | he
          · exact hx.1 e he
          · rw [List.mem_singleton.mp he]; exact hz
        · refine tree_locus t₁ h₁ (fun o ho => hobs o (List.mem_append_right _ ho)) x
            ⟨hx.1, fun g hg => ?_⟩
          rcases List.mem_append.mp hg with hg | hg
          · exact hx.2 g hg
          · rw [List.mem_singleton.mp hg]; exact hz

theorem reach_cover_sound {s : Stmt} {t : SplitTree} {r : Scope}
    (hr : reach s (.cover t) = some r) (hK : r.mem K) : Holds K s := by
  obtain ⟨v, e, g, k⟩ := s
  cases k with
  | cover bs =>
    simp only [reach] at hr
    split_ifs at hr
    cases ho : treeObligations v bs e g t with
    | none => simp [ho] at hr
    | some obs =>
      simp only [ho, Option.bind_eq_bind, Option.bind_some] at hr
      cases hrs : reachAllBase obs with
      | none => simp [hrs] at hr
      | some rs =>
        simp only [hrs, Option.bind_some, Option.pure_def, Option.some.injEq] at hr
        subst hr
        have hobs : ∀ o ∈ obs, Holds K o.1 := by
          intro o ho'
          obtain ⟨r', hr', hreach⟩ := forall₂_exists_right (mapM_forall₂ hrs) o ho'
          have hmem := (foldl_meet_den rs (.outside []) hK).2 r' hr'
          obtain ⟨c, hc⟩ := treeObligations_ideal t ho o ho'
          rw [hc] at hreach
          exact reach_ideal_sound (r := r') (by simpa [reach, IdealCert.toCert] using hreach) hmem
        exact tree_locus t ho hobs
  | _ => simp [reach] at hr

/-- Reach soundness: a certificate's computed reach holds in every field it denotes. -/
theorem reach_sound {s : Stmt} {c : Cert} {r : Scope}
    (hr : reach s c = some r) (hK : r.mem K) : Holds K s := by
  cases c with
  | ideal field qs m k => exact reach_ideal_sound hr hK
  | point field vs => exact reach_point_sound hr hK
  | proper field a b => exact reach_proper_sound hr hK
  | cover t => exact reach_cover_sound hr hK

/-- An accepted receipt check: the statement holds throughout the requested scope. -/
theorem check_sound {s : Stmt} {scope : Scope} {c : Cert} {r : Scope}
    (h : check s scope c = .accepted r) (hK : scope.mem K) : Holds K s := by
  unfold check at h
  split_ifs at h
  cases hr : reach s c with
  | none =>
    simp only [hr] at h
    split at h <;> (try split_ifs at h) <;> (try split at h) <;> simp_all
  | some r' =>
    simp only [hr] at h
    split_ifs at h with hle
    exact reach_sound hr (Scope.le_den hle hK)

end GPBinding.Admission

end
