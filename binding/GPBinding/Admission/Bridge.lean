import GPBinding.Admission.Good
import GPBinding.Admission.Arith
import HexMvPolyMathlib

/-!
From the executable checkers to Mathlib polynomials over ℚ, through `HexMvPolyMathlib`'s
correspondence `toMvPolynomial` (Addendum A §3.3).
-/

noncomputable section

namespace GPBinding.Admission
open GPProfile Hex HexMvPolyMathlib

/-- The meaning of a sparse rational polynomial in arity `n`. -/
def meaning (n : ℕ) (p : Sparse) : MvPolynomial (Fin n) Rat :=
  match toHexQ n p with
  | some P => toMvPolynomial P
  | none => 0

theorem meaning_of {n : ℕ} {p : Sparse} {P : GPProfile.P n Rat} (h : toHexQ n p = some P) :
    meaning n p = toMvPolynomial P := by
  simp [meaning, h]

/-! ## `Option` `mapM` -/

theorem mapM_forall₂ {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → List.Forall₂ (fun a b => f a = some b) l l'
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact .nil
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨b, hb, l'', hl, rfl⟩ := h
    exact .cons hb (mapM_forall₂ hl)

theorem map_meaning_of_forall₂ {n : ℕ} :
    ∀ {ps : List Sparse} {Ps : List (GPProfile.P n Rat)},
      List.Forall₂ (fun a b => toHexQ n a = some b) ps Ps →
        Ps.map toMvPolynomial = ps.map (meaning n)
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hab rest => by simp [meaning_of hab, map_meaning_of_forall₂ rest]

theorem map_meaning {n : ℕ} {ps : List Sparse} {Ps : List (GPProfile.P n Rat)}
    (h : ps.mapM (toHexQ n) = some Ps) : Ps.map toMvPolynomial = ps.map (meaning n) :=
  map_meaning_of_forall₂ (mapM_forall₂ h)

/-! ## `toMvPolynomial` over lists -/

theorem toMv_list_sum {n : ℕ} (l : List (GPProfile.P n Rat)) :
    toMvPolynomial l.sum = (l.map toMvPolynomial).sum := by
  induction l with
  | nil => simp
  | cons P l ih => simp [ih]

theorem toMv_list_prod {n : ℕ} (l : List (GPProfile.P n Rat)) :
    toMvPolynomial l.prod = (l.map toMvPolynomial).prod := by
  induction l with
  | nil => simp
  | cons P l ih => simp [ih]

theorem toMv_zipWith_mul {n : ℕ} :
    ∀ (Q E : List (GPProfile.P n Rat)),
      (List.zipWith (· * ·) Q E).map toMvPolynomial =
        List.zipWith (· * ·) (Q.map toMvPolynomial) (E.map toMvPolynomial)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | q :: Q, e :: E => by simp [toMv_zipWith_mul Q E]

/-! ## The residual -/

theorem residual_meaning {n : ℕ} {s : Stmt} {qs : List Sparse} {h : Sparse} {m k : ℕ}
    {R : GPProfile.P n Rat} (hR : residual n s qs h m k = some R) :
    qs.length = s.eqs.length ∧
      toMvPolynomial R =
        (List.zipWith (· * ·) (qs.map (meaning n)) (s.eqs.map (meaning n))).sum -
          meaning n h ^ m * (s.guards.map (meaning n)).prod ^ k := by
  unfold residual at hR
  cases hE : s.eqs.mapM (toHexQ n) <;> cases hG : s.guards.mapM (toHexQ n) <;>
    cases hQ : qs.mapM (toHexQ n) <;> cases hH : toHexQ n h <;> simp only [hE, hG, hQ, hH] at hR <;>
    try contradiction
  rename_i E G Q H
  have lenQ := (mapM_forall₂ hQ).length_eq
  have lenE := (mapM_forall₂ hE).length_eq
  split_ifs at hR with hlen hk <;> simp only [Option.some.injEq] at hR <;>
    subst hR <;> simp only [beq_iff_eq] at hlen <;> refine ⟨by omega, ?_⟩ <;>
    rw [← map_meaning hE, ← map_meaning hQ, ← map_meaning hG, meaning_of hH] <;>
    simp [toMv_list_sum, toMv_list_prod, hk]

/-! ## Point values -/

theorem eval_toHex {n : ℕ} (x : Fin n → Rat) (P : GPProfile.P n Rat) :
    MvPoly.eval x P = MvPolynomial.eval x (toMvPolynomial P) := by
  rw [← aeval_eq_eval, aeval_apply]
  exact congrArg (fun f : MvPolynomial (Fin n) Rat →+* Rat => f (toMvPolynomial P))
    (MvPolynomial.coe_aeval_eq_eval x)

theorem map_eval_of_forall₂ {n : ℕ} (x : Fin n → Rat) :
    ∀ {ps : List Sparse} {Ps : List (GPProfile.P n Rat)},
      List.Forall₂ (fun a b => toHexQ n a = some b) ps Ps →
        Ps.map (MvPoly.eval x) = ps.map (fun e => MvPolynomial.eval x (meaning n e))
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hab rest => by
    simp [meaning_of hab, eval_toHex, map_eval_of_forall₂ x rest]

theorem pointValues_meaning {n : ℕ} {s : Stmt} {values : List Rat} {ev gv : List Rat}
    (hv : pointValues n s values = some (ev, gv)) :
    ev = s.eqs.map (fun e => MvPolynomial.eval (pointFn values n) (meaning n e)) ∧
      gv = s.guards.map (fun g => MvPolynomial.eval (pointFn values n) (meaning n g)) := by
  unfold pointValues at hv
  cases hE : s.eqs.mapM (toHexQ n) <;> cases hG : s.guards.mapM (toHexQ n) <;>
    simp only [hE, hG, Option.bind_eq_bind, Option.bind_some, Option.bind_none, Option.pure_def,
      reduceCtorEq] at hv
  rename_i E G
  simp only [Option.some.injEq, Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl⟩ := hv
  exact ⟨map_eval_of_forall₂ _ (mapM_forall₂ hE), map_eval_of_forall₂ _ (mapM_forall₂ hG)⟩

/-! ## Good coefficients -/

theorem foldl_add_mem {α : Type} {S : Subring Rat} :
    ∀ (l : List (α × Rat)) (a : Rat), a ∈ S → (∀ t ∈ l, t.2 ∈ S) →
      l.foldl (fun acc t => acc + t.2) a ∈ S
  | [], _, h, _ => h
  | t :: l, _, h, hl => foldl_add_mem l _ (S.add_mem h (hl t List.mem_cons_self))
      fun u hu => hl u (List.mem_cons_of_mem _ hu)

theorem terms_coeffs {n : ℕ} :
    ∀ {p : Sparse} {ts : List (Mono n × Rat)},
      List.Forall₂ (fun a b => ((mono? n a.1).bind fun x => some (x, a.2)) = some b) p ts →
        ∀ t ∈ ts, ∃ u ∈ p, t.2 = u.2
  | [], [], .nil, _, ht => by simp at ht
  | a :: _, b :: _, .cons hab rest, t, ht => by
    rcases List.mem_cons.mp ht with rfl | hl
    · refine ⟨a, List.mem_cons_self, ?_⟩
      cases hma : mono? n a.1 <;> simp [hma] at hab
      rw [← hab]
    · obtain ⟨u, hu, e⟩ := terms_coeffs rest t hl
      exact ⟨u, List.mem_cons_of_mem _ hu, e⟩

theorem meaning_good {K : Type*} [Field K] {n : ℕ} {p : Sparse}
    (hp : ∀ c ∈ p.coeffs, c ∈ Good K) : meaning n p ∈ GoodPoly K (Fin n) := by
  cases h : toHexQ n p with
  | none => simp [meaning, h, (GoodPoly K (Fin n)).zero_mem]
  | some P =>
    rw [meaning_of h, mem_goodPoly]
    intro d
    obtain ⟨m, rfl⟩ := (monoEquiv (n := n)).surjective d
    rw [coeff_toMvPolynomial]
    simp only [toHexQ, toHex, Option.bind_eq_bind, Option.pure_def] at h
    cases hts : p.mapM (fun x => (mono? n x.1).bind fun a => some (a, x.2)) with
    | none => simp [hts] at h
    | some ts =>
      simp only [hts, Option.bind_some, Option.some.injEq] at h
      subst h
      rw [MvPoly.coeff_ofTerms]
      apply foldl_add_mem _ _ (Good K).zero_mem
      intro t ht
      obtain ⟨u, hu, hut⟩ := terms_coeffs (mapM_forall₂ hts) t (List.mem_of_mem_filter ht)
      rw [hut]
      exact hp _ (List.mem_map.mpr ⟨u, hu, rfl⟩)

end GPBinding.Admission

end
