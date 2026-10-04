import GPBinding.Admission.Profile
import GPBinding.Binder.Elab
import GPProfile.Rules
import GP50.CoverProofs

/-!
Soundness of the K3 rules R1–R4 and their C4 relation certificates (post-G2 §3.4): when a rule
instance is accepted, the premises' meanings give the conclusion's meaning in every field of the
conclusion scope. These proofs are the direction tables.
-/

noncomputable section

namespace GPBinding.Admission
open GPProfile MvPolynomial HexMvPolyMathlib

variable {K : Type*} [Field K]

/-! ## Scope meets and certificate obligations -/

theorem reachAll_each {obs : List (Stmt × Cert)} {rr : Scope} (h : reachAll obs = some rr)
    (hK : rr.mem K) : ∀ o ∈ obs, ∃ r, reach o.1 o.2 = some r ∧ r.mem K := by
  unfold reachAll at h
  cases hm : obs.mapM (fun o => reach o.1 o.2) with
  | none => simp [hm] at h
  | some rs =>
    simp only [hm, Option.map_some, Option.some.injEq] at h
    subst h
    intro o ho
    obtain ⟨r, hr, hreach⟩ := forall₂_exists_right (mapM_forall₂ hm) o ho
    exact ⟨r, hreach, (foldl_meet_den rs Scope.all hK).2 r hr⟩

theorem reachAll_sound {obs : List (Stmt × Cert)} {rr : Scope} (h : reachAll obs = some rr)
    (hK : rr.mem K) : ∀ o ∈ obs, Holds K o.1 := fun o ho =>
  let ⟨_, hreach, hr⟩ := reachAll_each h hK o ho
  reach_sound hreach hr

/-! ## Scopes that avoid primes -/

theorem avoids_mem {sc : Scope} {bad : List ℕ} (h : sc.avoids bad = true) (hK : sc.mem K) :
    Avoids K bad := by
  rcases hK with ⟨h0, -⟩ | ⟨hp, hm⟩
  · exact Or.inl h0
  · right
    refine ⟨hp, fun hb => ?_⟩
    obtain ⟨c0, ps⟩ := sc
    cases ps with
    | finite ps =>
      simp only [Scope.avoids, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
        Bool.not_true, List.contains_iff_mem] at h
      rcases h _ hm with h' | h'
      · exact absurd ((isPrime_iff _).mpr hp) (by simp [h'])
      · simp_all
    | cofinite e =>
      simp only [Scope.avoids, List.all_eq_true, List.contains_iff_mem] at h
      exact hm (h _ hb)

/-! ## Evaluation kills the ideal of the equations -/

theorem eval_span_zero {n : ℕ} {x : Fin n → K} {l : List (MvPolynomial (Fin n) K)}
    {f : MvPolynomial (Fin n) K} (hf : f ∈ Ideal.span {g | g ∈ l}) (hl : ∀ g ∈ l, eval x g = 0) :
    eval x f = 0 := by
  have hle : Ideal.span {g | g ∈ l} ≤ RingHom.ker (eval x) :=
    Ideal.span_le.mpr fun g hg => (RingHom.mem_ker).mpr (hl g hg)
  exact (RingHom.mem_ker).mp (hle hf)

theorem eval_guards_ne_zero {s : Stmt} {x : Fin s.vars.length → K} (hx : Locus (K := K) s x) :
    eval x (s.guards.map fun g => toK (K := K) (meaning s.vars.length g)).prod ≠ 0 :=
  eval_prod_ne_zero x _ fun b hb => by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hb
    exact hx.2 g hg

theorem eval_eqs_zero {s : Stmt} {x : Fin s.vars.length → K} (hx : Locus (K := K) s x) :
    ∀ b ∈ s.eqs.map (fun e => toK (K := K) (meaning s.vars.length e)), eval x b = 0 := by
  intro b hb
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
  exact hx.1 e he

/-! ## R1: IN_IDEAL(h) ⇒ VANISHES_ON(h) -/

theorem r1_sound {P C : Stmt} {r : Scope} (h : ruleReach C [P] .r1 = some r) (hP : Holds K P) :
    Holds K C := by
  obtain ⟨vP, eP, gP, kP⟩ := P
  obtain ⟨vC, eC, gC, kC⟩ := C
  simp only [ruleReach] at h
  cases kP <;> cases kC <;> simp only at h <;> try contradiction
  rename_i hP' hC'
  split_ifs at h with hs
  simp only [sameSystem, Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hs
  obtain ⟨k, hk⟩ := hP
  intro x hx
  have h0 := eval_span_zero hk (eval_eqs_zero hx)
  rw [map_mul, map_pow] at h0
  rcases mul_eq_zero.mp h0 with hv | hv
  · exact hv
  · exact absurd (pow_eq_zero_iff'.mp hv).1 (eval_guards_ne_zero hx)

/-! ## Bridge: a witness point refutes ideal membership -/

theorem witness_sound {P C : Stmt} {r : Scope} (h : ruleReach C [P] .witness = some r)
    (hP : Holds K P) : Holds K C := by
  obtain ⟨vP, eP, gP, kP⟩ := P
  obtain ⟨vC, eC, gC, kC⟩ := C
  simp only [ruleReach] at h
  cases kP <;> cases kC <;> simp only at h <;> try contradiction
  rename_i hC
  split_ifs at h with hs
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hs
  obtain ⟨⟨rfl, rfl⟩, hg⟩ := hs
  obtain ⟨x, hxe, hxg⟩ := hP
  rintro ⟨k, hk⟩
  have h0 := eval_span_zero hk fun b hb => by
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hb
    exact hxe e' he'
  rw [map_mul, map_pow] at h0
  rcases mul_eq_zero.mp h0 with hv | hv
  · rcases hg with rfl | ⟨rfl, rfl⟩
    · exact hxg _ (List.mem_append_right _ (List.mem_singleton_self _)) hv
    · rw [GPBinding.Binder.toK_meaning_one, map_one] at hv
      exact one_ne_zero hv
  · refine (eval_prod_ne_zero x _ fun b hb => ?_) (pow_eq_zero_iff'.mp hv).1
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hb
    rcases hg with rfl | ⟨rfl, -⟩
    · exact hxg g' (List.mem_append_left _ hg')
    · exact hxg g' hg'

/-! ## R4 generalized: a COVER premise and per-branch claims -/

theorem cover_rule_sound {P C : Stmt} {Qs : List Stmt} {r : Scope}
    (h : ruleReach C (P :: Qs) .byCover = some r) (hP : Holds K P) (hQ : ∀ Q ∈ Qs, Holds K Q) :
    Holds K C := by
  obtain ⟨vP, eP, gP, kP⟩ := P
  obtain ⟨vC, eC, gC, kC⟩ := C
  simp only [ruleReach] at h
  cases kP with
  | cover bs =>
    simp only at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, sameSystem, beq_iff_eq, List.all_eq_true] at hc
    obtain ⟨⟨⟨hk, ⟨⟨rfl, rfl⟩, rfl⟩⟩, hlen⟩, hall⟩ := hc
    have hcov : ∀ x, Locus (K := K) (⟨vP, eP, gP, kC⟩ : Stmt) x → ∃ b ∈ bs,
        (⟨vP, eP ++ b.1, gP ++ b.2, kC⟩ : Stmt) ∈ Qs ∧
          Locus (K := K) (⟨vP, eP ++ b.1, gP ++ b.2, kC⟩ : Stmt) x := by
      intro x hx
      obtain ⟨b, hb, hbe, hbg⟩ := hP x hx
      obtain ⟨Q, hbQ⟩ := mem_zip_of_mem hlen.symm hb
      have hQe := hall _ hbQ
      simp only [beq_iff_eq] at hQe
      refine ⟨b, hb, hQe ▸ (List.of_mem_zip hbQ).2, fun e he => ?_, fun g hg => ?_⟩
      · rcases List.mem_append.mp he with he | he
        · exact hx.1 e he
        · exact hbe e he
      · rcases List.mem_append.mp hg with hg | hg
        · exact hx.2 g hg
        · exact hbg g hg
    cases kC with
    | empty =>
      intro x hx
      obtain ⟨b, -, hQm, hxQ⟩ := hcov x hx
      exact hQ _ hQm x hxQ
    | vanishesOn f =>
      intro x hx
      obtain ⟨b, -, hQm, hxQ⟩ := hcov x hx
      exact hQ _ hQm x hxQ
    | _ => simp at hk
  | _ => simp at h

/-! ## R4: object cover by a structural split -/

theorem r4_sound {B₁ B₂ C : Stmt} {h : Sparse} {r : Scope}
    (hr : ruleReach C [B₁, B₂] (.split h) = some r) (h₁ : Holds K B₁) (h₂ : Holds K B₂) :
    Holds K C := by
  simp only [ruleReach] at hr
  split_ifs at hr with hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hkind, rfl⟩, rfl⟩ := hc
  obtain ⟨v, e, g, k⟩ := C
  have split : ∀ x, Locus (K := K) ⟨v, e, g, k⟩ x →
      Locus (K := K) ⟨v, e ++ [h], g, k⟩ x ∨ Locus (K := K) ⟨v, e, g ++ [h], k⟩ x := by
    intro x ⟨he, hg⟩
    by_cases hv : value v.length h x = 0
    · left
      refine ⟨fun e' he' => ?_, hg⟩
      rcases List.mem_append.mp he' with he' | he'
      · exact he e' he'
      · rw [List.mem_singleton.mp he']; exact hv
    · right
      refine ⟨he, fun g' hg' => ?_⟩
      rcases List.mem_append.mp hg' with hg' | hg'
      · exact hg g' hg'
      · rw [List.mem_singleton.mp hg']; exact hv
  cases k with
  | empty =>
    intro x hx
    rcases split x hx with hx | hx
    · exact h₁ x hx
    · exact h₂ x hx
  | vanishesOn f =>
    intro x hx
    rcases split x hx with hx | hx
    · exact h₁ x hx
    · exact h₂ x hx
  | nonempty => simp at hkind
  | inIdeal _ => simp at hkind
  | notInIdeal _ | cover _ => simp at hkind

/-! ## C4 inclusion: the tight locus lies in the loose locus -/

/-! ### Ideal transport (G3a review §3), in any commutative ring -/

theorem uniform_pow {R : Type*} [CommRing R] {I : Ideal R} {G : R} :
    ∀ E : List R, (∀ e ∈ E, ∃ k, e * G ^ k ∈ I) → ∃ N, ∀ e ∈ E, e * G ^ N ∈ I
  | [], _ => ⟨0, by simp⟩
  | e :: E, h => by
    obtain ⟨k, hk⟩ := h e List.mem_cons_self
    obtain ⟨N, hN⟩ := uniform_pow E fun e' he' => h e' (List.mem_cons_of_mem _ he')
    refine ⟨k + N, fun e' he' => ?_⟩
    rcases List.mem_cons.mp he' with rfl | he'
    · rw [pow_add, ← mul_assoc]; exact I.mul_mem_right _ hk
    · rw [add_comm, pow_add, ← mul_assoc]; exact I.mul_mem_right _ (hN e' he')

theorem span_mul_mem {R : Type*} [CommRing R] {S : Set R} {I : Ideal R} {c : R}
    (h : ∀ s ∈ S, s * c ∈ I) {f : R} (hf : f ∈ Ideal.span S) : f * c ∈ I := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact I.add_mem hx hy
  | smul a x _ hx => rw [smul_eq_mul, mul_assoc]; exact I.mul_mem_left a hx

theorem guards_unit {R : Type*} [CommRing R] {I : Ideal R} {G : R} :
    ∀ Gs : List R, (∀ g ∈ Gs, ∃ k a, G ^ k - a * g ∈ I) → ∃ M Q, G ^ M - Gs.prod * Q ∈ I
  | [], _ => ⟨0, 1, by simp⟩
  | g :: Gs, h => by
    obtain ⟨k, a, hk⟩ := h g List.mem_cons_self
    obtain ⟨M, Q, hM⟩ := guards_unit Gs fun g' hg' => h g' (List.mem_cons_of_mem _ hg')
    refine ⟨k + M, a * Q, ?_⟩
    have e : G ^ (k + M) - (g :: Gs).prod * (a * Q) =
        G ^ k * (G ^ M - Gs.prod * Q) + Gs.prod * Q * (G ^ k - a * g) := by
      simp only [List.prod_cons]; ring
    rw [e]
    exact I.add_mem (I.mul_mem_left _ hM) (I.mul_mem_left _ hk)

/-- If the loose equations `E` vanish and the loose guards `Gs` are units in `R[1/G]/I`, then
`h·(∏ Gs)^k ∈ ⟨E⟩` puts `h·G^j` in `I`. -/
theorem ideal_transport {R : Type*} [CommRing R] {I : Ideal R} {G h : R} {E Gs : List R}
    (hE : ∀ e ∈ E, ∃ k, e * G ^ k ∈ I) (hG : ∀ g ∈ Gs, ∃ k a, G ^ k - a * g ∈ I)
    (hP : ∃ k, h * Gs.prod ^ k ∈ Ideal.span {f | f ∈ E}) : ∃ k, h * G ^ k ∈ I := by
  obtain ⟨N, hN⟩ := uniform_pow E hE
  obtain ⟨M, Q, hM⟩ := guards_unit Gs hG
  obtain ⟨k₀, hk₀⟩ := hP
  have h1 : h * Gs.prod ^ k₀ * G ^ N ∈ I := span_mul_mem (fun e he => hN e he) hk₀
  have h2 : (G ^ M) ^ k₀ - (Gs.prod * Q) ^ k₀ ∈ I := by
    rw [← Ideal.Quotient.eq] at hM ⊢
    simp only [map_pow] at hM ⊢
    rw [hM]
  refine ⟨M * k₀ + N, ?_⟩
  have e : h * G ^ (M * k₀ + N) =
      h * G ^ N * ((G ^ M) ^ k₀ - (Gs.prod * Q) ^ k₀) + Q ^ k₀ * (h * Gs.prod ^ k₀ * G ^ N) := by
    rw [pow_add, pow_mul]; ring
  rw [e]
  exact I.add_mem (I.mul_mem_left _ h2) (I.mul_mem_left _ h1)

theorem span_append_single {R : Type*} [CommRing R] {E : List R} {y x : R}
    (hx : x ∈ Ideal.span {f | f ∈ E ++ [y]}) : ∃ a, x - a * y ∈ Ideal.span {f | f ∈ E} := by
  have hset : {f | f ∈ E ++ [y]} = insert y {f | f ∈ E} := by
    ext f; simp [or_comm]
  rw [hset, Ideal.mem_span_insert] at hx
  obtain ⟨a, z, hz, rfl⟩ := hx
  exact ⟨a, by simpa using hz⟩

/-- If the loose equations `E` are nilpotent and the loose guards `Gs` units in `R[1/G]/I`, then
`(∏ Gs)^k ∈ ⟨E⟩` makes the localized quotient the zero ring: a power of `G` lies in `I`. -/
theorem radical_transport {R : Type*} [CommRing R] {I : Ideal R} {G : R} {E Gs : List R}
    (hE : ∀ e ∈ E, ∃ m k, e ^ m * G ^ k ∈ I) (hG : ∀ g ∈ Gs, ∃ k a, G ^ k - a * g ∈ I)
    (hL : ∃ k, Gs.prod ^ k ∈ Ideal.span {f | f ∈ E}) : ∃ j, G ^ j ∈ I := by
  obtain ⟨M, Q, hM⟩ := guards_unit Gs hG
  obtain ⟨k₀, hk₀⟩ := hL
  have hrad : ∀ e ∈ E, e * G ∈ I.radical := by
    intro e he
    obtain ⟨m, k, hmk⟩ := hE e he
    refine ⟨m + k, ?_⟩
    have e' : (e * G) ^ (m + k) = e ^ m * G ^ k * (e ^ k * G ^ m) := by ring
    rw [e']
    exact I.mul_mem_right _ hmk
  obtain ⟨n, hn⟩ : Gs.prod ^ k₀ * G ∈ I.radical := span_mul_mem hrad hk₀
  have h2 : (G ^ M) ^ (k₀ * n) - (Gs.prod * Q) ^ (k₀ * n) ∈ I := by
    rw [← Ideal.Quotient.eq] at hM ⊢
    simp only [map_pow] at hM ⊢
    rw [hM]
  refine ⟨M * (k₀ * n) + n, ?_⟩
  have e : G ^ (M * (k₀ * n) + n) = G ^ n * ((G ^ M) ^ (k₀ * n) - (Gs.prod * Q) ^ (k₀ * n)) +
      Q ^ (k₀ * n) * (Gs.prod ^ k₀ * G) ^ n := by
    rw [pow_add, pow_mul]; ring
  rw [e]
  exact I.add_mem (I.mul_mem_left _ h2) (I.mul_mem_left _ hn)

/-- The C4 inclusion obligations, read at the ideal level in `K`. -/
theorem inclusion_ideal_facts {T L : Stmt} {eqCerts guardCerts : List Cert}
    {obs : List (Stmt × Cert)} {rr : Scope}
    (h : inclusionObligations T L eqCerts guardCerts = some obs) (hr : reachAll obs = some rr)
    (hK : rr.mem K) :
    T.vars = L.vars ∧
      (∀ e ∈ L.eqs, ∃ m k, toK (K := K) (meaning T.vars.length e) ^ m *
          (T.guards.map fun g => toK (K := K) (meaning T.vars.length g)).prod ^ k ∈
        Ideal.span {f | f ∈ T.eqs.map fun e => toK (K := K) (meaning T.vars.length e)}) ∧
      (∀ g ∈ L.guards, ∃ k a, (T.guards.map fun g => toK (K := K) (meaning T.vars.length g)).prod ^ k -
          a * toK (K := K) (meaning T.vars.length g) ∈
        Ideal.span {f | f ∈ T.eqs.map fun e => toK (K := K) (meaning T.vars.length e)}) := by
  unfold inclusionObligations at h
  split_ifs at h with hc
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at hc
  obtain ⟨⟨hv, he⟩, hg⟩ := hc
  simp only [Option.some.injEq] at h
  subst h
  refine ⟨hv, fun e heq => ?_, fun g hgm => ?_⟩
  · obtain ⟨c, hc⟩ := mem_zip_of_mem he.symm heq
    obtain ⟨r, hreach, hrK⟩ :=
      reachAll_each hr hK _ (List.mem_append_left _ (List.mem_map.mpr ⟨(e, c), hc, rfl⟩))
    obtain ⟨m, k, hk⟩ := reach_vanishes_ideal (s := ⟨T.vars, T.eqs, T.guards, .vanishesOn e⟩) rfl hreach hrK
    exact ⟨m, k, hk⟩
  · obtain ⟨c, hc⟩ := mem_zip_of_mem hg.symm hgm
    obtain ⟨r, hreach, hrK⟩ :=
      reachAll_each hr hK _ (List.mem_append_right _ (List.mem_map.mpr ⟨(g, c), hc, rfl⟩))
    obtain ⟨k, hk⟩ := reach_empty_ideal rfl hreach hrK
    simp only [List.map_append, List.map_cons, List.map_nil] at hk
    obtain ⟨a, ha⟩ := span_append_single hk
    exact ⟨k, a, ha⟩

theorem idealInclusion_facts {T L : Stmt} {eqCerts guardCerts : List Cert}
    {obs : List (Stmt × Cert)} {rr : Scope}
    (h : idealInclusionObligations T L eqCerts guardCerts = some obs) (hr : reachAll obs = some rr)
    (hK : rr.mem K) :
    T.vars = L.vars ∧
      (∀ e ∈ L.eqs, ∃ k, toK (K := K) (meaning T.vars.length e) *
          (T.guards.map fun g => toK (K := K) (meaning T.vars.length g)).prod ^ k ∈
        Ideal.span {f | f ∈ T.eqs.map fun e => toK (K := K) (meaning T.vars.length e)}) ∧
      (∀ g ∈ L.guards, ∃ k a, (T.guards.map fun g => toK (K := K) (meaning T.vars.length g)).prod ^ k -
          a * toK (K := K) (meaning T.vars.length g) ∈
        Ideal.span {f | f ∈ T.eqs.map fun e => toK (K := K) (meaning T.vars.length e)}) := by
  unfold idealInclusionObligations at h
  split_ifs at h with hc
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at hc
  obtain ⟨⟨hv, he⟩, hg⟩ := hc
  simp only [Option.some.injEq] at h
  subst h
  refine ⟨hv, fun e heq => ?_, fun g hgm => ?_⟩
  · obtain ⟨c, hc⟩ := mem_zip_of_mem he.symm heq
    exact reachAll_sound hr hK _ (List.mem_append_left _ (List.mem_map.mpr ⟨(e, c), hc, rfl⟩))
  · obtain ⟨c, hc⟩ := mem_zip_of_mem hg.symm hgm
    obtain ⟨r, hreach, hrK⟩ :=
      reachAll_each hr hK _ (List.mem_append_right _ (List.mem_map.mpr ⟨(g, c), hc, rfl⟩))
    obtain ⟨k, hk⟩ := reach_empty_ideal rfl hreach hrK
    simp only [List.map_append, List.map_cons, List.map_nil] at hk
    obtain ⟨a, ha⟩ := span_append_single hk
    exact ⟨k, a, ha⟩

/-! ## R2: inclusion, by the direction table -/

theorem r2_sound {P C : Stmt} {eqCerts guardCerts : List Cert} {r : Scope}
    (h : ruleReach C [P] (.inclusion eqCerts guardCerts) = some r) (hK : r.mem K)
    (hP : Holds K P) : Holds K C := by
  obtain ⟨vP, eP, gP, kP⟩ := P
  obtain ⟨vC, eC, gC, kC⟩ := C
  simp only [ruleReach] at h
  have hk : kP = kC := by
    by_contra hne
    simp [hne] at h
  subst hk
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false] at h
  cases kP with
  | cover _ => simp at h
  | notInIdeal f =>
    simp only at h
    split_ifs at h with hone
    cases ho : inclusionObligations ⟨vP, eP, gP, .notInIdeal f⟩ ⟨vC, eC, gC, .notInIdeal f⟩
        eqCerts guardCerts with
    | none => simp [ho] at h
    | some obs =>
      simp only [ho, Option.bind_some] at h
      obtain ⟨hv, hE, hG⟩ := inclusion_ideal_facts ho h hK
      simp only at hv hE hG
      subst hv
      simp only [beq_iff_eq] at hone
      subst hone
      rintro ⟨k, hk⟩
      rw [GPBinding.Binder.toK_meaning_one, one_mul] at hk
      apply hP
      obtain ⟨j, hj⟩ := radical_transport (E := eC.map fun e => toK (K := K) (meaning vP.length e))
        (Gs := gC.map fun g => toK (K := K) (meaning vP.length g))
        (fun e he => by obtain ⟨e', he', rfl⟩ := List.mem_map.mp he; exact hE e' he')
        (fun g hg => by obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg; exact hG g' hg') ⟨k, hk⟩
      exact ⟨j, by rw [GPBinding.Binder.toK_meaning_one, one_mul]; exact hj⟩
  | empty =>
    cases ho : inclusionObligations ⟨vC, eC, gC, .empty⟩ ⟨vP, eP, gP, .empty⟩ eqCerts guardCerts with
    | none => simp [ho] at h
    | some obs =>
      simp only [ho, Option.bind_some] at h
      obtain ⟨hv, hloc⟩ := inclusion_locus ho (reachAll_sound h hK)
      simp only at hv
      subst hv
      intro x hx
      exact hP x (hloc x hx)
  | vanishesOn f =>
    cases ho : inclusionObligations ⟨vC, eC, gC, .vanishesOn f⟩ ⟨vP, eP, gP, .vanishesOn f⟩
        eqCerts guardCerts with
    | none => simp [ho] at h
    | some obs =>
      simp only [ho, Option.bind_some] at h
      obtain ⟨hv, hloc⟩ := inclusion_locus ho (reachAll_sound h hK)
      simp only at hv
      subst hv
      intro x hx
      exact hP x (hloc x hx)
  | nonempty =>
    cases ho : inclusionObligations ⟨vP, eP, gP, .nonempty⟩ ⟨vC, eC, gC, .nonempty⟩
        eqCerts guardCerts with
    | none => simp [ho] at h
    | some obs =>
      simp only [ho, Option.bind_some] at h
      obtain ⟨hv, hloc⟩ := inclusion_locus ho (reachAll_sound h hK)
      simp only at hv
      subst hv
      obtain ⟨x, hx⟩ := hP
      exact ⟨x, hloc x hx⟩
  | inIdeal f =>
    cases ho : idealInclusionObligations ⟨vC, eC, gC, .inIdeal f⟩ ⟨vP, eP, gP, .inIdeal f⟩
        eqCerts guardCerts with
    | none => simp [ho] at h
    | some obs =>
      simp only [ho, Option.bind_some] at h
      obtain ⟨hv, hE, hG⟩ := idealInclusion_facts ho h hK
      simp only at hv hE hG
      subst hv
      refine ideal_transport (E := eP.map fun e => toK (K := K) (meaning vC.length e))
        (Gs := gP.map fun g => toK (K := K) (meaning vC.length g)) ?_ ?_ hP
      · intro e he
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        exact hE e' he'
      · intro g hg
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        exact hG g' hg'

/-! ## Composition (R3) -/

theorem toK_bind₁ {σ τ : Type*} (f : σ → MvPolynomial τ Rat) (P : MvPolynomial σ Rat)
    (hf : ∀ i, f i ∈ GoodPoly K τ) (hP : P ∈ GoodPoly K σ) :
    toK (K := K) (bind₁ f P) = bind₁ (fun i => toK (K := K) (f i)) (toK P) := by
  choose f' hf' using hf
  obtain ⟨P', rfl, -⟩ := toK_lift hP
  have hfeq : f = fun i => MvPolynomial.map (Good K).subtype (f' i) := funext fun i => (hf' i).symm
  rw [hfeq, ← map_bind₁, toK_map, map_bind₁, toK_map]
  congr 2
  funext i
  exact (toK_map (f' i)).symm

theorem eval_bind₁ {σ τ : Type*} (x : τ → K) (g : σ → MvPolynomial τ K) (Q : MvPolynomial σ K) :
    eval x (bind₁ g Q) = eval (fun i => eval x (g i)) Q := by
  have := eval₂Hom_bind₁ (RingHom.id K) x g Q
  simpa [coe_eval₂Hom] using this

theorem compose_meaning {nS nT : ℕ} {phi : List Sparse} {p q : Sparse}
    (h : compose nS phi nT p = some q) :
    phi.length = nT ∧ meaning nS q =
      bind₁ (fun i : Fin nT => meaning nS (phi.getD i.val [])) (meaning nT p) := by
  unfold compose at h
  cases hg : phi.mapM (toHexQ nS) with
  | none => simp [hg] at h
  | some gs =>
    simp only [hg, Option.bind_eq_bind, Option.bind_some] at h
    split_ifs at h with hl
    simp only [bne_iff_ne, ne_eq, not_not] at hl
    cases hq : toHexQ nT p with
    | none => simp [hq] at h
    | some Q =>
      simp only [hq, Option.bind_some] at h
      split_ifs at h with hrt
      simp only [Option.some.injEq] at h
      subst h
      have F := mapM_forall₂ hg
      refine ⟨F.length_eq ▸ hl, ?_⟩
      rw [meaning_of (beq_iff_eq.mp hrt)]
      refine (toMvPolynomial_subst (R := Rat) (fun i => gs.getD i.val 0) Q).trans ?_
      rw [meaning_of hq]
      congr 2
      funext i
      have hi : i.val < phi.length := F.length_eq ▸ hl ▸ i.2
      have hig : i.val < gs.length := F.length_eq ▸ hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hig,
        List.getElem?_eq_getElem hi, Option.getD_some]
      have := F.get hi hig
      simp only [List.get_eq_getElem] at this
      exact (meaning_of this).symm

/-- Good coefficients for every listed sparse polynomial (in `K`). -/
def GoodAll (K : Type*) [Field K] (ps : List Sparse) : Prop := ∀ p ∈ ps, ∀ c ∈ p.coeffs, c ∈ Good K

/-- Composition in `K`: `p ∘ φ` is the substitution `Ψ = bind₁ φ` applied to `p`. -/
theorem compose_toK {nS nT : ℕ} {phi : List Sparse} {p q : Sparse}
    (h : compose nS phi nT p = some q) (hphi : GoodAll K phi) (hp : ∀ c ∈ p.coeffs, c ∈ Good K) :
    toK (K := K) (meaning nS q) =
      bind₁ (fun i : Fin nT => toK (K := K) (meaning nS (phi.getD i.val []))) (toK (meaning nT p)) := by
  obtain ⟨hl, hm⟩ := compose_meaning h
  have hgood : ∀ i : Fin nT, meaning nS (phi.getD i.val []) ∈ GoodPoly K (Fin nS) := by
    intro i
    apply meaning_good
    have hi : i.val < phi.length := hl ▸ i.2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact hphi _ (List.getElem_mem hi)
  rw [hm, toK_bind₁ _ _ hgood (meaning_good hp)]

theorem compose_value {nS nT : ℕ} {phi : List Sparse} {p q : Sparse}
    (h : compose nS phi nT p = some q) (hphi : GoodAll K phi) (hp : ∀ c ∈ p.coeffs, c ∈ Good K)
    (x : Fin nS → K) :
    value nS q x = value nT p (fun i => value nS (phi.getD i.val []) x) := by
  unfold value
  rw [compose_toK h hphi hp, eval_bind₁]

theorem compose_map_eq {nS nT : ℕ} {phi : List Sparse} (hphi : GoodAll K phi) {ps qs : List Sparse}
    (hF : List.Forall₂ (fun p q => compose nS phi nT p = some q) ps qs) (hg : GoodAll K ps) :
    (ps.map fun p => toK (K := K) (meaning nT p)).map
        (bind₁ (fun i : Fin nT => toK (K := K) (meaning nS (phi.getD i.val [])))) =
      qs.map fun q => toK (K := K) (meaning nS q) := by
  induction hF with
  | nil => rfl
  | cons h _ ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨(compose_toK h hphi (hg _ List.mem_cons_self)).symm,
      ih fun p hp => hg p (List.mem_cons_of_mem _ hp)⟩

theorem image_list {α β : Type*} (f : α → β) (L : List α) : f '' {x | x ∈ L} = {y | y ∈ L.map f} := by
  ext y
  simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_map]

theorem idealMap_facts {S T : Stmt} {phi : List Sparse} {eqCerts guardCerts : List Cert}
    {obs : List (Stmt × Cert)} {rr : Scope}
    (h : idealMapObligations S T phi eqCerts guardCerts = some obs) (hr : reachAll obs = some rr)
    (hK : rr.mem K) :
    ∃ ceqs cgs, T.eqs.mapM (compose S.vars.length phi T.vars.length) = some ceqs ∧
      T.guards.mapM (compose S.vars.length phi T.vars.length) = some cgs ∧
      (∀ e ∈ ceqs, ∃ k, toK (K := K) (meaning S.vars.length e) *
          (S.guards.map fun g => toK (K := K) (meaning S.vars.length g)).prod ^ k ∈
        Ideal.span {f | f ∈ S.eqs.map fun e => toK (K := K) (meaning S.vars.length e)}) ∧
      (∀ g ∈ cgs, ∃ k a, (S.guards.map fun g => toK (K := K) (meaning S.vars.length g)).prod ^ k -
          a * toK (K := K) (meaning S.vars.length g) ∈
        Ideal.span {f | f ∈ S.eqs.map fun e => toK (K := K) (meaning S.vars.length e)}) := by
  unfold idealMapObligations at h
  split_ifs at h with hc
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at hc
  obtain ⟨⟨-, he⟩, hg⟩ := hc
  cases hE : T.eqs.mapM (compose S.vars.length phi T.vars.length) with
  | none => simp [hE] at h
  | some ceqs =>
    cases hG : T.guards.mapM (compose S.vars.length phi T.vars.length) with
    | none => simp [hE, hG] at h
    | some cgs =>
      simp only [hE, hG, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      subst h
      have FE := mapM_forall₂ hE
      have FG := mapM_forall₂ hG
      refine ⟨ceqs, cgs, rfl, rfl, fun e heq => ?_, fun g hgm => ?_⟩
      · obtain ⟨c, hc⟩ := mem_zip_of_mem (FE.length_eq.symm.trans he.symm) heq
        exact reachAll_sound hr hK _ (List.mem_append_left _ (List.mem_map.mpr ⟨(e, c), hc, rfl⟩))
      · obtain ⟨c, hc⟩ := mem_zip_of_mem (FG.length_eq.symm.trans hg.symm) hgm
        obtain ⟨r, hreach, hrK⟩ :=
          reachAll_each hr hK _ (List.mem_append_right _ (List.mem_map.mpr ⟨(g, c), hc, rfl⟩))
        obtain ⟨k, hk⟩ := reach_empty_ideal rfl hreach hrK
        simp only [List.map_append, List.map_cons, List.map_nil] at hk
        obtain ⟨a, ha⟩ := span_append_single hk
        exact ⟨k, a, ha⟩

theorem map_locus {S T : Stmt} {phi : List Sparse} {eqCerts guardCerts : List Cert}
    {obs : List (Stmt × Cert)} (h : mapObligations S T phi eqCerts guardCerts = some obs)
    (hobs : ∀ o ∈ obs, Holds K o.1) (hphi : GoodAll K phi) (hT : GoodAll K (T.eqs ++ T.guards)) :
    ∀ x, Locus (K := K) S x →
      Locus (K := K) T (fun i => value S.vars.length (phi.getD i.val []) x) := by
  unfold mapObligations at h
  split_ifs at h with hc
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at hc
  obtain ⟨⟨-, he⟩, hg⟩ := hc
  cases hE : T.eqs.mapM (compose S.vars.length phi T.vars.length) with
  | none => simp [hE] at h
  | some ceqs =>
    cases hG : T.guards.mapM (compose S.vars.length phi T.vars.length) with
    | none => simp [hE, hG] at h
    | some cgs =>
      simp only [hE, hG, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      subst h
      have FE := mapM_forall₂ hE
      have FG := mapM_forall₂ hG
      intro x hx
      refine ⟨fun e heq => ?_, fun g hgq => ?_⟩
      · obtain ⟨ce, hce, hcomp⟩ := forall₂_exists_right FE e heq
        obtain ⟨c, hc⟩ := mem_zip_of_mem (FE.length_eq.symm.trans he.symm) hce
        have := hobs _ (List.mem_append_left _ (List.mem_map.mpr ⟨(ce, c), hc, rfl⟩))
        rw [← compose_value hcomp hphi (hT e (List.mem_append_left _ heq))]
        exact this x hx
      · obtain ⟨cg, hcg, hcomp⟩ := forall₂_exists_right FG g hgq
        obtain ⟨c, hc⟩ := mem_zip_of_mem (FG.length_eq.symm.trans hg.symm) hcg
        have := hobs _ (List.mem_append_right _ (List.mem_map.mpr ⟨(cg, c), hc, rfl⟩))
        rw [← compose_value hcomp hphi (hT g (List.mem_append_right _ hgq))]
        intro hz
        apply this x
        refine ⟨fun e' he' => ?_, hx.2⟩
        rcases List.mem_append.mp he' with he' | he'
        · exact hx.1 e' he'
        · rw [List.mem_singleton.mp he']; exact hz

/-- The C4 map obligations, read at the ideal level in `K`. -/
theorem map_ideal_facts {S T : Stmt} {phi : List Sparse} {eqCerts guardCerts : List Cert}
    {obs : List (Stmt × Cert)} {rr : Scope}
    (h : mapObligations S T phi eqCerts guardCerts = some obs) (hr : reachAll obs = some rr)
    (hK : rr.mem K) :
    ∃ ceqs cgs, T.eqs.mapM (compose S.vars.length phi T.vars.length) = some ceqs ∧
      T.guards.mapM (compose S.vars.length phi T.vars.length) = some cgs ∧
      (∀ e ∈ ceqs, ∃ m k, toK (K := K) (meaning S.vars.length e) ^ m *
          (S.guards.map fun g => toK (K := K) (meaning S.vars.length g)).prod ^ k ∈
        Ideal.span {f | f ∈ S.eqs.map fun e => toK (K := K) (meaning S.vars.length e)}) ∧
      (∀ g ∈ cgs, ∃ k a, (S.guards.map fun g => toK (K := K) (meaning S.vars.length g)).prod ^ k -
          a * toK (K := K) (meaning S.vars.length g) ∈
        Ideal.span {f | f ∈ S.eqs.map fun e => toK (K := K) (meaning S.vars.length e)}) := by
  unfold mapObligations at h
  split_ifs at h with hc
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at hc
  obtain ⟨⟨-, he⟩, hg⟩ := hc
  cases hE : T.eqs.mapM (compose S.vars.length phi T.vars.length) with
  | none => simp [hE] at h
  | some ceqs =>
    cases hG : T.guards.mapM (compose S.vars.length phi T.vars.length) with
    | none => simp [hE, hG] at h
    | some cgs =>
      simp only [hE, hG, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      subst h
      have FE := mapM_forall₂ hE
      have FG := mapM_forall₂ hG
      refine ⟨ceqs, cgs, rfl, rfl, fun e heq => ?_, fun g hgm => ?_⟩
      · obtain ⟨c, hc⟩ := mem_zip_of_mem (FE.length_eq.symm.trans he.symm) heq
        obtain ⟨r, hreach, hrK⟩ :=
          reachAll_each hr hK _ (List.mem_append_left _ (List.mem_map.mpr ⟨(e, c), hc, rfl⟩))
        obtain ⟨m, k, hk⟩ :=
          reach_vanishes_ideal (s := ⟨S.vars, S.eqs, S.guards, .vanishesOn e⟩) rfl hreach hrK
        exact ⟨m, k, hk⟩
      · obtain ⟨c, hc⟩ := mem_zip_of_mem (FG.length_eq.symm.trans hg.symm) hgm
        obtain ⟨r, hreach, hrK⟩ :=
          reachAll_each hr hK _ (List.mem_append_right _ (List.mem_map.mpr ⟨(g, c), hc, rfl⟩))
        obtain ⟨k, hk⟩ := reach_empty_ideal rfl hreach hrK
        simp only [List.map_append, List.map_cons, List.map_nil] at hk
        obtain ⟨a, ha⟩ := span_append_single hk
        exact ⟨k, a, ha⟩

theorem stmt_good {s : Stmt} (h : Avoids K s.primes) : GoodAll K s.polys :=
  fun p hp c hc => good_of_avoids h (List.mem_flatMap.mpr ⟨p, hp, hc⟩)

theorem polys_eqs_guards {s : Stmt} : ∀ p ∈ s.eqs ++ s.guards, p ∈ s.polys := by
  intro p hp
  simp only [Stmt.polys, List.mem_append] at hp ⊢
  tauto

/-! ## R3: polynomial maps, by the direction table -/

theorem r3_sound {P C : Stmt} {phi : List Sparse} {eqCerts guardCerts : List Cert} {r : Scope}
    (h : ruleReach C [P] (.map phi eqCerts guardCerts) = some r) (hK : r.mem K)
    (hP : Holds K P) (hphi : GoodAll K phi) (hPg : GoodAll K P.polys) (hCg : GoodAll K C.polys) :
    Holds K C := by
  have gP : GoodAll K (P.eqs ++ P.guards) := fun p hp => hPg p (polys_eqs_guards p hp)
  have gC : GoodAll K (C.eqs ++ C.guards) := fun p hp => hCg p (polys_eqs_guards p hp)
  simp only [ruleReach] at h
  split at h
  · -- NONEMPTY: source = premise, target = conclusion.
    rename_i hkP hkC
    cases ho : mapObligations P C phi eqCerts guardCerts with
    | none => simp [ho] at h
    | some obs =>
      simp only [ho, Option.bind_some] at h
      unfold Holds at hP ⊢
      rw [hkP] at hP; rw [hkC]
      obtain ⟨x, hx⟩ := hP
      exact ⟨_, map_locus ho (reachAll_sound h hK) hphi gC x hx⟩
  · -- EMPTY: target = premise, source = conclusion.
    rename_i hkP hkC
    cases ho : mapObligations C P phi eqCerts guardCerts with
    | none => simp [ho] at h
    | some obs =>
      simp only [ho, Option.bind_some] at h
      unfold Holds at hP ⊢
      rw [hkP] at hP; rw [hkC]
      intro x hx
      exact hP _ (map_locus ho (reachAll_sound h hK) hphi gP x hx)
  · -- VANISHES_ON(h) on the target gives VANISHES_ON(h ∘ φ) on the source.
    rename_i f f' hkP hkC
    split_ifs at h with hcomp
    cases ho : mapObligations C P phi eqCerts guardCerts with
    | none => simp [ho] at h
    | some obs =>
      simp only [ho, Option.bind_some] at h
      have hf : ∀ c ∈ f.coeffs, c ∈ Good K :=
        hPg f (by simp [Stmt.polys, hkP, Kind.target?])
      unfold Holds at hP ⊢
      rw [hkP] at hP; rw [hkC]
      intro x hx
      rw [compose_value (beq_iff_eq.mp hcomp) hphi hf]
      exact hP _ (map_locus ho (reachAll_sound h hK) hphi gP x hx)
  · -- NOT_IN_IDEAL(1) moves S → T: were 1 in the target's localized ideal, pushing the identity
    -- through `Ψ = bind₁ φ` would make the source's localized quotient the zero ring.
    rename_i f f' hkP hkC
    split_ifs at h with hone
    simp only [Bool.and_eq_true, beq_iff_eq] at hone
    obtain ⟨rfl, rfl⟩ := hone
    cases ho : mapObligations P C phi eqCerts guardCerts with
    | none => simp [ho] at h
    | some obs =>
      simp only [ho, Option.bind_some] at h
      obtain ⟨ceqs, cgs, hE, hG, hEo, hGo⟩ := map_ideal_facts ho h hK
      unfold Holds at hP ⊢
      rw [hkP] at hP; rw [hkC]
      rintro ⟨k, hk⟩
      rw [GPBinding.Binder.toK_meaning_one, one_mul] at hk
      have hm := Ideal.mem_map_of_mem
        (bind₁ (fun i : Fin C.vars.length => toK (K := K) (meaning P.vars.length (phi.getD i.val [])))) hk
      rw [Ideal.map_span, image_list, map_pow, map_list_prod,
        compose_map_eq hphi (mapM_forall₂ hG) fun p hp => gC p (List.mem_append_right _ hp),
        compose_map_eq hphi (mapM_forall₂ hE) fun p hp => gC p (List.mem_append_left _ hp)] at hm
      have hE' : ∀ e ∈ ceqs.map (fun e => toK (K := K) (meaning P.vars.length e)), ∃ m k,
          e ^ m * (P.guards.map fun g => toK (K := K) (meaning P.vars.length g)).prod ^ k ∈
            Ideal.span {f | f ∈ P.eqs.map fun e => toK (K := K) (meaning P.vars.length e)} := by
        intro e he
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        exact hEo e' he'
      have hG' : ∀ g ∈ cgs.map (fun g => toK (K := K) (meaning P.vars.length g)), ∃ k a,
          (P.guards.map fun g => toK (K := K) (meaning P.vars.length g)).prod ^ k - a * g ∈
            Ideal.span {f | f ∈ P.eqs.map fun e => toK (K := K) (meaning P.vars.length e)} := by
        intro g hg
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        exact hGo g' hg'
      obtain ⟨j, hj⟩ := radical_transport hE' hG' ⟨k, hm⟩
      exact hP ⟨j, by rw [GPBinding.Binder.toK_meaning_one, one_mul]; exact hj⟩
  · -- IN_IDEAL(h) on the target gives IN_IDEAL(h ∘ φ) on the source: push the premise through
    -- `Ψ = bind₁ φ`, then transport as in R2.
    rename_i f f' hkP hkC
    split_ifs at h with hcomp
    cases ho : idealMapObligations C P phi eqCerts guardCerts with
    | none => simp [ho] at h
    | some obs =>
      simp only [ho, Option.bind_some] at h
      have hf : ∀ c ∈ f.coeffs, c ∈ Good K :=
        hPg f (by simp [Stmt.polys, hkP, Kind.target?])
      obtain ⟨ceqs, cgs, hE, hG, hEo, hGo⟩ := idealMap_facts ho h hK
      unfold Holds at hP ⊢
      rw [hkP] at hP; rw [hkC]
      obtain ⟨k₀, hk₀⟩ := hP
      have hm := Ideal.mem_map_of_mem
        (bind₁ (fun i : Fin P.vars.length => toK (K := K) (meaning C.vars.length (phi.getD i.val [])))) hk₀
      rw [Ideal.map_span, image_list, map_mul, map_pow, map_list_prod,
        ← compose_toK (beq_iff_eq.mp hcomp) hphi hf,
        compose_map_eq hphi (mapM_forall₂ hG) fun p hp => gP p (List.mem_append_right _ hp),
        compose_map_eq hphi (mapM_forall₂ hE) fun p hp => gP p (List.mem_append_left _ hp)] at hm
      refine ideal_transport (E := ceqs.map fun e => toK (K := K) (meaning C.vars.length e))
        (Gs := cgs.map fun g => toK (K := K) (meaning C.vars.length g)) ?_ ?_ ⟨k₀, hm⟩
      · intro e he
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        exact hEo e' he'
      · intro g hg
        obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        exact hGo g' hg'
  · simp at h

/-! ## Rule admission is sound -/

theorem reach_nil {C : Stmt} {d : RuleData} {rr : Scope} (h : ruleReach C [] d = some rr) : False := by
  cases d <;> simp [ruleReach] at h

theorem reach_many {C P Q R : Stmt} {Ps : List Stmt} {d : RuleData} {rr : Scope}
    (hd : d ≠ .byCover) (h : ruleReach C (P :: Q :: R :: Ps) d = some rr) : False := by
  cases d <;> first | exact hd rfl | simp [ruleReach] at h

theorem reach_one_split {C P : Stmt} {f : Sparse} {rr : Scope}
    (h : ruleReach C [P] (.split f) = some rr) : False := by
  simp [ruleReach] at h

theorem reach_two_r1 {C P Q : Stmt} {rr : Scope} (h : ruleReach C [P, Q] .r1 = some rr) : False := by
  simp [ruleReach] at h

theorem reach_two_inclusion {C P Q : Stmt} {a b : List Cert} {rr : Scope}
    (h : ruleReach C [P, Q] (.inclusion a b) = some rr) : False := by
  simp [ruleReach] at h

theorem reach_two_map {C P Q : Stmt} {phi : List Sparse} {a b : List Cert} {rr : Scope}
    (h : ruleReach C [P, Q] (.map phi a b) = some rr) : False := by
  simp [ruleReach] at h

theorem reach_two_witness {C P Q : Stmt} {rr : Scope} (h : ruleReach C [P, Q] .witness = some rr) :
    False := by
  simp [ruleReach] at h

open GP50 GPBinding.Spike in
theorem acceptsRule_claim_meaning (clauses : List GPProfile.Clause) (rules : List RuleInst)
    (w : Warrant) (premises : List Warrant) (name : String)
    (accepted : acceptsRule clauses rules w premises name = true)
    (truth : ∀ premise ∈ premises, Semantic.ClaimMeaning profile clauses premise.claim) :
    Semantic.ClaimMeaning profile clauses w.claim := by
  unfold acceptsRule at accepted
  simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at accepted
  obtain ⟨-, r, -, hm⟩ := accepted
  obtain ⟨⟨⟨-, -⟩, -⟩, hmatch⟩ := hm
  cases hc : Semantic.boundClause ops clauses w with
  | none => simp [hc] at hmatch
  | some c =>
    cases hps : premises.mapM (Semantic.boundClause ops clauses) with
    | none => simp [hc, hps] at hmatch
    | some ps =>
      simp only [hc, hps, Bool.and_eq_true, List.all_eq_true] at hmatch
      obtain ⟨⟨⟨-, hle⟩, havoid⟩, hrr⟩ := hmatch
      cases hR : ruleReach c.stmt (ps.map (·.stmt)) r.data with
      | none => simp [hR] at hrr
      | some rr =>
        simp only [hR] at hrr
        have premiseMeans := Semantic.boundClauses_mapM_means profile clauses premises ps hps truth
        rcases Semantic.boundClause_registered profile clauses w c hc with ⟨unique, present, key⟩
        have means : Semantic.Means profile c.stmt c.scope := by
          refine means_iff.mpr fun K hK => ?_
          have hrrK : rr.mem K.carrier := Scope.le_den hrr hK
          have hpK : ∀ p ∈ ps, Holds K.carrier p.stmt :=
            fun p hp => means_iff.mp (premiseMeans p hp) K (Scope.le_den (hle p hp) hK)
          have hav := avoids_mem havoid hK
          have hCg : GoodAll K.carrier c.stmt.polys := stmt_good (hav.mono fun x hx => mem_union_left hx)
          have hPg : ∀ p ∈ ps, GoodAll K.carrier p.stmt.polys := fun p hp =>
            stmt_good (hav.mono fun x hx =>
              mem_union_right (mem_union_left (List.mem_flatMap.mpr ⟨p, hp, hx⟩)))
          have hDg : Avoids K.carrier r.data.primes :=
            hav.mono fun x hx => mem_union_right (mem_union_right hx)
          by_cases hcov : r.data = .byCover
          · rw [hcov] at hR
            rcases ps with _ | ⟨p₁, qs⟩
            · exact (reach_nil hR).elim
            · have hR' : ruleReach c.stmt (p₁.stmt :: qs.map (·.stmt)) .byCover = some rr := hR
              exact cover_rule_sound hR' (hpK p₁ List.mem_cons_self) fun Q hQ => by
                obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hQ
                exact hpK q (List.mem_cons_of_mem _ hq)
          rcases ps with _ | ⟨p₁, _ | ⟨p₂, _ | ⟨p₃, ps⟩⟩⟩
          · exact (reach_nil hR).elim
          · have h₁ := hpK p₁ List.mem_cons_self
            cases hd : r.data with
            | r1 => rw [hd] at hR; exact r1_sound hR h₁
            | inclusion eqC gC => rw [hd] at hR; exact r2_sound hR hrrK h₁
            | map phi eqC gC =>
              rw [hd] at hR
              have hphi : GoodAll K.carrier phi := fun f hf c' hc' =>
                good_of_avoids (by simpa [RuleData.primes, hd] using hDg)
                  (List.mem_flatMap.mpr ⟨f, hf, hc'⟩)
              exact r3_sound hR hrrK h₁ hphi (hPg p₁ List.mem_cons_self) hCg
            | split h => rw [hd] at hR; exact (reach_one_split hR).elim
            | witness => rw [hd] at hR; exact witness_sound hR h₁
            | byCover => exact absurd hd hcov
          · cases hd : r.data with
            | split h =>
              rw [hd] at hR
              exact r4_sound hR (hpK p₁ List.mem_cons_self)
                (hpK p₂ (List.mem_cons_of_mem _ List.mem_cons_self))
            | r1 => rw [hd] at hR; exact (reach_two_r1 hR).elim
            | inclusion _ _ => rw [hd] at hR; exact (reach_two_inclusion hR).elim
            | map _ _ _ => rw [hd] at hR; exact (reach_two_map hR).elim
            | witness => rw [hd] at hR; exact (reach_two_witness hR).elim
            | byCover => exact absurd hd hcov
          · exact (reach_many hcov hR).elim
        refine ⟨⟨c, present, key⟩, fun c' hc' hkey' => ?_⟩
        have := key_unique_of_nodup clauses (·.key) unique c' c hc' present (hkey'.trans key.symm)
        exact this ▸ means

open GP50 in
private theorem binding_beq_eq (a b : Binding) : instBEqBinding.beq a b = true → a = b := by
  cases a; cases b
  simp [instBEqBinding.beq, Bool.and_eq_true, beq_iff_eq]

open GP50 in
/-- The binder trust assumption, stated semantically: a binder record matching a clause's
binding identities comes with that clause's meaning (the binder's checks plus
`means_of_warranted` supply it; with no records it holds trivially). -/
def RecordsSound (clauses : List GPProfile.Clause) (records : List BinderRecord) : Prop :=
  ∀ c ∈ clauses, ∀ r ∈ records, r.statementHash = c.binding.statementHash →
    r.scopeHash = c.binding.scopeHash → Semantic.Means profile c.stmt c.scope

open GP50 in
theorem acceptsProof_claim_meaning (clauses : List GPProfile.Clause) (records : List BinderRecord)
    (hrec : RecordsSound clauses records) (w : Warrant) (decl : String)
    (accepted : acceptsProof clauses records w decl = true) :
    Semantic.ClaimMeaning profile clauses w.claim := by
  unfold acceptsProof at accepted
  simp only [Bool.and_eq_true, Option.isSome_iff_exists, List.any_eq_true, beq_iff_eq] at accepted
  obtain ⟨⟨c, hc⟩, r, hr, ⟨-, hsh⟩, hsc⟩ := accepted
  rcases Semantic.boundClause_registered profile clauses w c hc with ⟨unique, present, key⟩
  have hb : c.binding = w.binding := by
    unfold Semantic.boundClause at hc
    split at hc
    · contradiction
    · have m := List.find?_some (p := fun c' : Semantic.Clause ops =>
        c'.key == w.claim && c'.version == w.version && c'.binding == w.binding) hc
      simp only [Bool.and_eq_true, beq_iff_eq] at m
      exact binding_beq_eq _ _ m.2
  have means := hrec c present r hr (hsh.trans (congrArg Binding.statementHash hb).symm)
    (hsc.trans (congrArg Binding.scopeHash hb).symm)
  refine ⟨⟨c, present, key⟩, fun c' hc' hkey' => ?_⟩
  have := key_unique_of_nodup clauses (·.key) unique c' c hc' present (hkey'.trans key.symm)
  exact this ▸ means

open GP50 in
theorem base_validator_sound_rules (clauses : List GPProfile.Clause) (receipts : List Receipt)
    (rules : List RuleInst) (records : List BinderRecord) (hrec : RecordsSound clauses records)
    (snapshot : Snapshot) (unique : (snapshot.warrants.map (·.id)).Nodup) :
    Semantic.BaseValidatorSound profile clauses
      { receipt := accepts clauses receipts, proof := acceptsProof clauses records,
        rule := acceptsRule clauses rules, narrow := fun _ _ => false } snapshot := by
  constructor
  · intro w member name accepted
    exact ⟨w, member, rfl, accepts_claim_meaning clauses receipts w name accepted⟩
  · intro w member decl accepted
    exact ⟨w, member, rfl, acceptsProof_claim_meaning clauses records hrec w decl accepted⟩
  · intro w present premises name accepted members supported
    refine ⟨w, present, rfl, ?_⟩
    apply acceptsRule_claim_meaning clauses rules w premises name accepted
    intro premise hp
    exact Semantic.warrant_meaning_claim profile clauses snapshot unique premise (members premise hp)
      (supported premise hp)

open GP50 GPBinding.Spike in
/-- Fold soundness with K3 rules and bound theorem warrants: every held claim means its
registered statement in every field its scope denotes, whether supported by receipts, rules,
theorem warrants, narrowing, or a mixture. Theorem warrants rest on `RecordsSound`. -/
theorem fold_held_meaning_rules (clauses : List GPProfile.Clause) (receipts : List Receipt)
    (rules : List RuleInst) (records : List BinderRecord) (hrec : RecordsSound clauses records)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admissionWithRules clauses receipts rules records) events = .ok state)
    (heldClaim : held state claim = true) :
    (∃ c ∈ clauses, c.key = claim) ∧
    ∀ c ∈ clauses, c.key = claim → ∀ K : FieldCtx, Scope.mem K.carrier c.scope →
      Holds K.carrier c.stmt := by
  have unique : (state.snapshot.warrants.map (·.id)).Nodup := by
    unfold fold at folded
    cases resolved : resolve events with
    | error message => simp [resolved] at folded
    | ok snapshot =>
      rw [resolved] at folded
      have stateEq : evaluate (admissionWithRules clauses receipts rules records) snapshot = state :=
        Except.ok.inj folded
      subst state
      exact resolve_warrant_ids_nodup events snapshot resolved
  have h := Semantic.fold_held_meaning profile clauses _ events state claim
    (base_validator_sound_rules clauses receipts rules records hrec state.snapshot unique) folded heldClaim
  exact ⟨h.1, fun c hc hk => means_iff.mp (h.2 c hc hk)⟩

open GP50 in
/-- Without binder records, receipts and rules alone. -/
theorem fold_held_meaning_receipts_rules (clauses : List GPProfile.Clause) (receipts : List Receipt)
    (rules : List RuleInst) (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admissionWithRules clauses receipts rules []) events = .ok state)
    (heldClaim : held state claim = true) :
    (∃ c ∈ clauses, c.key = claim) ∧
    ∀ c ∈ clauses, c.key = claim → ∀ K : GPBinding.Spike.FieldCtx, Scope.mem K.carrier c.scope →
      Holds K.carrier c.stmt :=
  fold_held_meaning_rules clauses receipts rules [] (fun _ _ _ hr => by simp at hr) events state claim
    folded heldClaim

end GPBinding.Admission

end
