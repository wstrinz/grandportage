import GPBinding.Real.Profile
import GPBinding.Real.SOSSound
import GPBinding.Real.RAlgSound
import GPBinding.Real.AlgPointSound
import GPBinding.Real.RootCoverSound
import GPBinding.Real.OrderedSound
import GPBinding.Real.CaseTreeSound
import GPBinding.Real.GoalSound
import GPBinding.Admission.RuleSound
import GPProfile.Real.Admission
import Mathlib.Analysis.Real.Sqrt

/-!
Soundness of 3b admission (`GPProfile.Real.admission3`): every accepted receipt and rule gives its
claim's meaning in `profile3`, so the Kernel's generic fold theorem makes every held claim mean its
statement (`fold_held_meaning3`).

- `alg` evidence is 3a's: an `alg` statement's truth in `profile3` is literally 3a's, so 3a's
  `check_sound` and `acceptsRule_claim_meaning` apply unchanged; `algPoint` by `algPointCheck_means`.
- Number-field receipts by `nfCheck_holds` (`NumberFieldSound`), in every field.
- Rational-root receipts by `ratRootCheck_holds`, in every field isomorphic to ℚ; selected-root
  cover receipts by `rootCoverCheck_holds` (Descartes uniqueness), in every field isomorphic to ℝ
  (`RootCoverSound`).
- SOS receipts by `sosCheck_holds`, in every semireal field (ℝ-scope fields are semireal).
- Point receipts by `pointCheck_sound_value` over ℝ, carried to every field isomorphic to ℝ; a sign
  atom is the usual sign over ℝ, and `signSq` is invariant under ring isomorphisms.
- Ordered Positivstellensatz receipts (C7) by `Ordered.orderedCheck_holds`, in every field
  isomorphic to ℝ (`OrderedSound`).
- Refutation case trees (G-6) by `CaseTree.caseTreeCheck_holds`, in every field isomorphic to ℝ
  (`CaseTreeSound`), for real systems and for order-free EMPTY claims at `real`.
- Kind-1: every semireal field has characteristic 0, so a 3a claim held at a scope containing
  characteristic 0 holds in it (K1a); ℝ-scope fields are semireal (K1b).
- The DECIDE goal family (A2, `GoalSound`): `cover_all` receipts by `coverAllCheck_sound`; rules
  `realize`, `spine` and `decide` by `realizeRuleOk_sound`, `spineRuleOk_sound`, `decideRuleOk_sound`.
  `fold_held_goal` reads a held goal-family claim as its meaning over the Euclidean plane.
-/

noncomputable section

namespace GPBinding.Real
open GPProfile GPProfile.Real GPBinding.Admission GP50 MvPolynomial

/-! ## Transport along `ℝ ≃+* K` -/

theorem value_map {K : Type*} [Field K] [CharZero K] (f : ℝ →+* K) {n : ℕ} (p : Sparse)
    (x : Fin n → ℝ) : value n p (fun i => f (x i)) = f (value n p x) := by
  rw [value_eq, value_eq]
  simp only [evalQ, coe_eval₂Hom]
  rw [eval₂_comp_left f (Rat.castHom ℝ) x, RingHom.ext_rat (f.comp (Rat.castHom ℝ)) (Rat.castHom K)]
  rfl

theorem signSq_map {K L : Type*} [Field K] [Field L] (e : K ≃+* L) (y : K) : signSq (e y) = signSq y := by
  have h0 : e y = 0 ↔ y = 0 := map_eq_zero_iff e e.injective
  have hs : IsSquare (e y) ↔ IsSquare y :=
    ⟨fun h => by simpa using h.map e.symm, fun h => h.map e⟩
  unfold signSq
  by_cases hy : y = 0
  · simp [hy]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (mt h0.mp hy)), ite_eq_right_of_eq_false _ _ (eq_false hy)]
    by_cases hq : IsSquare y
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (hs.mpr hq)), ite_eq_left_of_eq_true _ _ (eq_true hq)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (mt hs.mp hq)), ite_eq_right_of_eq_false _ _ (eq_false hq)]

theorem signSq_real (y : ℝ) : signSq y = ((SignType.sign y : SignType) : ℤ) := by
  unfold signSq
  rcases lt_trichotomy y 0 with h | rfl | h
  · have hn : ¬ IsSquare y := fun hsq => absurd hsq.nonneg (not_le.mpr h)
    simp [h.ne, hn, sign_neg h]
  · simp
  · have hsq : IsSquare y := ⟨√y, (Real.mul_self_sqrt h.le).symm⟩
    simp [h.ne', hsq, sign_pos h]

/-- **Point receipts.** An accepted point is a point of the system in every field isomorphic to
ℝ (the hook into `pointCheck_sound_value`, `RAlgSound`). -/
theorem pointCheck_locus {r : RealSys} {w : RealWitness} (h : pointCheck r w = true)
    {K : Type*} [Field K] (e : K ≃+* ℝ) : ∃ x : Fin r.vars.length → K, RealLocus r x := by
  have := isSemireal_of_equiv_real e
  obtain ⟨x, he, hg, hs⟩ := pointCheck_sound_value h
  have hv : ∀ q : Sparse, value _ q (fun i => e.symm.toRingHom (x i)) = e.symm (value _ q x) :=
    fun q => value_map e.symm.toRingHom q x
  refine ⟨fun i => e.symm.toRingHom (x i), fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · rw [hv, he q hq, map_zero]
  · rw [hv]
    exact fun h0 => hg q hq (e.symm.injective (h0.trans (map_zero _).symm))
  · rw [hv, signSq_map, signSq_real, hs q hq]

/-! ## Receipts -/

theorem means_alg_iff {s : Stmt} {sc : Scope} :
    Semantic.Means profile3 (.alg s) (.alg sc) ↔ Semantic.Means Admission.profile s sc := Iff.rfl

theorem certOk3_sound {s : Stmt3} {sc : Scope3} {c : Cert3} (h : certOk3 s sc c = true) :
    Semantic.Means profile3 s sc := by
  cases s with
  | alg s =>
    cases sc with
    | alg sc =>
      cases c with
      | alg c =>
        change (check s sc c).ok = true at h
        apply means_alg_iff.mpr
        refine means_iff.mpr fun K hK => ?_
        unfold Check.ok at h
        split at h
        · exact check_sound (by assumption) hK
        · contradiction
      | algPoint c =>
        change (sc.le Scope.char0Only && algPointCheck s c) = true at h
        rw [Bool.and_eq_true] at h
        apply means_alg_iff.mpr
        have hm := means_iff.mp (AlgPoint.algPointCheck_means h.2)
        exact means_iff.mpr fun K hK => hm K (Scope.le_den h.1 hK)
      | sos _ => simp [certOk3] at h
      | point _ => simp [certOk3] at h
      | nf _ => simp [certOk3] at h
      | ratRoot => simp [certOk3] at h
      | rootCover _ => simp [certOk3] at h
      | ordered _ => simp [certOk3] at h
      | caseTree _ => simp [certOk3] at h
      | coverAll => simp [certOk3] at h
    | semireal => cases c <;> simp [certOk3] at h
    | real => cases c <;> simp [certOk3] at h
    | ratField => cases c <;> simp [certOk3] at h
  | orderFree s =>
    cases sc with
    | alg _ => cases c <;> simp [certOk3] at h
    | semireal =>
      cases c with
      | sos c =>
        intro (K : Spike.FieldCtx) hK
        have : IsSemireal K.carrier := hK
        exact sosCheck_holds h K.carrier
      | _ => simp [certOk3] at h
    | real =>
      cases c with
      | sos c =>
        intro (K : Spike.FieldCtx) hK
        have : IsSemireal K.carrier := isSemireal_of_equiv_real (Classical.choice hK)
        exact sosCheck_holds h K.carrier
      | point w =>
        change (s.kind == .nonempty && pointCheck (orderFreeSys s) w) = true at h
        rw [Bool.and_eq_true, beq_iff_eq] at h
        intro (K : Spike.FieldCtx) hK
        obtain ⟨x, he, hg, -⟩ := pointCheck_locus h.2 (Classical.choice hK)
        change Admission.Holds K.carrier s
        unfold Admission.Holds
        rw [h.1]
        exact ⟨x, he, hg⟩
      | caseTree c =>
        change (s.kind == .empty && caseTreeCheck (orderFreeSys s) c) = true at h
        rw [Bool.and_eq_true, beq_iff_eq] at h
        intro (K : Spike.FieldCtx) hK
        change Admission.Holds K.carrier s
        unfold Admission.Holds
        rw [h.1]
        intro x hx
        exact CaseTree.caseTreeCheck_holds h.2 (Classical.choice hK) x ⟨hx.1, hx.2, by simp [orderFreeSys]⟩
      | _ => simp [certOk3] at h
    | ratField =>
      cases c with
      | ratRoot =>
        intro (K : Spike.FieldCtx) hK
        exact RootCover.ratRootCheck_holds h (Classical.choice hK)
      | _ => simp [certOk3] at h
  | real r e =>
    cases sc with
    | real =>
      cases e with
      | nonempty =>
        cases c with
        | point w =>
          intro (K : Spike.FieldCtx) hK
          exact pointCheck_locus h (Classical.choice hK)
        | _ => simp [certOk3] at h
      | empty =>
        cases c with
        | ordered c =>
          intro (K : Spike.FieldCtx) hK
          exact Ordered.orderedCheck_holds h (Classical.choice hK)
        | caseTree c =>
          intro (K : Spike.FieldCtx) hK
          exact CaseTree.caseTreeCheck_holds h (Classical.choice hK)
        | _ => simp [certOk3] at h
    | _ => cases c <;> cases e <;> simp [certOk3] at h
  | goal g =>
    cases sc with
    | real =>
      cases c with
      | coverAll =>
        cases g with
        | cover n m L => exact means_goal (coverAllCheck_sound h)
        | _ => simp [certOk3] at h
      | _ => cases g <;> simp [certOk3] at h
    | _ => cases c <;> cases g <;> simp [certOk3] at h
  | nf p =>
    cases sc with
    | alg sc =>
      cases c with
      | nf c =>
        change (sc.le Scope.char0Only && nfCheck p c) = true at h
        rw [Bool.and_eq_true] at h
        intro (K : Spike.FieldCtx) _
        exact NumberField.nfCheck_holds h.2 K.carrier
      | _ => simp [certOk3] at h
    | semireal => cases c <;> simp [certOk3] at h
    | real => cases c <;> simp [certOk3] at h
    | ratField => cases c <;> simp [certOk3] at h
  | realCover r bs =>
    cases sc with
    | real =>
      cases c with
      | rootCover c =>
        intro (K : Spike.FieldCtx) hK
        exact RootCover.rootCoverCheck_holds h (Classical.choice hK)
      | _ => simp [certOk3] at h
    | _ => cases c <;> simp [certOk3] at h

theorem accepts3_claim_meaning (clauses : List Clause3) (receipts : List Receipt3) (w : Warrant)
    (name : String) (accepted : accepts3With (wellFormed3 clauses receipts) clauses receipts w name = true) :
    Semantic.ClaimMeaning profile3 clauses w.claim := by
  unfold accepts3With at accepted
  simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq, decide_eq_true_eq] at accepted
  obtain ⟨wf, c, hc, ⟨⟨hkey, -⟩, -⟩, r, -, hok⟩ := accepted
  have nodup : (clauses.map (·.key)).Nodup := by
    unfold wellFormed3 at wf
    simp only [Bool.and_eq_true, beq_iff_eq] at wf
    exact nodup_of_eraseDups_length_eq _ (by simpa only [List.length_map] using wf.1)
  have means := certOk3_sound hok.2
  refine ⟨⟨c, hc, hkey⟩, fun c' hc' hkey' => ?_⟩
  have := key_unique_of_nodup clauses (·.key) nodup c' c hc' hc (hkey'.trans hkey.symm)
  exact this ▸ means

/-! ## Kind-1 rules -/

theorem k1Ok_sound {k : Kind} {target : Scope3} (ht : Scope3.le target .semireal = true)
    {c : Clause3} {ps : List Clause3} (h : k1Ok k target c ps = true)
    (hp : ∀ p ∈ ps, Semantic.Means profile3 p.stmt p.scope) : Semantic.Means profile3 c.stmt c.scope := by
  match ps, h, hp with
  | [], h, _ => simp [k1Ok] at h
  | _ :: _ :: _, h, _ => simp [k1Ok] at h
  | [p], h, hp =>
    have hP := hp p List.mem_cons_self
    obtain ⟨_, _, _, cs, csc⟩ := c
    obtain ⟨_, _, _, pst, psc⟩ := p
    cases pst with
    | alg s =>
      cases psc with
      | alg sc =>
        cases cs with
        | orderFree s' =>
          simp only [k1Ok, Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨⟨rfl, -⟩, h0⟩, hle⟩ := h
          intro (K : Spike.FieldCtx) hK
          have : IsSemireal K.carrier := le3_sound _ _ K ht (le3_sound _ _ K hle hK)
          have hmem : Scope.mem K.carrier sc := Or.inl ⟨ringChar.eq_zero, h0⟩
          exact hP K hmem K rfl
        | alg _ => simp [k1Ok] at h
        | real _ _ => simp [k1Ok] at h
        | nf _ => simp [k1Ok] at h
        | realCover _ _ => simp [k1Ok] at h
        | goal _ => simp [k1Ok] at h
      | semireal => cases cs <;> simp [k1Ok] at h
      | real => cases cs <;> simp [k1Ok] at h
      | ratField => cases cs <;> simp [k1Ok] at h
    | orderFree _ => cases psc <;> cases cs <;> simp [k1Ok] at h
    | real _ _ => cases psc <;> cases cs <;> simp [k1Ok] at h
    | nf _ => cases psc <;> cases cs <;> simp [k1Ok] at h
    | realCover _ _ => cases psc <;> cases cs <;> simp [k1Ok] at h
    | goal _ => cases psc <;> cases cs <;> simp [k1Ok] at h

/-! ## 3a rules on the `alg` projection -/

theorem toAlg_spec {c : Clause3} {a : Clause} (h : c.toAlg = some a) :
    c.key = a.key ∧ c.stmt = .alg a.stmt ∧ c.scope = .alg a.scope := by
  obtain ⟨_, _, _, s, sc⟩ := c
  cases s with
  | alg s =>
    cases sc with
    | alg sc => cases h; exact ⟨rfl, rfl, rfl⟩
    | semireal => cases h
    | real => cases h
    | ratField => cases h
  | orderFree _ => cases sc <;> cases h
  | real _ _ => cases sc <;> cases h
  | nf _ => cases sc <;> cases h
  | realCover _ _ => cases sc <;> cases h
  | goal _ => cases sc <;> cases h

theorem claim_alg_of_claim3 {clauses : List Clause3} {k : ℕ}
    (h : Semantic.ClaimMeaning profile3 clauses k) (hex : ∃ a ∈ algClauses clauses, a.key = k) :
    Semantic.ClaimMeaning Admission.profile (algClauses clauses) k := by
  refine ⟨hex, fun a ha hk => ?_⟩
  obtain ⟨c, hc, hca⟩ := List.mem_filterMap.mp ha
  obtain ⟨hkey, hs, hsc⟩ := toAlg_spec hca
  have := h.2 c hc (hkey.trans hk)
  rw [hs, hsc] at this
  exact this

theorem claim3_of_claim_alg {clauses : List Clause3} (hnd : (clauses.map (·.key)).Nodup) {k : ℕ}
    (h : Semantic.ClaimMeaning Admission.profile (algClauses clauses) k) :
    Semantic.ClaimMeaning profile3 clauses k := by
  obtain ⟨⟨a, ha, hk⟩, hall⟩ := h
  obtain ⟨c, hc, hca⟩ := List.mem_filterMap.mp ha
  obtain ⟨hkey, hs, hsc⟩ := toAlg_spec hca
  refine ⟨⟨c, hc, hkey.trans hk⟩, fun c' hc' hk' => ?_⟩
  have := key_unique_of_nodup clauses (·.key) hnd c' c hc' hc (hk'.trans (hkey.trans hk).symm)
  subst this
  rw [hs, hsc]
  exact hall a ha hk

theorem mapM_some_each {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {bs : List β}, l.mapM f = some bs → ∀ a ∈ l, ∃ b, f a = some b
  | [], _, _, a, ha => by simp at ha
  | x :: xs, bs, h, a, ha => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases hx : f x with
    | none => simp [hx] at h
    | some b =>
      cases hxs : xs.mapM f with
      | none => simp [hx, hxs] at h
      | some cs =>
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ⟨b, hx⟩
        · exact mapM_some_each hxs a ha

/-- An accepted 3a rule binds every premise to a clause. -/
theorem acceptsRule_premises {cl : List Clause} {rules : List RuleInst} {w : Warrant}
    {premises : List Warrant} {name : String} (h : acceptsRule cl rules w premises name = true) :
    ∀ p ∈ premises, ∃ c ∈ cl, c.key = p.claim := by
  unfold acceptsRule at h
  simp only [Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨-, r, -, -, hmatch⟩ := h
  intro p hp
  cases hps : premises.mapM (Semantic.boundClause ops cl) with
  | none =>
    cases hc : Semantic.boundClause ops cl w <;> simp [hc, hps] at hmatch
  | some ps =>
    obtain ⟨c, hc⟩ := mapM_some_each hps p hp
    obtain ⟨-, mem, key⟩ := Semantic.boundClause_registered Admission.profile cl p c hc
    exact ⟨c, mem, key⟩

theorem lift_claim_meaning {clauses : List Clause3} (hnd : (clauses.map (·.key)).Nodup)
    (r : RuleInst3) (d : RuleData) (w : Warrant) (premises : List Warrant)
    (hok : acceptsRuleWith (namesDistinct [r.lift d]) (keysUnique (algClauses clauses))
      (algClauses clauses) [r.lift d] w premises r.name = true)
    (truth : ∀ p ∈ premises, Semantic.ClaimMeaning profile3 clauses p.claim) :
    Semantic.ClaimMeaning profile3 clauses w.claim := by
  have acc : acceptsRule (algClauses clauses) [r.lift d] w premises r.name = true := by
    rw [acceptsRule_eq_acceptsRuleWith]; exact hok
  have bound := acceptsRule_premises acc
  exact claim3_of_claim_alg hnd (acceptsRule_claim_meaning _ _ w premises r.name acc
    fun p hp => claim_alg_of_claim3 (truth p hp) (bound p hp))

theorem boundWith3_fun (clauses : List Clause3) :
    boundWith3 (keysUnique3 clauses) clauses = Semantic.boundClause ops3 clauses := rfl

theorem k1_claim_meaning {clauses : List Clause3} {k : Kind} {target : Scope3}
    (ht : Scope3.le target .semireal = true) (w : Warrant) (premises : List Warrant)
    (hok : (match boundWith3 (keysUnique3 clauses) clauses w,
        premises.mapM (boundWith3 (keysUnique3 clauses) clauses) with
      | some c, some ps => k1Ok k target c ps
      | _, _ => false) = true)
    (truth : ∀ p ∈ premises, Semantic.ClaimMeaning profile3 clauses p.claim) :
    Semantic.ClaimMeaning profile3 clauses w.claim := by
  rw [boundWith3_fun] at hok
  cases hc : Semantic.boundClause ops3 clauses w with
  | none => simp [hc] at hok
  | some c =>
    cases hps : premises.mapM (Semantic.boundClause ops3 clauses) with
    | none => simp [hc, hps] at hok
    | some ps =>
      simp only [hc, hps] at hok
      have premiseMeans := Semantic.boundClauses_mapM_means profile3 clauses premises ps hps truth
      rcases Semantic.boundClause_registered profile3 clauses w c hc with ⟨unique, present, key⟩
      have means := k1Ok_sound ht hok premiseMeans
      refine ⟨⟨c, present, key⟩, fun c' hc' hkey' => ?_⟩
      have := key_unique_of_nodup clauses (·.key) unique c' c hc' present (hkey'.trans key.symm)
      exact this ▸ means

/-- A 3b rule whose clause-level check is sound gives its conclusion's claim meaning (the shape of
`k1_claim_meaning`, for the goal rules). -/
theorem rule3_claim_meaning {clauses : List Clause3} (ok : Clause3 → List Clause3 → Bool)
    (sound : ∀ c ps, ok c ps = true → (∀ p ∈ ps, Semantic.Means profile3 p.stmt p.scope) →
      Semantic.Means profile3 c.stmt c.scope)
    (w : Warrant) (premises : List Warrant)
    (hok : (match boundWith3 (keysUnique3 clauses) clauses w,
        premises.mapM (boundWith3 (keysUnique3 clauses) clauses) with
      | some c, some ps => ok c ps
      | _, _ => false) = true)
    (truth : ∀ p ∈ premises, Semantic.ClaimMeaning profile3 clauses p.claim) :
    Semantic.ClaimMeaning profile3 clauses w.claim := by
  rw [boundWith3_fun] at hok
  cases hc : Semantic.boundClause ops3 clauses w with
  | none => simp [hc] at hok
  | some c =>
    cases hps : premises.mapM (Semantic.boundClause ops3 clauses) with
    | none => simp [hc, hps] at hok
    | some ps =>
      simp only [hc, hps] at hok
      have premiseMeans := Semantic.boundClauses_mapM_means profile3 clauses premises ps hps truth
      rcases Semantic.boundClause_registered profile3 clauses w c hc with ⟨unique, present, key⟩
      have means := sound c ps hok premiseMeans
      refine ⟨⟨c, present, key⟩, fun c' hc' hkey' => ?_⟩
      have := key_unique_of_nodup clauses (·.key) unique c' c hc' present (hkey'.trans key.symm)
      exact this ▸ means

theorem acceptsRule3_claim_meaning (clauses : List Clause3) (rules : List RuleInst3) (w : Warrant)
    (premises : List Warrant) (name : String)
    (accepted : acceptsRule3With (namesDistinct3 rules) (keysUnique3 clauses)
      (keysUnique (algClauses clauses)) clauses (algClauses clauses) rules w premises name = true)
    (truth : ∀ p ∈ premises, Semantic.ClaimMeaning profile3 clauses p.claim) :
    Semantic.ClaimMeaning profile3 clauses w.claim := by
  unfold acceptsRule3With at accepted
  simp only [Bool.and_eq_true, List.any_eq_true] at accepted
  obtain ⟨⟨-, hu⟩, r, -, -, hok⟩ := accepted
  have hnd : (clauses.map (·.key)).Nodup :=
    nodup_of_eraseDups_length_eq _ (by simpa [keysUnique3] using hu)
  unfold ruleOk3 at hok
  cases hd : r.data with
  | lift d => rw [hd] at hok; exact lift_claim_meaning hnd r d w premises hok truth
  | k1Empty => rw [hd] at hok; exact k1_claim_meaning rfl w premises hok truth
  | k1Nonempty => rw [hd] at hok; exact k1_claim_meaning rfl w premises hok truth
  | realize e g =>
    rw [hd] at hok
    exact rule3_claim_meaning (realizeRuleOk e g) (fun _ _ => realizeRuleOk_sound) w premises hok truth
  | spine =>
    rw [hd] at hok
    exact rule3_claim_meaning spineRuleOk (fun _ _ => spineRuleOk_sound) w premises hok truth
  | decide =>
    rw [hd] at hok
    exact rule3_claim_meaning decideRuleOk (fun _ _ => decideRuleOk_sound) w premises hok truth

/-! ## The fold -/

theorem base3_sound (clauses : List Clause3) (receipts : List Receipt3) (rules : List RuleInst3)
    (snapshot : Snapshot) (unique : (snapshot.warrants.map (·.id)).Nodup) :
    Semantic.BaseValidatorSound profile3 clauses (base3 clauses receipts rules) snapshot := by
  constructor
  · intro w member name accepted
    exact ⟨w, member, rfl, accepts3_claim_meaning clauses receipts w name accepted⟩
  · intro w _ decl accepted
    simp [base3] at accepted
  · intro w present premises name accepted members supported
    refine ⟨w, present, rfl, ?_⟩
    apply acceptsRule3_claim_meaning clauses rules w premises name accepted
    intro premise hp
    exact Semantic.warrant_meaning_claim profile3 clauses snapshot unique premise (members premise hp)
      (supported premise hp)

/-- **3b fold soundness.** Every claim held by the Kernel fold under `admission3` means its
registered statement in `profile3`: in every field context its scope denotes, whether supported
by receipts (3a, `algPoint`, SOS, point, ordered, case tree), rules (3a's lifted, K1a, K1b), narrowing, or a mixture. -/
theorem fold_held_meaning3 (clauses : List Clause3) (receipts : List Receipt3) (rules : List RuleInst3)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission3 clauses receipts rules) events = .ok state)
    (heldClaim : held state claim = true) :
    (∃ c ∈ clauses, c.key = claim) ∧
    ∀ c ∈ clauses, c.key = claim → Semantic.Means profile3 c.stmt c.scope := by
  have unique : (state.snapshot.warrants.map (·.id)).Nodup := by
    unfold fold at folded
    cases resolved : resolve events with
    | error message => simp [resolved] at folded
    | ok snapshot =>
      rw [resolved] at folded
      have stateEq : evaluate (admission3 clauses receipts rules) snapshot = state :=
        Except.ok.inj folded
      subst state
      exact resolve_warrant_ids_nodup events snapshot resolved
  exact Semantic.fold_held_meaning profile3 clauses _ events state claim
    (base3_sound clauses receipts rules state.snapshot unique) folded heldClaim

/-- A held claim at `real` scope is true over ℝ itself. -/
theorem fold_held_real (clauses : List Clause3) (receipts : List Receipt3) (rules : List RuleInst3)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission3 clauses receipts rules) events = .ok state)
    (heldClaim : held state claim = true) :
    ∀ c ∈ clauses, c.key = claim → c.scope = .real → Holds3 c.stmt ⟨ℝ⟩ := by
  intro c hc hk hs
  have := (fold_held_meaning3 clauses receipts rules events state claim folded heldClaim).2 c hc hk
  rw [hs] at this
  exact this ⟨ℝ⟩ ⟨RingEquiv.refl ℝ⟩

/-- **The DECIDE goal, held by the Kernel (A2).** A held goal-family claim at `real` scope means its
statement over the Euclidean plane: Q(n, m), ¬Q(n, m), a complete cover, or the spine implication. -/
theorem fold_held_goal (clauses : List Clause3) (receipts : List Receipt3) (rules : List RuleInst3)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission3 clauses receipts rules) events = .ok state)
    (heldClaim : held state claim = true) :
    ∀ c ∈ clauses, c.key = claim → c.scope = .real → ∀ g, c.stmt = .goal g → GoalHolds g := by
  intro c hc hk hs g hg
  have := fold_held_real clauses receipts rules events state claim folded heldClaim c hc hk hs
  rw [hg] at this
  exact this

/-- A held `goal n m false` at `real`: no `n` points of the plane have `m` unit distances. -/
theorem fold_held_not_Q (clauses : List Clause3) (receipts : List Receipt3) (rules : List RuleInst3)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission3 clauses receipts rules) events = .ok state)
    (heldClaim : held state claim = true) {n m : ℕ} :
    ∀ c ∈ clauses, c.key = claim → c.scope = .real → c.stmt = .goal (.goal n m false) → ¬ GoalQ n m :=
  fun c hc hk hs hg => fold_held_goal clauses receipts rules events state claim folded heldClaim c hc hk hs _ hg

end GPBinding.Real
