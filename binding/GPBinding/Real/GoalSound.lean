import GPBinding.Real.Profile
import GPProfile.Real.Admission

/-!
Soundness of the DECIDE goal family's evidence (release plan A2), over the meanings of
`GPBinding.Real.Goal`.

- `coverAllCheck_sound`: an accepted `cover_all` receipt lists every graph on `Fin n` with at least
  `m` edges, so the cover is complete (`coverComplete_of_all`).
- `realizeOk_sound`: a held NONEMPTY claim over ℝ whose statement is the Lean encoder's for a graph
  with at least `m` canonical edges gives Q(n, m) (`holds_iff_holdsE_udg`, `udg_realize`).
- `exclusionOk_sound`: a held EMPTY claim over ℝ whose statement is the encoder's for a graph (gauged
  or not) gives the `IsEmpty` hypothesis of `spine_sound` (`candidate_isEmpty`).
- `realizeRuleOk_sound`, `spineRuleOk_sound`, `decideRuleOk_sound`: the three rules, from premises
  meaning their statements to the conclusion's meaning (`spine_sound`; modus ponens).

The edge count is exact: the canonical edge list (`Data.edgeList`, pairs `i < j < n` once each)
has exactly as many entries as the graph has edges (`card_edgeFinset_eq_length`).
-/

noncomputable section

namespace GPBinding.Real
open GPProfile GPProfile.Real GPProfile.UDG GPBinding.UDG GPBinding.Admission UDGRope GP50
open scoped Finset

/-! ## Edge counts -/

theorem pairs_nodup (n : ℕ) : (pairs n).Nodup := by
  unfold pairs
  rw [List.nodup_flatMap]
  refine ⟨fun i _ => (List.nodup_range.filter _).map fun a b h => (Prod.mk.inj h).2, ?_⟩
  refine List.nodup_range.pairwise_of_forall_ne fun i _ j _ hij => ?_
  simp only [Function.onFun, List.disjoint_left, List.mem_map]
  rintro _ ⟨a, -, rfl⟩ ⟨b, -, h⟩
  exact hij (Prod.mk.inj h).1.symm

theorem edgeList_nodup (D : Data) : D.edgeList.Nodup := (pairs_nodup D.n).filter _

/-- A duplicate-free list of pairs `i < j < n` that lists exactly the edges of `G` has as many
entries as `G` has edges. -/
theorem card_edgeFinset_eq_length {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : List (ℕ × ℕ)) (hnd : S.Nodup) (hlt : ∀ p ∈ S, p.1 < p.2 ∧ p.2 < n)
    (hadj : ∀ i j : Fin n, i.val < j.val → (G.Adj i j ↔ (i.val, j.val) ∈ S)) :
    #G.edgeFinset = S.length := by
  rw [← List.toFinset_card_of_nodup hnd]
  symm
  refine Finset.card_bij (fun p hp => s(⟨p.1, (hlt p (List.mem_toFinset.mp hp)).1.trans
      (hlt p (List.mem_toFinset.mp hp)).2⟩, ⟨p.2, (hlt p (List.mem_toFinset.mp hp)).2⟩)) ?_ ?_ ?_
  · intro p hp
    have h := hlt p (List.mem_toFinset.mp hp)
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact (hadj _ _ h.1).mpr (List.mem_toFinset.mp hp)
  · intro p hp q hq he
    have h1 := hlt p (List.mem_toFinset.mp hp)
    have h2 := hlt q (List.mem_toFinset.mp hq)
    rcases Sym2.eq_iff.mp he with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · simp only [Fin.mk.injEq] at ha hb
      exact Prod.ext ha hb
    · simp only [Fin.mk.injEq] at ha hb
      omega
  · intro e he
    induction e using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rcases lt_or_gt_of_ne (G.ne_of_adj he) with h | h
      · exact ⟨(u.val, v.val), List.mem_toFinset.mpr ((hadj u v h).mp he), rfl⟩
      · exact ⟨(v.val, u.val), List.mem_toFinset.mpr ((hadj v u h).mp he.symm), Sym2.eq_swap⟩

theorem graph_adj_iff (D : Data) {i j : Fin D.n} (h : i.val < j.val) :
    D.graph.Adj i j ↔ (i.val, j.val) ∈ D.edgeList := by
  rw [mem_edgeList]
  exact ⟨fun ha => ⟨h, j.isLt, ha.2⟩, fun ha => ⟨fun e => by rw [e] at h; exact lt_irrefl _ h, ha.2.2⟩⟩

/-- The canonical edge list counts the graph's edges exactly. -/
theorem card_edgeFinset_graph (D : Data) [DecidableRel D.graph.Adj] :
    #D.graph.edgeFinset = D.edgeList.length :=
  card_edgeFinset_eq_length D.graph D.edgeList (edgeList_nodup D)
    (fun p hp => by obtain ⟨a, b, c⟩ := mem_edgeList.mp hp; exact ⟨a, b⟩) fun _ _ h => graph_adj_iff D h

/-! ## The exhaustive cover -/

theorem mem_sublistsGE {α : Type} : ∀ {m : ℕ} {l S : List α}, S.Sublist l → m ≤ S.length → S ∈ sublistsGE m l
  | m, [], S, hs, hm => by
    rw [List.sublist_nil.mp hs] at hm ⊢
    simp only [List.length_nil, Nat.le_zero] at hm
    simp [sublistsGE, hm]
  | m, a :: l, S, hs, hm => by
    have hlen := hs.length_le
    simp only [List.length_cons] at hlen
    unfold sublistsGE
    rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ l.length + 1 < m by omega)), List.mem_append]
    cases hs with
    | cons _ hs => exact Or.inr (mem_sublistsGE hs hm)
    | cons_cons _ hs =>
      simp only [List.length_cons] at hm
      exact Or.inl (List.mem_map.mpr ⟨_, mem_sublistsGE hs (by omega), rfl⟩)

/-- The canonical edge list of a graph on `Fin n`. -/
def edgesOfGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List (ℕ × ℕ) :=
  (pairs n).filter fun p => if h : p.1 < n ∧ p.2 < n then decide (G.Adj ⟨p.1, h.1⟩ ⟨p.2, h.2⟩) else false

theorem mem_edgesOfGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {i j : ℕ} :
    (i, j) ∈ edgesOfGraph G ↔ ∃ (h : i < j ∧ j < n), G.Adj ⟨i, h.1.trans h.2⟩ ⟨j, h.2⟩ := by
  simp only [edgesOfGraph, List.mem_filter, mem_pairs]
  constructor
  · rintro ⟨h, ha⟩
    rw [dite_eq_left_of_eq_true (eq_true ⟨h.1.trans h.2, h.2⟩), decide_eq_true_eq] at ha
    exact ⟨h, ha⟩
  · rintro ⟨h, ha⟩
    exact ⟨h, by rw [dite_eq_left_of_eq_true (eq_true ⟨h.1.trans h.2, h.2⟩), decide_eq_true_eq]; exact ha⟩

/-- **`cover_all`.** An accepted exhaustive cover is complete. -/
theorem coverAllCheck_sound {n m : ℕ} {L : List EdgeList} (h : coverAllCheck n m L = true) :
    CoverComplete n m (goalGraphs n L) := by
  classical
  simp only [coverAllCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  apply coverComplete_of_all
  intro G hG
  let S := edgesOfGraph G
  have hadj : ∀ i j : Fin n, i.val < j.val → (G.Adj i j ↔ (i.val, j.val) ∈ S) := fun i j hij => by
    rw [mem_edgesOfGraph]
    exact ⟨fun ha => ⟨⟨hij, j.isLt⟩, ha⟩, fun ⟨_, ha⟩ => ha⟩
  have hcard : #G.edgeFinset = S.length :=
    card_edgeFinset_eq_length G S ((pairs_nodup n).filter _)
      (fun p hp => by obtain ⟨hh, -⟩ := (mem_edgesOfGraph G).mp hp; exact hh) hadj
  obtain ⟨l, hl, hS⟩ := h.2 S (mem_sublistsGE List.filter_sublist (hcard ▸ hG))
  refine List.mem_map.mpr ⟨l, hl, ?_⟩
  ext i j
  show (⟨n, l, false⟩ : Data).graph.Adj i j ↔ G.Adj i j
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · have := graph_adj_iff ⟨n, l, false⟩ (i := i) (j := j) hij
    rw [hS] at this
    exact this.trans (hadj i j hij).symm
  · have : i = j := Fin.ext hij
    subst this
    exact ⟨fun h => absurd h (SimpleGraph.irrefl _), fun h => absurd h (SimpleGraph.irrefl _)⟩
  · have := graph_adj_iff ⟨n, l, false⟩ (i := j) (j := i) hij
    rw [hS] at this
    exact ((⟨n, l, false⟩ : Data).graph.adj_comm i j).trans
      (this.trans ((hadj j i hij).symm.trans (G.adj_comm j i)))

/-! ## The realization and the exclusions -/

theorem stmt_some {D : Data} {k : Kind} {s : Stmt} (h : D.stmt k = some s) :
    ∃ vars eqs guards, D.system = some (vars, eqs, guards) ∧ s = ⟨vars, eqs, guards, k⟩ := by
  unfold Data.stmt at h
  cases hs : D.system with
  | none => simp [hs] at h
  | some t =>
    obtain ⟨vars, eqs, guards⟩ := t
    simp only [hs, Option.map_some, Option.some.injEq] at h
    exact ⟨vars, eqs, guards, rfl, h.symm⟩

/-- **`realize`.** An encoder-exact NONEMPTY statement true over ℝ, for a graph on `n` vertices with
at least `m` canonical edges, gives Q(n, m). -/
theorem realizeOk_sound {n m : ℕ} {edges : EdgeList} {gauge : Bool} {s : Stmt}
    (h : realizeOk n m edges gauge s = true) (hs : Admission.Holds ℝ s) : GoalQ n m := by
  classical
  simp only [realizeOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hst, hm⟩ := h
  obtain ⟨vars, eqs, guards, hsys, rfl⟩ := stmt_some hst
  let D : Data := ⟨n, edges, gauge⟩
  have hE := (holds_iff_holdsE_udg D hsys .nonempty (Or.inr rfl)).mp hs
  exact udg_realize D hsys hE (m := m) (by rw [card_edgeFinset_graph D]; exact hm)

/-- **An exclusion.** An encoder-exact EMPTY statement true over ℝ (gauged or not) leaves its graph
no unit-distance embedding. -/
theorem exclusionOk_sound {n : ℕ} {l : EdgeList} {s : Stmt} (h : exclusionOk n l s = true)
    (hs : Admission.Holds ℝ s) : IsEmpty ((goalGraph n l).UnitDistEmbedding (EuclideanSpace ℝ (Fin 2))) := by
  simp only [exclusionOk, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · obtain ⟨vars, eqs, guards, hsys, rfl⟩ := stmt_some h
    exact candidate_isEmpty ⟨n, l, false⟩ hsys
      ((holds_iff_holdsE_udg ⟨n, l, false⟩ hsys .empty (Or.inl rfl)).mp hs)
  · obtain ⟨vars, eqs, guards, hsys, rfl⟩ := stmt_some h
    exact candidate_isEmpty ⟨n, l, true⟩ hsys
      ((holds_iff_holdsE_udg ⟨n, l, true⟩ hsys .empty (Or.inl rfl)).mp hs)

/-! ## The rules -/

/-- A premise at `real` scope is true over ℝ itself. -/
theorem means_real_holds {st : Stmt3} (h : Semantic.Means profile3 st .real) : Holds3 st ⟨ℝ⟩ :=
  h ⟨ℝ⟩ ⟨RingEquiv.refl ℝ⟩

/-- A goal-family statement holds at any scope once it holds. -/
theorem means_goal {g : GoalStmt} {sc : Scope3} (h : GoalHolds g) : Semantic.Means profile3 (.goal g) sc :=
  fun _ _ => h

theorem realizeRuleOk_sound {edges : EdgeList} {gauge : Bool} {c : Clause3} {ps : List Clause3}
    (h : realizeRuleOk edges gauge c ps = true) (hp : ∀ p ∈ ps, Semantic.Means profile3 p.stmt p.scope) :
    Semantic.Means profile3 c.stmt c.scope := by
  rcases ps with _ | ⟨p, _ | ⟨_, _⟩⟩
  · simp [realizeRuleOk] at h
  rotate_left
  · simp [realizeRuleOk] at h
  ·
    have hP := hp p List.mem_cons_self
    obtain ⟨_, _, _, cs, csc⟩ := c
    obtain ⟨_, _, _, pst, psc⟩ := p
    cases cs <;> try (simp [realizeRuleOk] at h; done)
    rename_i g
    cases g <;> try (simp [realizeRuleOk] at h; done)
    rename_i n m v
    cases v <;> try (simp [realizeRuleOk] at h; done)
    cases csc <;> try (simp [realizeRuleOk] at h; done)
    cases pst <;> try (simp [realizeRuleOk] at h; done)
    rename_i s
    cases psc <;> try (simp [realizeRuleOk] at h; done)
    exact means_goal (realizeOk_sound h (means_real_holds hP))

theorem spinePremisesOk_sound {n : ℕ} :
    ∀ {L : List EdgeList} {ps : List Clause3}, spinePremisesOk n L ps = true →
      (∀ p ∈ ps, Semantic.Means profile3 p.stmt p.scope) →
      ∀ G ∈ goalGraphs n L, IsEmpty (G.UnitDistEmbedding (EuclideanSpace ℝ (Fin 2)))
  | [], [], _, _, G, hG => by simp [goalGraphs] at hG
  | [], _ :: _, h, _, _, _ => by simp [spinePremisesOk] at h
  | _ :: _, [], h, _, _, _ => by simp [spinePremisesOk] at h
  | l :: L, p :: ps, h, hp, G, hG => by
    simp only [spinePremisesOk, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    simp only [goalGraphs, List.map_cons, List.mem_cons] at hG
    rcases hG with rfl | hG
    · have hP := hp p List.mem_cons_self
      obtain ⟨_, _, _, pst, psc⟩ := p
      split at h1
      · rename_i s hpst hpsc
        simp only at hpst hpsc
        subst hpst hpsc
        exact exclusionOk_sound h1 (means_real_holds hP)
      · simp at h1
    · exact spinePremisesOk_sound h2 (fun q hq => hp q (List.mem_cons_of_mem _ hq)) G hG

theorem spineRuleOk_sound {c : Clause3} {ps : List Clause3} (h : spineRuleOk c ps = true)
    (hp : ∀ p ∈ ps, Semantic.Means profile3 p.stmt p.scope) : Semantic.Means profile3 c.stmt c.scope := by
  obtain ⟨_, _, _, cs, csc⟩ := c
  cases cs <;> try (simp [spineRuleOk] at h; done)
  rename_i g
  cases g <;> try (simp [spineRuleOk] at h; done)
  cases csc <;> try (simp [spineRuleOk] at h; done)
  exact means_goal fun hc => spine_sound hc (spinePremisesOk_sound h hp)

theorem decideRuleOk_sound {c : Clause3} {ps : List Clause3} (h : decideRuleOk c ps = true)
    (hp : ∀ p ∈ ps, Semantic.Means profile3 p.stmt p.scope) : Semantic.Means profile3 c.stmt c.scope := by
  rcases ps with _ | ⟨sp, _ | ⟨cv, _ | ⟨_, _⟩⟩⟩
  · simp [decideRuleOk] at h
  · simp [decideRuleOk] at h
  rotate_left
  · simp [decideRuleOk] at h
  ·
    have hS := hp sp List.mem_cons_self
    have hC := hp cv (List.mem_cons_of_mem _ List.mem_cons_self)
    obtain ⟨_, _, _, cs, csc⟩ := c
    obtain ⟨_, _, _, sst, ssc⟩ := sp
    obtain ⟨_, _, _, cst, csc'⟩ := cv
    cases cs <;> try (simp [decideRuleOk] at h; done)
    rename_i g
    cases g <;> try (simp [decideRuleOk] at h; done)
    rename_i n m v
    cases v <;> try (simp [decideRuleOk] at h; done)
    cases csc <;> try (simp [decideRuleOk] at h; done)
    cases sst <;> try (simp [decideRuleOk] at h; done)
    rename_i g₁
    cases g₁ <;> try (simp [decideRuleOk] at h; done)
    cases ssc <;> try (simp [decideRuleOk] at h; done)
    cases cst <;> try (simp [decideRuleOk] at h; done)
    rename_i g₂
    cases g₂ <;> try (simp [decideRuleOk] at h; done)
    cases csc' <;> try (simp [decideRuleOk] at h; done)
    simp only [decideRuleOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
    exact means_goal ((means_real_holds hS) (means_real_holds hC))

end GPBinding.Real
