import UDGRope.Basic

/-!
The u(22) spine's soundness lemmas (HW61 P4 and G-2). Mathlib only, over the rope's vocabulary.

- `tu_hereditary` (**P4, L2**, artwaste `enum/PRUNING.md` §1 at `ba1c76fd`): if every `N`-point
  set has at most `M` unit pairs, a graph `H` containing a totally unfaithful gadget `T` whose
  pair is non-adjacent in `H` is not an induced subgraph of any unit-distance graph on `N`
  vertices with at least `M` edges. `T` is generic: its total unfaithfulness is a hypothesis,
  discharged for the six gadgets by `UDGRope.gadget*_tu`.
- `CoverComplete`, `spine_sound` (Will, G-2 staging, 2026-10-09): a complete cover of `n`-point
  sets with at least `m` unit pairs by candidate graphs, each with no unit-distance embedding,
  shows that no such set exists.
- `realize_sound` (the G-2 yes bridge): a unit-distance embedding of a graph on `Fin n` with at
  least `m` edges gives `n` points with at least `m` unit pairs.
- `coverComplete_all` and `not_coverComplete_nil` show the definition is satisfiable and not
  vacuous: the list of all graphs on `Fin n` with at least `m` edges is complete, and the empty
  list is not complete for two points at distance 1. `coverComplete_of_all`: so is any list
  containing all of them.
-/

noncomputable section

namespace GPBinding.UDG
open UDGRope
open scoped Finset

/-- Every `n`-point set with at least `m` unit pairs contains a unit-distance copy of a graph of
`L`: an injective map into the set with every edge at distance 1 (extra unit distances allowed). -/
def CoverComplete (n m : ℕ) (L : List (SimpleGraph (Fin n))) : Prop :=
  ∀ P : Finset ℝ², P.card = n → m ≤ unitDistNum P →
    ∃ G ∈ L, ∃ f : G.UnitDistEmbedding ℝ², ∀ v, f.p v ∈ P

/-- **Spine soundness.** A complete cover whose every candidate has no unit-distance embedding
rules out `n` points with `m` unit distances. -/
theorem spine_sound {n m : ℕ} {L : List (SimpleGraph (Fin n))} (hc : CoverComplete n m L)
    (hL : ∀ G ∈ L, IsEmpty (G.UnitDistEmbedding ℝ²)) :
    ¬ ∃ P : Finset ℝ², P.card = n ∧ m ≤ unitDistNum P := by
  rintro ⟨P, hP, hm⟩
  obtain ⟨G, hG, f, -⟩ := hc P hP hm
  exact (hL G hG).false f

/-- The image of an injective map on a finite type, as a `Finset`. -/
theorem card_map_univ {n : ℕ} (f : Fin n ↪ ℝ²) : (Finset.univ.map f).card = n := by simp

/-- An unit-distance embedding's points have at least the graph's edges as unit pairs, plus every
non-edge forced to distance 1. -/
theorem edges_lt_unitDistNum {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (f : G.UnitDistEmbedding ℝ²) {x y : Fin N} (hxy : ¬ G.Adj x y) (hd : dist (f.p x) (f.p y) = 1) :
    #G.edgeFinset < unitDistNum (Finset.univ.map f.p) := by
  classical
  rw [unitDistNum_map]
  have hne : x ≠ y := by rintro rfl; simp at hd
  have hsub : insert s(x, y) G.edgeFinset ⊆ (unitGraph f.p).edgeFinset := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact ⟨hne, hd⟩
    · induction e using Sym2.ind with
      | h u v =>
        have h' : G.Adj u v := by simpa using he
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact ⟨h'.ne, f.unit_dist h'⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simpa using hxy)] at this
  exact this

/-- **The yes bridge.** A unit-distance embedding of a graph on `Fin n` with at least `m` edges
gives `n` distinct points with at least `m` unit pairs. -/
theorem realize_sound {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : Nonempty (G.UnitDistEmbedding ℝ²)) (hm : m ≤ #G.edgeFinset) :
    ∃ P : Finset ℝ², P.card = n ∧ m ≤ unitDistNum P := by
  classical
  obtain ⟨f⟩ := hG
  refine ⟨Finset.univ.map f.p, card_map_univ f.p, ?_⟩
  rw [unitDistNum_map]
  refine hm.trans (Finset.card_le_card fun e he => ?_)
  induction e using Sym2.ind with
  | h u v =>
    have h' : G.Adj u v := by simpa using he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact ⟨h'.ne, f.unit_dist h'⟩

/-- **P4 (L2, the hereditary TU rule).** Let every `N`-point set have at most `M` unit pairs
(`u(N) ≤ M`). Let `T` be totally unfaithful with pair `a b`, copied (not necessarily induced) into
`H` with the pair's image non-adjacent in `H`, and let `H` be an induced subgraph of `G` on `N`
vertices with at least `M` edges. Then `G` has no unit-distance embedding. -/
theorem tu_hereditary {N M : ℕ} (hu : ∀ P : Finset ℝ², P.card = N → unitDistNum P ≤ M)
    {k : ℕ} (T : SimpleGraph (Fin k)) (a b : Fin k)
    (hT : ∀ f : T.UnitDistEmbedding ℝ², dist (f.p a) (f.p b) = 1)
    {W : Type*} (H : SimpleGraph W) (φ : T.Copy H) (hab : ¬ H.Adj (φ a) (φ b))
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (ι : H ↪g G) (hM : M ≤ #G.edgeFinset) :
    IsEmpty (G.UnitDistEmbedding ℝ²) := by
  refine ⟨fun f => ?_⟩
  have hd : dist (f.p (ι (φ a))) (f.p (ι (φ b))) = 1 := hT (f.copy (ι.toCopy.comp φ))
  have hlt := edges_lt_unitDistNum G f (x := ι (φ a)) (y := ι (φ b))
    (by rw [ι.map_adj_iff]; exact hab) hd
  have := hu _ (card_map_univ f.p)
  omega

open Classical in
/-- Sanity: the list of all graphs on `Fin n` with at least `m` edges is a complete cover. -/
theorem coverComplete_all (n m : ℕ) :
    CoverComplete n m (Finset.univ.filter fun G : SimpleGraph (Fin n) => m ≤ #G.edgeFinset).toList := by
  intro P hP hm
  let e : Fin n ≃ P := (P.equivFinOfCardEq hP).symm
  let f : Fin n ↪ ℝ² := e.toEmbedding.trans (Function.Embedding.subtype _)
  have himg : Finset.univ.map f = P := by
    ext q
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact (e i).2
    · intro hq; exact ⟨e.symm ⟨q, hq⟩, by simp [f]⟩
  refine ⟨unitGraph f, ?_, ⟨f, fun h => h.2⟩, fun v => ?_⟩
  · rw [Finset.mem_toList, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have := unitDistNum_map f
    rw [himg] at this
    convert hm using 1
    rw [this]
  · rw [← himg]; exact Finset.mem_map_of_mem _ (Finset.mem_univ v)

open Classical in
/-- A list that contains every graph on `Fin n` with at least `m` edges is a complete cover (the
`exhaustive` cover warrant of `gp cover`, which lists them all). -/
theorem coverComplete_of_all {n m : ℕ} {L : List (SimpleGraph (Fin n))}
    (h : ∀ G : SimpleGraph (Fin n), m ≤ #G.edgeFinset → G ∈ L) : CoverComplete n m L := by
  intro P hP hm
  obtain ⟨G, hG, hf⟩ := coverComplete_all n m P hP hm
  rw [Finset.mem_toList, Finset.mem_filter] at hG
  exact ⟨G, h G hG.2, hf⟩

/-- Sanity: the empty cover is not complete for two points at unit distance. -/
theorem not_coverComplete_nil : ¬ CoverComplete 2 1 [] := by
  intro h
  have hpq : pt 0 0 ≠ pt 1 0 := fun h' => by simpa using congrArg (fun v : ℝ² => v 0) h'
  obtain ⟨G, hG, -⟩ := h {pt 0 0, pt 1 0} (Finset.card_pair hpq) (by
    rw [unitDistNum_eq, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
    refine ⟨s(pt 0 0, pt 1 0), ?_⟩
    simp only [Finset.mem_filter, Finset.mk_mem_sym2_iff, Finset.mem_insert, Finset.mem_singleton,
      true_or, or_true, and_self, Sym2.lift_mk, true_and]
    rw [dist_eq_one_iff]; simp)
  simp at hG

end GPBinding.UDG
