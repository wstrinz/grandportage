import UDGRope.Rhombus

/-!
**P2, the six totally unfaithful (TU) gadgets.** For each gadget of artwaste's
`data/tu-gadgets.json` (`artwasteland/Maths` at `ba1c76fd`): the distinguished pair is not an
edge, and in every injective unit-distance embedding into the plane its displacement equals an
edge's, so the pair is at distance 1. Each proof is the integer combination of rhombus relations
(P1) given in artwaste's `check/PROOFS.md`, with the cycles named there; `R(a,b,c,d)` is
`p a - p b + p c - p d`.

| gadget | pair | combination | forced equal to edge |
|---|---|---|---|
| 0 | 1 5 | `-R(0,1,2,3) + R(2,3,4,5)` | 0 4 |
| 1 | 4 5 | `-R(0,3,2,4) + R(1,3,2,6) - R(1,2,5,6)` | 0 2 |
| 2 | 2 4 | `-R(0,2,1,3) + R(0,2,5,4) + R(1,3,2,6) - R(1,2,5,6)` | 1 2 |
| 3 | 3 7 | `R(0,1,3,2) - R(0,2,5,6) + R(1,3,4,7) - R(2,3,4,5)` | 2 6 |
| 4 | 6 7 | `-R(0,2,5,6) + R(1,3,4,7) - R(2,3,4,5)` (gadget 3's graph) | 0 1 |
| 5 | 6 7 | the same, without edge 2 6 | 0 1 |
-/

namespace UDGRope

/-- Equal displacement to an edge's gives distance 1. -/
theorem dist_of_disp {V : Type*} {G : SimpleGraph V} (f : G.UnitDistEmbedding ℝ²) {a b u v : V}
    (huv : G.Adj u v) (h : f.p a - f.p b = f.p u - f.p v) : dist (f.p a) (f.p b) = 1 := by
  rw [dist_eq_norm, h, ← dist_eq_norm]
  exact f.unit_dist huv

/-- **Gadget 0** is totally unfaithful: pair (1, 5), forced equal to edge 0 4. -/
theorem gadget0_tu :
    ¬ gadget0.Adj 1 5 ∧ ∀ f : gadget0.UnitDistEmbedding ℝ², dist (f.p 1) (f.p 5) = 1 := by
  refine ⟨by simp [gadget0], fun f => dist_of_disp f (u := 0) (v := 4) (by simp [gadget0]) ?_⟩
  have r1 := rhombus f (a := 0) (b := 1) (c := 2) (d := 3) (by simp [gadget0]) (by simp [gadget0])
    (by simp [gadget0]) (by simp [gadget0]) (by decide) (by decide)
  have r2 := rhombus f (a := 2) (b := 3) (c := 4) (d := 5) (by simp [gadget0]) (by simp [gadget0])
    (by simp [gadget0]) (by simp [gadget0]) (by decide) (by decide)
  linear_combination (norm := module) -r1 + r2

/-- **Gadget 1** is totally unfaithful: pair (4, 5), forced equal to edge 0 2. -/
theorem gadget1_tu :
    ¬ gadget1.Adj 4 5 ∧ ∀ f : gadget1.UnitDistEmbedding ℝ², dist (f.p 4) (f.p 5) = 1 := by
  refine ⟨by simp [gadget1], fun f => dist_of_disp f (u := 0) (v := 2) (by simp [gadget1]) ?_⟩
  have r2 := rhombus f (a := 0) (b := 3) (c := 2) (d := 4) (by simp [gadget1]) (by simp [gadget1])
    (by simp [gadget1]) (by simp [gadget1]) (by decide) (by decide)
  have r3 := rhombus f (a := 1) (b := 3) (c := 2) (d := 6) (by simp [gadget1]) (by simp [gadget1])
    (by simp [gadget1]) (by simp [gadget1]) (by decide) (by decide)
  have r4 := rhombus f (a := 1) (b := 2) (c := 5) (d := 6) (by simp [gadget1]) (by simp [gadget1])
    (by simp [gadget1]) (by simp [gadget1]) (by decide) (by decide)
  linear_combination (norm := module) -r2 + r3 - r4

/-- **Gadget 2** is totally unfaithful: pair (2, 4), forced equal to edge 1 2. -/
theorem gadget2_tu :
    ¬ gadget2.Adj 2 4 ∧ ∀ f : gadget2.UnitDistEmbedding ℝ², dist (f.p 2) (f.p 4) = 1 := by
  refine ⟨by simp [gadget2], fun f => dist_of_disp f (u := 1) (v := 2) (by simp [gadget2]) ?_⟩
  have r1 := rhombus f (a := 0) (b := 2) (c := 1) (d := 3) (by simp [gadget2]) (by simp [gadget2])
    (by simp [gadget2]) (by simp [gadget2]) (by decide) (by decide)
  have r2 := rhombus f (a := 0) (b := 2) (c := 5) (d := 4) (by simp [gadget2]) (by simp [gadget2])
    (by simp [gadget2]) (by simp [gadget2]) (by decide) (by decide)
  have r3 := rhombus f (a := 1) (b := 3) (c := 2) (d := 6) (by simp [gadget2]) (by simp [gadget2])
    (by simp [gadget2]) (by simp [gadget2]) (by decide) (by decide)
  have r4 := rhombus f (a := 1) (b := 2) (c := 5) (d := 6) (by simp [gadget2]) (by simp [gadget2])
    (by simp [gadget2]) (by simp [gadget2]) (by decide) (by decide)
  linear_combination (norm := module) -r1 + r2 + r3 - r4

/-- **Gadget 3** is totally unfaithful: pair (3, 7), forced equal to edge 2 6. -/
theorem gadget3_tu :
    ¬ gadget3.Adj 3 7 ∧ ∀ f : gadget3.UnitDistEmbedding ℝ², dist (f.p 3) (f.p 7) = 1 := by
  refine ⟨by simp [gadget3], fun f => dist_of_disp f (u := 2) (v := 6) (by simp [gadget3]) ?_⟩
  have r1 := rhombus f (a := 0) (b := 1) (c := 3) (d := 2) (by simp [gadget3]) (by simp [gadget3])
    (by simp [gadget3]) (by simp [gadget3]) (by decide) (by decide)
  have r2 := rhombus f (a := 0) (b := 2) (c := 5) (d := 6) (by simp [gadget3]) (by simp [gadget3])
    (by simp [gadget3]) (by simp [gadget3]) (by decide) (by decide)
  have r3 := rhombus f (a := 1) (b := 3) (c := 4) (d := 7) (by simp [gadget3]) (by simp [gadget3])
    (by simp [gadget3]) (by simp [gadget3]) (by decide) (by decide)
  have r4 := rhombus f (a := 2) (b := 3) (c := 4) (d := 5) (by simp [gadget3]) (by simp [gadget3])
    (by simp [gadget3]) (by simp [gadget3]) (by decide) (by decide)
  linear_combination (norm := module) r1 - r2 + r3 - r4

/-- **Gadget 4** (gadget 3's graph) is totally unfaithful: pair (6, 7), forced equal to edge 0 1. -/
theorem gadget4_tu :
    ¬ gadget3.Adj 6 7 ∧ ∀ f : gadget3.UnitDistEmbedding ℝ², dist (f.p 6) (f.p 7) = 1 := by
  refine ⟨by simp [gadget3], fun f => dist_of_disp f (u := 0) (v := 1) (by simp [gadget3]) ?_⟩
  have r2 := rhombus f (a := 0) (b := 2) (c := 5) (d := 6) (by simp [gadget3]) (by simp [gadget3])
    (by simp [gadget3]) (by simp [gadget3]) (by decide) (by decide)
  have r3 := rhombus f (a := 1) (b := 3) (c := 4) (d := 7) (by simp [gadget3]) (by simp [gadget3])
    (by simp [gadget3]) (by simp [gadget3]) (by decide) (by decide)
  have r4 := rhombus f (a := 2) (b := 3) (c := 4) (d := 5) (by simp [gadget3]) (by simp [gadget3])
    (by simp [gadget3]) (by simp [gadget3]) (by decide) (by decide)
  linear_combination (norm := module) -r2 + r3 - r4

/-- **Gadget 5** (gadget 3 without edge 2 6) is totally unfaithful: pair (6, 7), forced equal to
edge 0 1. -/
theorem gadget5_tu :
    ¬ gadget5.Adj 6 7 ∧ ∀ f : gadget5.UnitDistEmbedding ℝ², dist (f.p 6) (f.p 7) = 1 := by
  refine ⟨by simp [gadget5], fun f => dist_of_disp f (u := 0) (v := 1) (by simp [gadget5]) ?_⟩
  have r2 := rhombus f (a := 0) (b := 2) (c := 5) (d := 6) (by simp [gadget5]) (by simp [gadget5])
    (by simp [gadget5]) (by simp [gadget5]) (by decide) (by decide)
  have r3 := rhombus f (a := 1) (b := 3) (c := 4) (d := 7) (by simp [gadget5]) (by simp [gadget5])
    (by simp [gadget5]) (by simp [gadget5]) (by decide) (by decide)
  have r4 := rhombus f (a := 2) (b := 3) (c := 4) (d := 5) (by simp [gadget5]) (by simp [gadget5])
    (by simp [gadget5]) (by simp [gadget5]) (by decide) (by decide)
  linear_combination (norm := module) -r2 + r3 - r4

end UDGRope
