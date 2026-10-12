import UDGRope.Basic

/-!
**Non-vacuity of P2: the six TU gadgets embed.** For each gadget, an explicit injective
unit-distance embedding into the plane with exact coordinates in `ℚ(√3)`, and the distinguished
pair at distance 1 in that embedding, computed directly from the coordinates (not from the TU
lemma). So `gadget*_tu` quantify over a nonempty type, and their conclusion is realized.

The coordinates are artwaste's diagrams D0, D1 and D2 in `check/PROOFS.md` (`artwasteland/Maths`
at `ba1c76fd4abbd776315621ab85b7381e05352985`, `unit-distance-22/`, MIT), relabelled to the
vertex numbers of `data/tu-gadgets.json`. Gadgets 3, 4 and 5 share D2's points; gadget 4 is
gadget 3's graph with the pair (6, 7), and gadget 5 is gadget 3's graph without the edge 2 6.

| gadget | diagram | vertices 0, 1, 2, … as `(x, y)` with `s = √3` | pair |
|---|---|---|---|
| 0 | D0 | (0,0) (0,1) (½,1+s/2) (½,s/2) (1,0) (1,1) | 1 5 |
| 1 | D1 | (0,s) (0,0) (½,s/2) (-½,s/2) (1,s) (3/2,s/2) (1,0) | 4 5 |
| 2 | D1 | (1,0) (-½,s/2) (½,s/2) (0,0) (3/2,s/2) (1,s) (0,s) | 2 4 |
| 3, 4, 5 | D2 | (0,0) (0,1) (½,s/2) (½,1+s/2) (3/2,1+s/2) (3/2,s/2) (1,0) (1,1) | 3 7; 6 7; 6 7 |

Injectivity uses only `1.7 < √3 < 1.8`; every edge and pair uses only `√3 ^ 2 = 3`.
-/

noncomputable section

namespace UDGRope

theorem sqrt3_sq : √3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)

theorem sqrt3_lo : (1.7 : ℝ) < √3 := by nlinarith [sqrt3_sq, Real.sqrt_nonneg 3]

theorem sqrt3_hi : √3 < (1.8 : ℝ) := by nlinarith [sqrt3_sq, Real.sqrt_nonneg 3]

theorem pt_eq_pt {a b c d : ℝ} : pt a b = pt c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (· 0) h, by simpa using congrArg (· 1) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The point map with coordinate lists `X` and `Y`. -/
def ptsOf {n : ℕ} (X Y : Fin n → ℝ) (i : Fin n) : ℝ² := pt (X i) (Y i)

/-- Distinct vertices with distinct coordinate pairs give an injective point map. -/
theorem ptsOf_injective {n : ℕ} {X Y : Fin n → ℝ} (h : ∀ i j, X i = X j → Y i = Y j → i = j) :
    Function.Injective (ptsOf X Y) :=
  fun i j hij => h i j (pt_eq_pt.1 hij).1 (pt_eq_pt.1 hij).2

/-- An injective point map whose listed edges are unit is a unit-distance embedding of the
graph with those edges. -/
def embOf {n : ℕ} (S : Set (Sym2 (Fin n))) (X Y : Fin n → ℝ) (hinj : Function.Injective (ptsOf X Y))
    (h : ∀ e ∈ S, Sym2.lift ⟨fun a b => (X a - X b) ^ 2 + (Y a - Y b) ^ 2,
      fun a b => by ring⟩ e = 1) : (SimpleGraph.fromEdgeSet S).UnitDistEmbedding ℝ² where
  p := ⟨ptsOf X Y, hinj⟩
  unit_dist {u v} huv := by
    rw [SimpleGraph.fromEdgeSet_adj] at huv
    rw [dist_eq_one_iff]
    simpa [ptsOf] using h _ huv.1

theorem embOf_p {n : ℕ} {S : Set (Sym2 (Fin n))} {X Y : Fin n → ℝ} {hinj h} (i : Fin n) :
    (embOf S X Y hinj h).p i = pt (X i) (Y i) := rfl

/-- Injectivity of coordinate lists: distinct vertices differ in a coordinate. -/
macro "coords_inj" X:ident Y:ident : tactic => `(tactic| (
  intro i j hx hy
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | (exfalso; simp [$X:ident, $Y:ident] at hx hy <;> linarith [sqrt3_lo, sqrt3_hi])))

/-- Every listed edge is unit: split the edge set, then use `√3 ^ 2 = 3`. -/
macro "unit_edges" X:ident Y:ident : tactic => `(tactic| (
  intro e he
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
  repeat' (first | subst he | (obtain h1 | he := he; subst h1))
  all_goals (norm_num [$X:ident, $Y:ident] <;> linarith [sqrt3_sq])))

/-- The distinguished pair is at distance 1, from the coordinates. -/
macro "unit_pair" E:ident X:ident Y:ident : tactic => `(tactic| (
  unfold $E:ident
  rw [embOf_p, embOf_p, dist_eq_one_iff]
  norm_num [$X:ident, $Y:ident] <;> linarith [sqrt3_sq]))

/-! ## Gadget 0 (D0) -/

/-- Gadget 0's coordinates (D0): vertex `i` is at `(gadget0X i, gadget0Y i)`. -/
def gadget0X : Fin 6 → ℝ := ![0, 0, 1 / 2, 1 / 2, 1, 1]
def gadget0Y : Fin 6 → ℝ := ![0, 1, 1 + √3 / 2, √3 / 2, 0, 1]

/-- An exact unit-distance embedding of gadget 0. -/
def gadget0Emb : gadget0.UnitDistEmbedding ℝ² :=
  embOf _ gadget0X gadget0Y (ptsOf_injective (by coords_inj gadget0X gadget0Y))
    (by unit_edges gadget0X gadget0Y)

theorem gadget0_embeds : Nonempty (gadget0.UnitDistEmbedding ℝ²) := ⟨gadget0Emb⟩

/-- Gadget 0's pair (1, 5) is at distance 1 in `gadget0Emb`. -/
theorem gadget0_pair : dist (gadget0Emb.p 1) (gadget0Emb.p 5) = 1 := by
  unit_pair gadget0Emb gadget0X gadget0Y

/-! ## Gadgets 1 and 2 (D1) -/

/-- Gadget 1's coordinates (D1). -/
def gadget1X : Fin 7 → ℝ := ![0, 0, 1 / 2, -1 / 2, 1, 3 / 2, 1]
def gadget1Y : Fin 7 → ℝ := ![√3, 0, √3 / 2, √3 / 2, √3, √3 / 2, 0]

/-- An exact unit-distance embedding of gadget 1. -/
def gadget1Emb : gadget1.UnitDistEmbedding ℝ² :=
  embOf _ gadget1X gadget1Y (ptsOf_injective (by coords_inj gadget1X gadget1Y))
    (by unit_edges gadget1X gadget1Y)

theorem gadget1_embeds : Nonempty (gadget1.UnitDistEmbedding ℝ²) := ⟨gadget1Emb⟩

/-- Gadget 1's pair (4, 5) is at distance 1 in `gadget1Emb`. -/
theorem gadget1_pair : dist (gadget1Emb.p 4) (gadget1Emb.p 5) = 1 := by
  unit_pair gadget1Emb gadget1X gadget1Y

/-- Gadget 2's coordinates (D1). -/
def gadget2X : Fin 7 → ℝ := ![1, -1 / 2, 1 / 2, 0, 3 / 2, 1, 0]
def gadget2Y : Fin 7 → ℝ := ![0, √3 / 2, √3 / 2, 0, √3 / 2, √3, √3]

/-- An exact unit-distance embedding of gadget 2. -/
def gadget2Emb : gadget2.UnitDistEmbedding ℝ² :=
  embOf _ gadget2X gadget2Y (ptsOf_injective (by coords_inj gadget2X gadget2Y))
    (by unit_edges gadget2X gadget2Y)

theorem gadget2_embeds : Nonempty (gadget2.UnitDistEmbedding ℝ²) := ⟨gadget2Emb⟩

/-- Gadget 2's pair (2, 4) is at distance 1 in `gadget2Emb`. -/
theorem gadget2_pair : dist (gadget2Emb.p 2) (gadget2Emb.p 4) = 1 := by
  unit_pair gadget2Emb gadget2X gadget2Y

/-! ## Gadgets 3, 4 and 5 (D2) -/

/-- The coordinates of gadgets 3, 4 and 5 (D2). -/
def gadget3X : Fin 8 → ℝ := ![0, 0, 1 / 2, 1 / 2, 3 / 2, 3 / 2, 1, 1]
def gadget3Y : Fin 8 → ℝ := ![0, 1, √3 / 2, 1 + √3 / 2, 1 + √3 / 2, √3 / 2, 0, 1]

theorem gadget3_inj : Function.Injective (ptsOf gadget3X gadget3Y) :=
  ptsOf_injective (by coords_inj gadget3X gadget3Y)

/-- An exact unit-distance embedding of gadget 3's graph (gadgets 3 and 4). -/
def gadget3Emb : gadget3.UnitDistEmbedding ℝ² :=
  embOf _ gadget3X gadget3Y gadget3_inj (by unit_edges gadget3X gadget3Y)

/-- An exact unit-distance embedding of gadget 5, on the same points. -/
def gadget5Emb : gadget5.UnitDistEmbedding ℝ² :=
  embOf _ gadget3X gadget3Y gadget3_inj (by unit_edges gadget3X gadget3Y)

theorem gadget3_embeds : Nonempty (gadget3.UnitDistEmbedding ℝ²) := ⟨gadget3Emb⟩

/-- Gadget 4 is gadget 3's graph with the pair (6, 7), so its embedding is gadget 3's. -/
theorem gadget4_embeds : Nonempty (gadget3.UnitDistEmbedding ℝ²) := ⟨gadget3Emb⟩

theorem gadget5_embeds : Nonempty (gadget5.UnitDistEmbedding ℝ²) := ⟨gadget5Emb⟩

/-- Gadget 3's pair (3, 7) is at distance 1 in `gadget3Emb`. -/
theorem gadget3_pair : dist (gadget3Emb.p 3) (gadget3Emb.p 7) = 1 := by
  unit_pair gadget3Emb gadget3X gadget3Y

/-- Gadget 4's pair (6, 7) is at distance 1 in `gadget3Emb`. -/
theorem gadget4_pair : dist (gadget3Emb.p 6) (gadget3Emb.p 7) = 1 := by
  unit_pair gadget3Emb gadget3X gadget3Y

/-- Gadget 5's pair (6, 7) is at distance 1 in `gadget5Emb`. -/
theorem gadget5_pair : dist (gadget5Emb.p 6) (gadget5Emb.p 7) = 1 := by
  unit_pair gadget5Emb gadget3X gadget3Y

end UDGRope
