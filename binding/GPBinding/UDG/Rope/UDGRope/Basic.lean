import UDGRope.Defs

/-!
Coordinates in the plane, heredity (P3) and the unit-pair count of an embedded vertex set.

- `dist_eq_one_iff`, `eq_iff_sq`: distance 1 and equality of plane points in coordinates.
- `heredity` (P3, L1): Mathlib's `UnitDistEmbedding.copy`, re-exported.
- `unitDistNum_map`: the unit pairs of `f(V)` for an injective `f` are the edges of the unit graph
  `unitGraph f` (every pair of distinct vertices at distance 1), so the count is its edge count.
-/

noncomputable section

namespace UDGRope
open scoped Finset

theorem dist_sq (p q : ℝ²) : dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Fin.sum_univ_two, Real.dist_eq,
    Real.dist_eq, sq_abs, sq_abs]

theorem dist_eq_one_iff (p q : ℝ²) :
    dist p q = 1 ↔ (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 = 1 := by
  rw [← dist_sq]
  constructor
  · intro h; rw [h]; norm_num
  · intro h
    have h0 : 0 ≤ dist p q := dist_nonneg
    nlinarith [sq_nonneg (dist p q - 1), sq_nonneg (dist p q + 1)]

theorem eq_iff_sq (p q : ℝ²) : p = q ↔ (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 = 0 := by
  constructor
  · rintro rfl; ring
  · intro h
    have h0 : p 0 - q 0 = 0 := by nlinarith [sq_nonneg (p 0 - q 0), sq_nonneg (p 1 - q 1)]
    have h1 : p 1 - q 1 = 0 := by nlinarith [sq_nonneg (p 0 - q 0), sq_nonneg (p 1 - q 1)]
    ext i
    fin_cases i
    · exact sub_eq_zero.mp h0
    · exact sub_eq_zero.mp h1

/-- The plane point with coordinates `(a, b)`. -/
abbrev pt (a b : ℝ) : ℝ² := !₂[a, b]

@[simp] theorem pt_zero (a b : ℝ) : pt a b 0 = a := rfl
@[simp] theorem pt_one (a b : ℝ) : pt a b 1 = b := rfl

/-- **P3 (L1, heredity).** A unit-distance embedding of `G` restricts along any copy of `H` in `G`
(not necessarily induced): Mathlib's `SimpleGraph.UnitDistEmbedding.copy`. -/
def heredity {V W E : Type*} [MetricSpace E] {G : SimpleGraph V} {H : SimpleGraph W}
    (U : G.UnitDistEmbedding E) (f : H.Copy G) : H.UnitDistEmbedding E :=
  U.copy f

theorem heredity_nonempty {V W E : Type*} [MetricSpace E] {G : SimpleGraph V} {H : SimpleGraph W}
    (f : H.Copy G) (h : Nonempty (G.UnitDistEmbedding E)) : Nonempty (H.UnitDistEmbedding E) :=
  h.map fun U => U.copy f

/-! ## Counting unit pairs -/

/-- The unit graph of a point map: distinct vertices at distance 1. -/
def unitGraph {V X : Type*} [MetricSpace X] (f : V → X) : SimpleGraph V where
  Adj u v := u ≠ v ∧ dist (f u) (f v) = 1
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [dist_comm]; exact h.2⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

theorem dist_out {X : Type*} [MetricSpace X] (p : Sym2 X) :
    dist p.out.1 p.out.2 = Sym2.lift ⟨fun a b => dist a b, fun a b => dist_comm a b⟩ p := by
  conv_rhs => rw [← Quot.out_eq p]
  rfl

theorem unitDistNum_eq {X : Type*} [MetricSpace X] (s : Finset X) :
    unitDistNum s = #{p ∈ s.sym2 | Sym2.lift ⟨fun a b => dist a b, fun a b => dist_comm a b⟩ p = 1} := by
  unfold unitDistNum
  congr 1
  ext p
  simp only [Finset.mem_filter, dist_out]

/-- The unit pairs of an injectively embedded vertex set are the edges of the unit graph. -/
theorem unitDistNum_map {V X : Type*} [Fintype V] [MetricSpace X] (f : V ↪ X)
    [DecidableRel (unitGraph f).Adj] :
    unitDistNum (Finset.univ.map f) = #(unitGraph f).edgeFinset := by
  classical
  rw [unitDistNum_eq, Finset.sym2_map, Finset.filter_map, Finset.card_map]
  congr 1
  ext e
  induction e using Sym2.ind with
  | h u v =>
    rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    simp only [Finset.mem_sym2_iff, Finset.mem_univ, implies_true, true_and, Function.comp_apply,
      Function.Embedding.sym2Map_apply, Sym2.map_mk, Sym2.lift_mk, unitGraph]
    constructor
    · intro h
      refine ⟨fun huv => ?_, h⟩
      subst huv
      simp at h
    · exact fun h => h.2

end UDGRope
