import UDGRope.Basic

/-!
The unit-distance system of a graph, in Mathlib terms (the meaning half of ENCODING-FRAME for
u(22) claims, HW61 G-1). For `G` on `Fin n` the system has variables `x i, y i`, one equation
`(x i - x j)² + (y i - y j)² - 1` per edge and the guard `(x i - x j)² + (y i - y j)²` for every
pair `i < j`. Non-edges carry no constraint, so extra unit distances are allowed (M5 pitfall 4).

- `udg_system_iff`: the system has a real point exactly when `G` has a (non-faithful, injective)
  unit-distance embedding into `ℝ²` (Mathlib's `SimpleGraph.UnitDistEmbedding`).
- `udg_gauge_iff`: pinning one edge `a b` at `(0, 0)`, `(1, 0)` loses no points. Any point moves
  there by the isometry `v ↦ R (v - p a)`, `R` the rotation taking `p b - p a` to `(1, 0)`.
-/

namespace GPBinding.UDG
open UDGRope

/-- A real point of the unit-distance system of `G`. -/
def SysPoint {n : ℕ} (G : SimpleGraph (Fin n)) (x y : Fin n → ℝ) : Prop :=
  (∀ i j, G.Adj i j → (x i - x j) ^ 2 + (y i - y j) ^ 2 - 1 = 0) ∧
    ∀ i j : Fin n, i < j → (x i - x j) ^ 2 + (y i - y j) ^ 2 ≠ 0

/-- **The UDG system's meaning.** The unit-distance system of `G` (one equation per edge, a
distinctness guard per pair, nothing on non-edges) has a real point exactly when `G` has an
injective unit-distance embedding into the Euclidean plane. -/
theorem udg_system_iff {n : ℕ} (G : SimpleGraph (Fin n)) :
    (∃ x y : Fin n → ℝ, (∀ i j, G.Adj i j → (x i - x j) ^ 2 + (y i - y j) ^ 2 - 1 = 0) ∧
      ∀ i j : Fin n, i < j → (x i - x j) ^ 2 + (y i - y j) ^ 2 ≠ 0) ↔
    Nonempty (G.UnitDistEmbedding ℝ²) := by
  constructor
  · rintro ⟨x, y, he, hg⟩
    have inj : Function.Injective fun i => pt (x i) (y i) := by
      intro i j hij
      by_contra hne
      have h0 : (x i - x j) ^ 2 + (y i - y j) ^ 2 = 0 := by
        have := (eq_iff_sq _ _).mp hij; simpa using this
      rcases lt_or_gt_of_ne hne with h | h
      · exact hg i j h h0
      · exact hg j i h (by linear_combination h0)
    refine ⟨⟨⟨_, inj⟩, fun {u v} huv => ?_⟩⟩
    rw [dist_eq_one_iff]
    simpa [sub_eq_zero] using he u v huv
  · rintro ⟨f⟩
    refine ⟨fun i => f.p i 0, fun i => f.p i 1, fun i j h => ?_, fun i j h h0 => ?_⟩
    · have := (dist_eq_one_iff _ _).mp (f.unit_dist h)
      linear_combination this
    · exact h.ne (f.p.injective ((eq_iff_sq _ _).mpr h0))

/-- **Gauge.** For an edge `a b`, the system has a real point exactly when it has one with
`x a = y a = 0`, `x b = 1`, `y b = 0` (a rotation and a translation; both preserve every
squared distance). -/
theorem udg_gauge_iff {n : ℕ} (G : SimpleGraph (Fin n)) {a b : Fin n} (hab : G.Adj a b) :
    (∃ x y, SysPoint G x y) ↔ ∃ x y, SysPoint G x y ∧ x a = 0 ∧ y a = 0 ∧ x b = 1 ∧ y b = 0 := by
  constructor
  · rintro ⟨x, y, he, hg⟩
    set c := x b - x a
    set s := y b - y a
    have hcs : c ^ 2 + s ^ 2 = 1 := by have := he a b hab; linear_combination this
    have key : ∀ i j, (c * (x i - x a) + s * (y i - y a) - (c * (x j - x a) + s * (y j - y a))) ^ 2 +
        (-s * (x i - x a) + c * (y i - y a) - (-s * (x j - x a) + c * (y j - y a))) ^ 2 =
        (x i - x j) ^ 2 + (y i - y j) ^ 2 := fun i j => by
      linear_combination ((x i - x j) ^ 2 + (y i - y j) ^ 2) * hcs
    refine ⟨fun i => c * (x i - x a) + s * (y i - y a), fun i => -s * (x i - x a) + c * (y i - y a),
      ⟨fun i j h => ?_, fun i j h => ?_⟩, by ring, by ring, ?_, by ring⟩
    · rw [key]; exact he i j h
    · rw [key]; exact hg i j h
    · show c * (x b - x a) + s * (y b - y a) = 1
      linear_combination hcs
  · rintro ⟨x, y, h, -⟩
    exact ⟨x, y, h⟩

end GPBinding.UDG
