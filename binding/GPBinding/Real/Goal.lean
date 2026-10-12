import GPBinding.UDG.Frame
import GPProfile.Real.Goal

/-!
The meanings of the DECIDE goal family (release plan A2, `GPProfile.Real.GoalStmt`), over the
Euclidean plane `EuclideanSpace ℝ (Fin 2)`. They do not depend on the field context: the family is
held at scope `real`, which contains ℝ itself.

- Q(n, m) (`GoalQ`): some `n` points of the plane have at least `m` unit distances (`unitDistNum`).
- `goal n m true` means Q(n, m); `goal n m false` means ¬Q(n, m).
- `cover n m L` means `CoverComplete n m L`, each edge list of `L` read as a graph on `Fin n`
  through `GPProfile.UDG.Data.graph` (`goalGraph`).
- `spine n m L` means `CoverComplete n m L → ¬Q(n, m)`.
-/

noncomputable section

namespace GPBinding.Real
open GPProfile GPProfile.Real GPProfile.UDG GPBinding.UDG UDGRope

/-- Q(n, m): some `n` points of the plane have at least `m` unit distances. -/
def GoalQ (n m : ℕ) : Prop := ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card = n ∧ m ≤ unitDistNum P

/-- An edge list as a graph on `Fin n` (out-of-range pairs name no edge; the gauge plays no part). -/
def goalGraph (n : ℕ) (l : EdgeList) : SimpleGraph (Fin n) := (⟨n, l, false⟩ : Data).graph

def goalGraphs (n : ℕ) (L : List EdgeList) : List (SimpleGraph (Fin n)) := L.map (goalGraph n)

/-- The truth of a goal-family statement. -/
def GoalHolds : GoalStmt → Prop
  | .goal n m true => GoalQ n m
  | .goal n m false => ¬ GoalQ n m
  | .cover n m L => CoverComplete n m (goalGraphs n L)
  | .spine n m L => CoverComplete n m (goalGraphs n L) → ¬ GoalQ n m

/-- Only Q and its negation contradict. -/
theorem goal_contra_sound {a b : GoalStmt} (h : a.contra b = true) (ha : GoalHolds a) (hb : GoalHolds b) :
    False := by
  cases a with
  | goal n m v =>
    cases b with
    | goal n' m' v' =>
      simp only [GoalStmt.contra, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
      obtain ⟨⟨rfl, rfl⟩, hv⟩ := h
      cases v <;> cases v' <;> simp at hv
      · exact ha hb
      · exact hb ha
    | cover _ _ _ => simp [GoalStmt.contra] at h
    | spine _ _ _ => simp [GoalStmt.contra] at h
  | cover _ _ _ => simp [GoalStmt.contra] at h
  | spine _ _ _ => simp [GoalStmt.contra] at h

end GPBinding.Real
