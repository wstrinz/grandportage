import GP50.ClosureProofs
namespace GP50
open scoped List

-- Proof-only closure predicate, with the same conjunctive rule as enabled.
def SupportClosed (nodes : List SupportNode) (reached : List Nat) : Prop :=
  ∀ node ∈ nodes, ∀ deps, node.premises = some deps →
    (∀ id ∈ deps, id ∈ reached) → node.id ∈ reached

theorem advance_prior (nodes : List SupportNode) (reached : List Nat) :
    ∀ id ∈ reached, id ∈ advance nodes reached := by
  intro id member
  simp only [advance, List.mem_eraseDups, List.mem_append, List.mem_map, List.mem_filter]
  exact Or.inl member

theorem advance_fire (nodes : List SupportNode) (reached : List Nat)
    (node : SupportNode) (present : node ∈ nodes) (deps : List Nat)
    (requirements : node.premises = some deps)
    (supported : ∀ id ∈ deps, id ∈ reached) :
    node.id ∈ advance nodes reached := by
  have ready : enabled node reached = true := by
    simp only [enabled, requirements]
    exact List.all_eq_true.mpr (fun id member => decide_eq_true (supported id member))
  simp only [advance, List.mem_eraseDups, List.mem_append, List.mem_map, List.mem_filter]
  exact Or.inr ⟨node, ⟨present, ready⟩, rfl⟩

theorem advance_of_closed (nodes : List SupportNode) (reached : List Nat)
    (closed : SupportClosed nodes reached) :
    ∀ id ∈ advance nodes reached, id ∈ reached := by
  intro id member
  simp only [advance, List.mem_eraseDups, List.mem_append, List.mem_map, List.mem_filter] at member
  rcases member with old | ⟨node, ⟨present, ready⟩, rfl⟩
  · exact old
  · cases req : node.premises with
    | none => simp [enabled, req] at ready
    | some deps =>
      apply closed node present deps req
      have allReady : deps.all (fun id => decide (id ∈ reached)) = true := by
        simpa [enabled, req] using ready
      intro id belongs
      exact of_decide_eq_true (List.all_eq_true.mp allReady id belongs)

theorem closed_advance (nodes : List SupportNode) (reached : List Nat)
    (closed : SupportClosed nodes reached) : SupportClosed nodes (advance nodes reached) := by
  intro node present deps requirements supported
  apply advance_prior
  apply closed node present deps requirements
  intro id belongs
  exact advance_of_closed nodes reached closed id (supported id belongs)

-- This generic finite-list lemma counts declaration positions, so repeated IDs
-- do not require a uniqueness invariant.
theorem filter_sublist_of_imp {α : Type} (xs : List α) (p q : α → Bool)
    (implication : ∀ x ∈ xs, p x = true → q x = true) :
    xs.filter p <+ xs.filter q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have tail := ih (fun y hy => implication y (by simp [hy]))
    by_cases hp : p x = true
    · have hq := implication x (by simp) hp
      simpa [hp, hq] using List.Sublist.cons_cons x tail
    · by_cases hq : q x = true
      · simpa [hp, hq] using List.Sublist.cons x tail
      · simpa [hp, hq] using tail

theorem rounds_growth (nodes : List SupportNode) (n : Nat)
    (notClosed : ¬ SupportClosed nodes (rounds nodes n)) :
    (nodes.filter fun node => decide (node.id ∈ rounds nodes n)).length <
      (nodes.filter fun node => decide (node.id ∈ rounds nodes (n+1))).length := by
  have sub : (nodes.filter fun node => decide (node.id ∈ rounds nodes n)) <+
      (nodes.filter fun node => decide (node.id ∈ rounds nodes (n+1))) := by
    apply filter_sublist_of_imp
    intro node _ old
    apply decide_eq_true
    exact advance_prior nodes (rounds nodes n) node.id (of_decide_eq_true old)
  apply Classical.byContradiction
  intro notGrowth
  have equal := sub.eq_of_length_le (Nat.le_of_not_gt notGrowth)
  apply notClosed
  intro node present deps requirements supported
  have new : node ∈ nodes.filter (fun node => decide (node.id ∈ rounds nodes (n+1))) := by
    apply List.mem_filter.mpr
    exact ⟨present, decide_eq_true (advance_fire nodes (rounds nodes n) node present deps requirements supported)⟩
  have old : node ∈ nodes.filter (fun node => decide (node.id ∈ rounds nodes n)) :=
    equal ▸ new
  exact of_decide_eq_true (List.mem_filter.mp old).2

theorem rounds_closed_or_count (nodes : List SupportNode) (n : Nat) :
    SupportClosed nodes (rounds nodes n) ∨
      n ≤ (nodes.filter fun node => decide (node.id ∈ rounds nodes n)).length := by
  classical
  induction n with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ n ih =>
    rcases ih with closed | count
    · exact Or.inl (closed_advance nodes (rounds nodes n) closed)
    · by_cases closed : SupportClosed nodes (rounds nodes n)
      · exact Or.inl (closed_advance nodes (rounds nodes n) closed)
      · exact Or.inr (by have growth := rounds_growth nodes n closed; omega)

theorem closure_closed (nodes : List SupportNode) :
    SupportClosed nodes (closure nodes) := by
  classical
  rcases rounds_closed_or_count nodes nodes.length with closed | count
  · exact closed
  · apply Classical.byContradiction
    intro notClosed
    have growth := rounds_growth nodes nodes.length notClosed
    have bound := List.length_filter_le
      (fun node : SupportNode => decide (node.id ∈ rounds nodes (nodes.length+1))) nodes
    omega

theorem closure_complete (nodes : List SupportNode) :
    ∀ id, Reachable nodes id → id ∈ closure nodes := by
  intro id reachable
  induction reachable with
  | fire present requirements supported ih =>
    exact closure_closed nodes _ present _ requirements ih

theorem closure_mem_iff_reachable (nodes : List SupportNode) (id : Nat) :
    id ∈ closure nodes ↔ Reachable nodes id :=
  ⟨closure_reachable nodes id, closure_complete nodes id⟩

#print axioms closure_closed
#print axioms closure_complete
#print axioms closure_mem_iff_reachable
end GP50

