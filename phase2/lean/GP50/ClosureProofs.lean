import GP50.Closure
namespace GP50
theorem advance_reachable (nodes : List SupportNode) (reached : List Nat)
    (prior : ∀ id ∈ reached, Reachable nodes id) :
    ∀ id ∈ advance nodes reached, Reachable nodes id := by
  intro id member
  simp only [advance, List.mem_eraseDups, List.mem_append, List.mem_map,
    List.mem_filter] at member
  rcases member with old | ⟨node, ⟨present, ready⟩, rfl⟩
  · exact prior id old
  · cases req : node.premises with
    | none => simp [enabled, req] at ready
    | some deps =>
      apply Reachable.fire present req
      intro dep belongs
      apply prior dep
      have allReady : deps.all (fun d => decide (d ∈ reached)) = true := by
        simpa [enabled, req] using ready
      exact of_decide_eq_true (List.all_eq_true.mp allReady dep belongs)
theorem rounds_reachable (nodes : List SupportNode) (n : Nat) :
    ∀ id ∈ rounds nodes n, Reachable nodes id := by
  induction n with
  | zero => simp [rounds]
  | succ n ih => exact advance_reachable nodes (rounds nodes n) ih
theorem closure_reachable (nodes : List SupportNode) :
    ∀ id ∈ closure nodes, Reachable nodes id :=
  rounds_reachable nodes nodes.length
theorem reachability_sound (nodes : List SupportNode) (Meaning : Nat → Prop)
    (contracts : ∀ node ∈ nodes, ∀ deps, node.premises = some deps →
      (∀ id ∈ deps, Meaning id) → Meaning node.id) :
    ∀ id, Reachable nodes id → Meaning id := by
  intro id reachable
  induction reachable with
  | fire member requirements supported ih =>
    exact contracts _ member _ requirements ih
theorem closure_sound (nodes : List SupportNode) (Meaning : Nat → Prop)
    (contracts : ∀ node ∈ nodes, ∀ deps, node.premises = some deps →
      (∀ id ∈ deps, Meaning id) → Meaning node.id) :
    ∀ id ∈ closure nodes, Meaning id := by
  intro id member
  exact reachability_sound nodes Meaning contracts id (closure_reachable nodes id member)
#print axioms closure_reachable
#print axioms closure_sound
end GP50
