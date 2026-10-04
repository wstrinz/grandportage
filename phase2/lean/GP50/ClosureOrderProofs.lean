import GP50.ClosureCompleteness
namespace GP50

-- Inclusion is about complete declarations, not just node IDs.
theorem reachable_of_node_subset (nodes other : List SupportNode)
    (inclusion : ∀ node, node ∈ nodes → node ∈ other) :
    ∀ id, Reachable nodes id → Reachable other id := by
  intro id reachable
  induction reachable with
  | fire present requirements supported ih =>
    exact Reachable.fire (inclusion _ present) requirements ih

theorem closure_mem_of_node_subset (nodes other : List SupportNode)
    (inclusion : ∀ node, node ∈ nodes → node ∈ other) :
    ∀ id, id ∈ closure nodes → id ∈ closure other := by
  intro id member
  exact closure_complete other id
    (reachable_of_node_subset nodes other inclusion id
      (closure_reachable nodes id member))

-- Multiplicity and list length may differ: each actual closure uses its own bound.
theorem closure_mem_iff_of_node_mem_iff (nodes other : List SupportNode)
    (sameDeclarations : ∀ node, node ∈ nodes ↔ node ∈ other) (id : Nat) :
    id ∈ closure nodes ↔ id ∈ closure other := by
  constructor
  · exact closure_mem_of_node_subset nodes other
      (fun node present => (sameDeclarations node).mp present) id
  · exact closure_mem_of_node_subset other nodes
      (fun node present => (sameDeclarations node).mpr present) id

theorem closure_mem_iff_of_perm (nodes other : List SupportNode)
    (permutation : List.Perm nodes other) (id : Nat) :
    id ∈ closure nodes ↔ id ∈ closure other :=
  closure_mem_iff_of_node_mem_iff nodes other
    (fun _ => permutation.mem_iff) id

theorem closure_reverse_mem_iff (nodes : List SupportNode) (id : Nat) :
    id ∈ closure nodes.reverse ↔ id ∈ closure nodes := by
  apply closure_mem_iff_of_node_mem_iff
  intro node
  simp

theorem closure_duplicate_list_mem_iff (nodes : List SupportNode) (id : Nat) :
    id ∈ closure (nodes ++ nodes) ↔ id ∈ closure nodes := by
  apply closure_mem_iff_of_node_mem_iff
  intro node
  simp

#print axioms reachable_of_node_subset
#print axioms closure_mem_of_node_subset
#print axioms closure_mem_iff_of_node_mem_iff
#print axioms closure_mem_iff_of_perm
#print axioms closure_reverse_mem_iff
#print axioms closure_duplicate_list_mem_iff
end GP50

