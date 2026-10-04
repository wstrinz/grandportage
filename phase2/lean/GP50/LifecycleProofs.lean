import GP50.Entry
import GP50.ClosureCompleteness
import GP50.ClosureOrderProofs
-- Kernel lifecycle, retraction and totality properties (promoted from Tests/ at Phase 2.5).
namespace GP50.LifecycleProperties
open GP50

-- A retracted warrant keeps its node but loses its requirements, exactly as `requirements`
-- returns `none` for a warrant that is no longer live.
def retractNode (w : Nat) (nodes : List SupportNode) : List SupportNode :=
  nodes.map fun n => if n.id = w then {n with premises := none} else n

-- Derivations in the original support graph that never fire the retracted node.
inductive Avoiding (nodes : List SupportNode) (w : Nat) : Nat → Prop where
  | fire {node : SupportNode} {deps : List Nat}
    (member : node ∈ nodes) (fresh : node.id ≠ w) (requirements : node.premises = some deps)
    (supported : ∀ id ∈ deps, Avoiding nodes w id) : Avoiding nodes w node.id

-- Retraction invalidates exactly its dependents: what stays reachable is precisely what
-- has some derivation avoiding the retracted warrant.
theorem retract_reachable_iff (nodes : List SupportNode) (w id : Nat) :
    Reachable (retractNode w nodes) id ↔ Avoiding nodes w id := by
  constructor
  · intro reachable
    induction reachable with
    | @fire node deps member requirements _ ih =>
      rcases List.mem_map.mp member with ⟨n,present,same⟩
      by_cases hit : n.id = w
      · simp only [hit,if_true] at same
        subst same
        simp at requirements
      · simp only [hit,if_false] at same
        subst same
        exact Avoiding.fire present hit requirements ih
  · intro avoiding
    induction avoiding with
    | @fire node deps member fresh requirements _ ih =>
      have kept : node ∈ retractNode w nodes :=
        List.mem_map.mpr ⟨node,member,by simp [fresh]⟩
      exact Reachable.fire kept requirements ih
theorem retract_closure_iff (nodes : List SupportNode) (w id : Nat) :
    id ∈ closure (retractNode w nodes) ↔ Avoiding nodes w id :=
  (closure_mem_iff_reachable _ id).trans (retract_reachable_iff nodes w id)
-- The retracted warrant itself never survives, and survivors were already supported.
theorem retracted_not_supported (nodes : List SupportNode) (w : Nat) : ¬ Avoiding nodes w w := by
  intro avoiding
  cases avoiding with
  | fire _ fresh _ _ => exact fresh rfl
theorem avoiding_reachable (nodes : List SupportNode) (w id : Nat) (h : Avoiding nodes w id) :
    Reachable nodes id := by
  induction h with
  | fire member _ requirements _ ih => exact Reachable.fire member requirements ih
-- Glue to the runtime: a non-live warrant contributes no requirements.
theorem requirements_not_live (admission : Admission) (snapshot : Snapshot) (w : Warrant)
    (dead : live snapshot w = false) : requirements admission snapshot w = none := by
  simp [requirements,dead]
-- A failed or timed-out attempt contributes a node with no requirements; adding nodes never
-- removes support, so failed retries cannot revoke independent support.
theorem attempt_requirements (admission : Admission) (snapshot : Snapshot) (w : Warrant)
    (status : AttemptStatus) (attempt : w.evidence = .attempt status) :
    requirements admission snapshot w = none := by
  unfold requirements
  split
  · rfl
  · rw [attempt]
theorem extra_nodes_keep_support (nodes extra : List SupportNode) (id : Nat)
    (h : Reachable nodes id) : Reachable (nodes ++ extra) id :=
  reachable_of_node_subset nodes (nodes ++ extra) (fun _ m => List.mem_append_left _ m) id h
-- Circular support never bootstraps: without any requirement-free node nothing is reachable.
theorem no_bootstrap (nodes : List SupportNode)
    (noRoot : ∀ n ∈ nodes, ∀ deps, n.premises = some deps → deps ≠ []) :
    ∀ id, ¬ Reachable nodes id := by
  intro id reachable
  induction reachable with
  | @fire node deps member requirements supported ih =>
    match deps, noRoot node member deps requirements, supported, ih with
    | d :: _, _, _, ih => exact ih d (List.mem_cons_self ..)
-- Determinism and totality: the fold is an ordinary total function returning a result or a
-- named malformed-input error; its value depends only on the event set (fold_eq_of_mem_iff).
theorem fold_total (admission : Admission) (events : List Event) :
    (∃ state, fold admission events = .ok state) ∨ (∃ message, fold admission events = .error message) := by
  cases h : fold admission events with
  | ok state => exact .inl ⟨state,rfl⟩
  | error message => exact .inr ⟨message,rfl⟩

end GP50.LifecycleProperties
