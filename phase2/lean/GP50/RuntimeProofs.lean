import GP50.Runtime
import GP50.ClosureCompleteness
namespace GP50
theorem mem_canonicalIds (xs : List Nat) (id : Nat) :
    id ∈ canonicalIds xs ↔ id ∈ xs := by
  simp [canonicalIds]

-- Completeness of the actual projection, not a caller-supplied support list.
theorem held_evaluate_iff (admission : Admission) (snapshot : Snapshot) (claim : Nat) :
    held (evaluate admission snapshot) claim = true ↔
      ∃ warrant ∈ snapshot.warrants, warrant.claim = claim ∧
        Reachable (supportNodes admission snapshot) warrant.id := by
  simp only [held, evaluate, projectClaims, List.contains_iff_mem, mem_canonicalIds,
    List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨warrant, ⟨present, supported⟩, conclusion⟩
    exact ⟨warrant, present, conclusion,
      (closure_mem_iff_reachable _ _).mp supported⟩
  · rintro ⟨warrant, present, conclusion, reachable⟩
    exact ⟨warrant, ⟨present, (closure_mem_iff_reachable _ _).mpr reachable⟩, conclusion⟩

theorem held_fold_iff (admission : Admission) (events : List Event)
    (state : RuntimeState) (success : fold admission events = .ok state) :
    ∃ snapshot, resolve events = .ok snapshot ∧
      ∀ claim, held state claim = true ↔
        ∃ warrant ∈ snapshot.warrants, warrant.claim = claim ∧
          Reachable (supportNodes admission snapshot) warrant.id := by
  cases resolved : resolve events with
  | error message =>
    simp only [fold, resolved] at success
    change Except.error message = Except.ok state at success
    cases success
  | ok snapshot =>
    simp only [fold, resolved] at success
    change Except.ok (evaluate admission snapshot) = Except.ok state at success
    have stateEq : evaluate admission snapshot = state := Except.ok.inj success
    subst state
    exact ⟨snapshot, rfl, held_evaluate_iff admission snapshot⟩

#print axioms held_fold_iff

#print axioms held_evaluate_iff
end GP50
