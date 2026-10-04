import GP50.Conflict
import GP50.EventOrderProofs
namespace GP50.Semantic
-- Detection cannot turn contradictory statements into sound claims.
theorem confirmed_conflict_excludes_joint_truth (p : Profile) (overlap : Overlap p)
    (a b : Clause p) (left right : Nat) (finding : ConflictFinding p overlap) (code : overlap.Code)
    (found : assessConflict p overlap a b left right = some finding)
    (inhabited : finding.witness = some code) :
    ¬(Means p a.stmt a.scope ∧ Means p b.stmt b.scope) := by
  unfold assessConflict at found
  split at found
  next contra =>
    cases Option.some.inj found
    obtain ⟨ctx, both⟩ := overlap.sound a.scope b.scope code inhabited
    intro truths
    exact p.contra_sound a.stmt b.stmt ctx contra
      (truths.1 ctx both.1) (truths.2 ctx both.2)
  next => contradiction

theorem release_preserves_complete_state (p : Profile) (overlap : Overlap p)
    (clauses : List (Clause p)) (state : RuntimeState) :
    (reviewRelease p overlap clauses state).state = state := rfl
-- The complete release review inherits actual event-set independence.
theorem release_review_eq_of_mem_iff (p : Profile) (overlap : Overlap p)
    (clauses : List (Clause p)) (admission : Admission) (left right : List Event)
    (same : ∀ event, event ∈ left ↔ event ∈ right) :
    (fold admission left).map (reviewRelease p overlap clauses) =
    (fold admission right).map (reviewRelease p overlap clauses) :=
  congrArg (fun result => result.map (reviewRelease p overlap clauses))
    (EventOrder.fold_eq_of_mem_iff admission left right same)
#print axioms release_review_eq_of_mem_iff
end GP50.Semantic
