import GP50.ConflictProofs
import GP50.NarrowingAdmissionProofs
namespace GP50.Semantic
private theorem supported_warrant_held (admission : Admission) (snapshot : Snapshot)
    (w : Warrant) (present : w ∈ snapshot.warrants)
    (supported : w.id ∈ (evaluate admission snapshot).supports) :
    held (evaluate admission snapshot) w.claim = true := by
  simp only [held, evaluate, projectClaims, canonicalIds, List.contains_iff_mem,
    List.mem_mergeSort, List.mem_eraseDups, List.mem_map, List.mem_filter]
  exact ⟨w, ⟨present, supported⟩, rfl⟩

-- This is conditional on semantic soundness of the actual evaluated held set.
-- A confirmed alarm consequently diagnoses a breached assumption or binding.
theorem sound_evaluate_conflict_has_no_witness (p : Profile) (overlap : Overlap p)
    (clauses : List (Clause p)) (admission : Admission) (snapshot : Snapshot)
    (sound : ∀ claim, held (evaluate admission snapshot) claim = true →
      ClaimMeaning p clauses claim)
    (finding : ConflictFinding p overlap)
    (present : finding ∈ conflictFindings p overlap clauses (evaluate admission snapshot)) :
    finding.witness = none := by
  unfold conflictFindings at present
  simp only [List.mem_flatMap, List.mem_filterMap] at present
  rcases present with ⟨a, ha, b, hb, found⟩
  split at found
  next checked =>
    simp only [Bool.and_eq_true, List.contains_iff_mem] at checked
    cases left : boundClause p clauses a with
    | none => simp [left] at found
    | some ac =>
      cases right : boundClause p clauses b with
      | none => simp [left, right] at found
      | some bc =>
        have assessed : assessConflict p overlap ac bc a.id b.id = some finding := by
          simpa only [left, right] using found
        have ar := boundClause_registered p clauses a ac left
        have br := boundClause_registered p clauses b bc right
        have leftTruth := (sound a.claim (supported_warrant_held admission snapshot a ha checked.1.2)).2 ac ar.2.1 ar.2.2
        have rightTruth := (sound b.claim (supported_warrant_held admission snapshot b hb checked.2)).2 bc br.2.1 br.2.2
        cases inhabited : finding.witness with
        | none => rfl
        | some code =>
          exact False.elim ((confirmed_conflict_excludes_joint_truth p overlap ac bc a.id b.id
            finding code assessed inhabited) ⟨leftTruth, rightTruth⟩)
  next => simp at found
-- The actual narrowed fold obtains that semantic soundness from its validator contracts.
theorem sound_fold_conflict_has_no_witness (p : Profile) (overlap : Overlap p)
    (clauses : List (Clause p)) (base : Admission) (events : List Event) (state : RuntimeState)
    (baseSound : BaseValidatorSound p clauses base state.snapshot)
    (folded : fold (withNarrowing p clauses base) events = .ok state)
    (finding : ConflictFinding p overlap)
    (present : finding ∈ conflictFindings p overlap clauses state) : finding.witness = none := by
  unfold fold at folded
  cases resolved : resolve events with
  | error message => simp [resolved] at folded
  | ok snapshot =>
    rw [resolved] at folded
    have stateEq : evaluate (withNarrowing p clauses base) snapshot = state := Except.ok.inj folded
    subst state
    apply sound_evaluate_conflict_has_no_witness p overlap clauses
      (withNarrowing p clauses base) snapshot _ finding present
    exact evaluate_held_meaning p clauses base snapshot
      (resolve_warrant_ids_nodup events snapshot resolved) baseSound

#print axioms sound_fold_conflict_has_no_witness
#print axioms sound_evaluate_conflict_has_no_witness
end GP50.Semantic
