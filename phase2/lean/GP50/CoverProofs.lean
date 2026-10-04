import GP50.Cover
import GP50.NarrowingAdmissionProofs
namespace GP50.Semantic

theorem checked_cover_sound (p : Profile) (coverage : Coverage p)
    (destination : Clause p) (branches : List (Clause p))
    (accepted : checkCover p coverage destination branches = true)
    (branchTruth : ∀ branch ∈ branches, Means p branch.stmt branch.scope) :
    Means p destination.stmt destination.scope := by
  have checks : branches.all (fun branch => p.same destination.stmt branch.stmt &&
      (destination.binding.statementHash == branch.binding.statementHash &&
       destination.binding.modelHash == branch.binding.modelHash &&
       destination.binding.inputHashes == branch.binding.inputHashes &&
       destination.binding.kernelVersion == branch.binding.kernelVersion)) = true ∧
      coverage.covers destination.scope (branches.map (·.scope)) = true := by
    simpa only [checkCover, Bool.and_eq_true] using accepted
  intro ctx inDestination
  rcases coverage.sound destination.scope (branches.map (·.scope)) ctx checks.2 inDestination with
    ⟨scope, scopePresent, inBranch⟩
  rcases List.mem_map.mp scopePresent with ⟨branch, branchPresent, scopeEq⟩
  have same : p.same destination.stmt branch.stmt = true := by
    have identityChecks := (List.all_eq_true.mp checks.1) branch branchPresent
    simp only [Bool.and_eq_true] at identityChecks
    exact identityChecks.1
  have statementEq := p.same_sound destination.stmt branch.stmt same
  rw [statementEq]
  rw [← scopeEq] at inBranch
  exact branchTruth branch branchPresent ctx inBranch

#print axioms checked_cover_sound

theorem boundClauses_mapM_means (p : Semantic.Profile) (clauses : List (Semantic.Clause p))
    (premises : List Warrant) (branches : List (Semantic.Clause p))
    (mapped : premises.mapM (Semantic.boundClause p clauses) = some branches)
    (truth : ∀ premise ∈ premises, Semantic.ClaimMeaning p clauses premise.claim) :
    ∀ branch ∈ branches, Semantic.Means p branch.stmt branch.scope := by
  induction premises generalizing branches with
  | nil =>
    simp at mapped
    subst branches
    simp
  | cons premise rest ih =>
    cases found : Semantic.boundClause p clauses premise with
    | none => simp [List.mapM_cons, found] at mapped
    | some chosen =>
      cases tailMapped : rest.mapM (Semantic.boundClause p clauses) with
      | none => simp [List.mapM_cons, found, tailMapped] at mapped
      | some tail =>
        have branchesEq : chosen :: tail = branches := by
          simpa [List.mapM_cons, found, tailMapped] using mapped
        subst branches
        intro branch present
        rcases List.mem_cons.mp present with equal | tailPresent
        · subst branch
          have info := Semantic.boundClause_registered p clauses premise chosen found
          exact (truth premise (List.mem_cons_self)).2 chosen info.2.1 info.2.2
        · exact ih tail tailMapped (fun w member => truth w (List.mem_cons_of_mem _ member))
            branch tailPresent

end GP50.Semantic
