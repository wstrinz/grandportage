import GP50.NarrowingProofs
import GP50.ResolveProofs
namespace GP50.Semantic

def ClaimMeaning (p : Profile) (clauses : List (Clause p)) (claim : Nat) : Prop :=
  (∃ clause ∈ clauses, clause.key = claim) ∧
  ∀ clause ∈ clauses, clause.key = claim → Means p clause.stmt clause.scope

def WarrantMeaning (p : Profile) (clauses : List (Clause p))
    (snapshot : Snapshot) (id : Nat) : Prop :=
  ∃ w ∈ snapshot.warrants, w.id = id ∧ ClaimMeaning p clauses w.claim

-- Only the non-overridden validators have explicit admission contracts.
structure BaseValidatorSound (p : Profile) (clauses : List (Clause p))
    (base : Admission) (snapshot : Snapshot) : Prop where
  receipt : ∀ w ∈ snapshot.warrants, ∀ data,
    base.receipt w data = true → WarrantMeaning p clauses snapshot w.id
  proof : ∀ w ∈ snapshot.warrants, ∀ declaration,
    base.proof w declaration = true → WarrantMeaning p clauses snapshot w.id
  rule : ∀ w ∈ snapshot.warrants, ∀ premises side,
    base.rule w premises side = true →
    (∀ premise ∈ premises, premise ∈ snapshot.warrants) →
    (∀ premise ∈ premises, WarrantMeaning p clauses snapshot premise.id) →
    WarrantMeaning p clauses snapshot w.id

theorem boundClause_registered (p : Profile) (clauses : List (Clause p))
    (w : Warrant) (clause : Clause p) (found : boundClause p clauses w = some clause) :
    (clauses.map (·.key)).Nodup ∧ clause ∈ clauses ∧ clause.key = w.claim := by
  unfold boundClause at found
  split at found
  · contradiction
  · rename_i distinct
    have sameLength : (clauses.map (·.key)).eraseDups.length = clauses.length := by
      simpa using distinct
    have nodup := nodup_of_eraseDups_length_eq (clauses.map (·.key))
      (by simpa only [List.length_map] using sameLength)
    have member : clause ∈ clauses := List.mem_of_find?_eq_some found
    have matching := List.find?_some (p := fun c : Clause p =>
      c.key == w.claim && c.version == w.version && c.binding == w.binding) found
    simp only [Bool.and_eq_true, beq_iff_eq] at matching
    exact ⟨nodup, member, matching.1.1⟩

theorem acceptsNarrow_claim_meaning (p : Profile) (clauses : List (Clause p))
    (dest source : Warrant) (accepted : acceptsNarrow p clauses dest source = true)
    (sourceTrue : ClaimMeaning p clauses source.claim) : ClaimMeaning p clauses dest.claim := by
  unfold acceptsNarrow at accepted
  cases destFound : boundClause p clauses dest with
  | none => simp [destFound] at accepted
  | some destClause =>
    cases sourceFound : boundClause p clauses source with
    | none => simp [destFound, sourceFound] at accepted
    | some sourceClause =>
      have checked : checkNarrow p destClause sourceClause = true := by
        simpa only [destFound, sourceFound] using accepted
      rcases boundClause_registered p clauses dest destClause destFound with ⟨unique, present, key⟩
      rcases boundClause_registered p clauses source sourceClause sourceFound with ⟨_, sourcePresent, sourceKey⟩
      have meaning := checked_narrow_sound p destClause sourceClause checked
        (sourceTrue.2 sourceClause sourcePresent sourceKey)
      refine ⟨⟨destClause, present, key⟩, ?_⟩
      intro other otherPresent otherKey
      have equal := key_unique_of_nodup clauses (fun c => c.key) unique
        other destClause otherPresent present (otherKey.trans key.symm)
      exact equal ▸ meaning

theorem warrant_meaning_claim (p : Profile) (clauses : List (Clause p))
    (snapshot : Snapshot) (unique : (snapshot.warrants.map (·.id)).Nodup)
    (w : Warrant) (present : w ∈ snapshot.warrants)
    (meaning : WarrantMeaning p clauses snapshot w.id) : ClaimMeaning p clauses w.claim := by
  rcases meaning with ⟨other, otherPresent, sameId, meaning⟩
  have equal := key_unique_of_nodup snapshot.warrants (fun w => w.id)
    unique other w otherPresent present sameId
  exact equal ▸ meaning

theorem withNarrowing_validator_sound (p : Profile) (clauses : List (Clause p))
    (base : Admission) (snapshot : Snapshot)
    (unique : (snapshot.warrants.map (·.id)).Nodup)
    (baseSound : BaseValidatorSound p clauses base snapshot) :
    ValidatorSound (withNarrowing p clauses base) snapshot (WarrantMeaning p clauses snapshot) := by
  constructor
  · exact baseSound.receipt
  · exact baseSound.proof
  · exact baseSound.rule
  · intro dest destPresent source sourcePresent accepted sourceTrue
    refine ⟨dest, destPresent, rfl, ?_⟩
    exact acceptsNarrow_claim_meaning p clauses dest source accepted
      (warrant_meaning_claim p clauses snapshot unique source sourcePresent sourceTrue)

theorem evaluate_held_meaning (p : Profile) (clauses : List (Clause p))
    (base : Admission) (snapshot : Snapshot)
    (unique : (snapshot.warrants.map (·.id)).Nodup)
    (baseSound : BaseValidatorSound p clauses base snapshot)
    (claim : Nat)
    (heldClaim : held (evaluate (withNarrowing p clauses base) snapshot) claim = true) :
    ClaimMeaning p clauses claim :=
  evaluate_held_truth_composition (withNarrowing p clauses base) snapshot
    (WarrantMeaning p clauses snapshot) (ClaimMeaning p clauses)
    (withNarrowing_validator_sound p clauses base snapshot unique baseSound)
    (warrant_meaning_claim p clauses snapshot unique) claim heldClaim

theorem fold_held_meaning (p : Profile) (clauses : List (Clause p))
    (base : Admission) (events : List Event) (state : RuntimeState) (claim : Nat)
    (baseSound : BaseValidatorSound p clauses base state.snapshot)
    (folded : fold (withNarrowing p clauses base) events = .ok state)
    (heldClaim : held state claim = true) :
    (∃ clause ∈ clauses, clause.key = claim) ∧
    (∀ clause ∈ clauses, clause.key = claim → Means p clause.stmt clause.scope) := by
  unfold fold at folded
  cases resolved : resolve events with
  | error message => simp [resolved] at folded
  | ok snapshot =>
    rw [resolved] at folded
    have stateEq : evaluate (withNarrowing p clauses base) snapshot = state := Except.ok.inj folded
    subst state
    exact evaluate_held_meaning p clauses base snapshot
      (resolve_warrant_ids_nodup events snapshot resolved) baseSound claim heldClaim

#print axioms boundClause_registered
#print axioms acceptsNarrow_claim_meaning
#print axioms withNarrowing_validator_sound
#print axioms fold_held_meaning
end GP50.Semantic
