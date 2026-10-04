import GP50.BoundReplayProofs
import GP50.AdmissionProofs
import GP50.ResolveProofs
namespace GP50.Span
open PolyStub

-- Meaning concerns decoded polynomial coefficients. Host byte/digest fidelity
-- remains a separate adapter trust boundary.
def ClaimMeaning (clauses : List Clause) (claim : Nat) : Prop :=
  (∃ clause ∈ clauses, clause.key = claim) ∧
  ∀ clause ∈ clauses, clause.key = claim → FormalSpan clause

def WarrantMeaning (snapshot : Snapshot) (clauses : List Clause) (id : Nat) : Prop :=
  ∃ w ∈ snapshot.warrants, w.id = id ∧ ClaimMeaning clauses w.claim

theorem admission_validator_sound (clauses : List Clause) (receipts : List Receipt)
    (snapshot : Snapshot) :
    ValidatorSound (admission clauses receipts) snapshot (WarrantMeaning snapshot clauses) := by
  constructor
  · intro w member name accepted
    refine ⟨w, member, rfl, ?_⟩
    constructor
    · rcases (accepts_exact_identity clauses receipts w name accepted).2 with
        ⟨clause, present, key, _⟩
      exact ⟨clause, present, key⟩
    · exact accepts_unique_clause_meaning clauses receipts w name accepted
  · intro w member name accepted
    contradiction
  · intro w member premises side accepted supported
    contradiction
  · intro w member source sourceMember accepted supported
    contradiction

theorem evaluate_held_formalSpan (clauses : List Clause) (receipts : List Receipt)
    (snapshot : Snapshot) (uniqueIds : (snapshot.warrants.map (·.id)).Nodup)
    (claim : Nat) (heldClaim : held (evaluate (admission clauses receipts) snapshot) claim = true) :
    ClaimMeaning clauses claim := by
  apply evaluate_held_truth_composition (admission clauses receipts) snapshot
    (WarrantMeaning snapshot clauses) (ClaimMeaning clauses)
    (admission_validator_sound clauses receipts snapshot) _ claim heldClaim
  intro w present meaning
  rcases meaning with ⟨other, otherPresent, sameId, meaning⟩
  have equal : other = w :=
    key_unique_of_nodup snapshot.warrants (fun w => w.id) uniqueIds
      other w otherPresent present sameId
  exact equal ▸ meaning

theorem resolve_held_formalSpan (clauses : List Clause) (receipts : List Receipt)
    (events : List Event) (snapshot : Snapshot) (claim : Nat)
    (resolved : resolve events = .ok snapshot)
    (heldClaim : held (evaluate (admission clauses receipts) snapshot) claim = true) :
    (∃ clause ∈ clauses, clause.key = claim) ∧
    (∀ clause ∈ clauses, clause.key = claim → FormalSpan clause) :=
  evaluate_held_formalSpan clauses receipts snapshot
    (resolve_warrant_ids_nodup events snapshot resolved) claim heldClaim

theorem fold_held_formalSpan (clauses : List Clause) (receipts : List Receipt)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission clauses receipts) events = .ok state)
    (heldClaim : held state claim = true) :
    (∃ clause ∈ clauses, clause.key = claim) ∧
    (∀ clause ∈ clauses, clause.key = claim → FormalSpan clause) := by
  unfold fold at folded
  cases resolved : resolve events with
  | error message => simp [resolved] at folded
  | ok snapshot =>
    rw [resolved] at folded
    have stateEq : evaluate (admission clauses receipts) snapshot = state := by
      exact Except.ok.inj folded
    subst state
    exact resolve_held_formalSpan clauses receipts events snapshot claim resolved heldClaim

#print axioms resolve_warrant_ids_nodup
#print axioms admission_validator_sound
#print axioms evaluate_held_formalSpan
#print axioms resolve_held_formalSpan
#print axioms fold_held_formalSpan

end GP50.Span
