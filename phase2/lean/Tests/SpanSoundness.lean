import GP50.SpanSoundnessProofs
namespace GP50.Span.Tests
open GP50.Span

-- The public result needs only concrete fold success and the held bit.
example (clauses : List Clause) (receipts : List Receipt)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (success : fold (admission clauses receipts) events = .ok state)
    (heldClaim : held state claim = true) :
    (∃ c ∈ clauses, c.key = claim) ∧
    (∀ c ∈ clauses, c.key = claim → FormalSpan c) :=
  fold_held_formalSpan clauses receipts events state claim success heldClaim

example (clauses : List Clause) (receipts : List Receipt)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (success : fold (admission clauses receipts) events = .ok state)
    (heldClaim : held state claim = true) :
    ∃ c ∈ clauses, c.key = claim :=
  (fold_held_formalSpan clauses receipts events state claim success heldClaim).1

example (clauses : List Clause) (receipts : List Receipt)
    (events : List Event) (state : RuntimeState) (claim : Nat) (c : Clause)
    (success : fold (admission clauses receipts) events = .ok state)
    (heldClaim : held state claim = true) (registered : c ∈ clauses) (key : c.key = claim) :
    FormalSpan c :=
  (fold_held_formalSpan clauses receipts events state claim success heldClaim).2 c registered key

example (events : List Event) (snapshot : Snapshot)
    (success : resolve events = .ok snapshot) :
    (snapshot.warrants.map (·.id)).Nodup :=
  resolve_warrant_ids_nodup events snapshot success

-- Conflicting duplicate IDs cannot project one warrant's receipt to another claim.
example (events : List Event) (snapshot : Snapshot) (left right : Warrant)
    (success : resolve events = .ok snapshot)
    (hl : left ∈ snapshot.warrants) (hr : right ∈ snapshot.warrants)
    (sameId : left.id = right.id) : left.claim = right.claim := by
  have equal := key_unique_of_nodup snapshot.warrants (fun w => w.id)
    (resolve_warrant_ids_nodup events snapshot success) left right hl hr sameId
  exact congrArg Warrant.claim equal

-- Registry well-formedness never enables any of these capabilities.
example (cs : List Clause) (rs : List Receipt) (w : Warrant) (name : String)
    (_valid : wellFormed cs rs = true) :
    (admission cs rs).proof w name = false := rfl
example (cs : List Clause) (rs : List Receipt) (w : Warrant)
    (premises : List Warrant) (side : String) (_valid : wellFormed cs rs = true) :
    (admission cs rs).rule w premises side = false := rfl
example (cs : List Clause) (rs : List Receipt) (w source : Warrant)
    (_valid : wellFormed cs rs = true) :
    (admission cs rs).narrow w source = false := rfl

example (cs : List Clause) (rs : List Receipt) (w : Warrant) (name : String)
    (invalid : wellFormed cs rs = false) : accepts cs rs w name = false := by
  simp [accepts, invalid]

-- Empty registries cannot yield a held claim after successful folding.
example (receipts : List Receipt) (events : List Event) (state : RuntimeState) (claim : Nat)
    (success : fold (admission [] receipts) events = .ok state) :
    held state claim = false := by
  cases heldBit : held state claim with
  | false => rfl
  | true =>
    rcases (fold_held_formalSpan [] receipts events state claim success heldBit).1 with
      ⟨c, present, _⟩
    simp at present

example (snapshot : Snapshot) (claim : Nat) :
    held (evaluate Admission.refuseAll snapshot) claim = false := by
  have sound : ValidatorSound Admission.refuseAll snapshot (fun _ => False) := by
    constructor <;> intros <;> contradiction
  cases bit : held (evaluate Admission.refuseAll snapshot) claim with
  | false => rfl
  | true =>
    have impossible := evaluate_held_truth_composition Admission.refuseAll snapshot
      (fun _ => False) (fun _ => False) sound (by intros; assumption) claim bit
    exact impossible.elim

-- A resolved snapshot cannot contain distinct claims under one warrant ID.
example (events : List Event) (snapshot : Snapshot) (left right : Warrant)
    (success : resolve events = .ok snapshot)
    (hl : left ∈ snapshot.warrants) (hr : right ∈ snapshot.warrants)
    (different : left.claim ≠ right.claim) : left.id ≠ right.id := by
  intro sameId
  have equal := key_unique_of_nodup snapshot.warrants (fun w => w.id)
    (resolve_warrant_ids_nodup events snapshot success) left right hl hr sameId
  exact different (congrArg Warrant.claim equal)

end GP50.Span.Tests
