import GP50.NarrowingAdmissionProofs
namespace GP50.Semantic.NarrowingAdmissionControls

example (p : Profile) (clauses : List (Clause p)) (base : Admission)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (contracts : BaseValidatorSound p clauses base state.snapshot)
    (success : fold (withNarrowing p clauses base) events = .ok state)
    (heldClaim : held state claim = true) :
    (∃ c ∈ clauses, c.key = claim) ∧
    (∀ c ∈ clauses, c.key = claim → Means p c.stmt c.scope) :=
  fold_held_meaning p clauses base events state claim contracts success heldClaim

example (p : Profile) (clauses : List (Clause p)) (base : Admission)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (contracts : BaseValidatorSound p clauses base state.snapshot)
    (success : fold (withNarrowing p clauses base) events = .ok state)
    (heldClaim : held state claim = true) : ∃ c ∈ clauses, c.key = claim :=
  (fold_held_meaning p clauses base events state claim contracts success heldClaim).1

example (p : Profile) (clauses : List (Clause p)) (base : Admission)
    (events : List Event) (state : RuntimeState) (claim : Nat) (c : Clause p)
    (contracts : BaseValidatorSound p clauses base state.snapshot)
    (success : fold (withNarrowing p clauses base) events = .ok state)
    (heldClaim : held state claim = true) (registered : c ∈ clauses) (key : c.key = claim) :
    Means p c.stmt c.scope :=
  (fold_held_meaning p clauses base events state claim contracts success heldClaim).2 c registered key

example (p : Profile) (clauses : List (Clause p)) (dest source : Warrant)
    (accepted : acceptsNarrow p clauses dest source = true)
    (sourceTrue : ClaimMeaning p clauses source.claim) :
    ClaimMeaning p clauses dest.claim :=
  acceptsNarrow_claim_meaning p clauses dest source accepted sourceTrue

example (p : Profile) (clauses : List (Clause p)) (w : Warrant) (c : Clause p)
    (found : boundClause p clauses w = some c) :
    (clauses.map (·.key)).Nodup ∧ c ∈ clauses ∧ c.key = w.claim :=
  boundClause_registered p clauses w c found

example (p : Profile) (clauses : List (Clause p)) (w : Warrant) (c left right : Clause p)
    (found : boundClause p clauses w = some c)
    (leftPresent : left ∈ clauses) (rightPresent : right ∈ clauses)
    (sameKey : left.key = right.key) : left = right :=
  key_unique_of_nodup clauses (fun c => c.key)
    (boundClause_registered p clauses w c found).1 left right leftPresent rightPresent sameKey

-- Distinct registered clauses sharing a key cannot get an arrival-order winner.
example (p : Profile) (clauses : List (Clause p)) (w : Warrant) (left right : Clause p)
    (leftPresent : left ∈ clauses) (rightPresent : right ∈ clauses)
    (sameKey : left.key = right.key) (different : left ≠ right) :
    boundClause p clauses w = none := by
  cases found : boundClause p clauses w with
  | none => rfl
  | some c =>
    exact (different (key_unique_of_nodup clauses (fun c => c.key)
      (boundClause_registered p clauses w c found).1 left right leftPresent rightPresent sameKey)).elim

example (p : Profile) (c : Clause p) (w : Warrant) :
    boundClause p [c,c] w = none := by
  simp [boundClause, List.eraseDups_cons]

example (p : Profile) (c : Clause p) (dest source : Warrant) :
    acceptsNarrow p [c,c] dest source = false := by
  simp [acceptsNarrow, boundClause, List.eraseDups_cons]

example (p : Profile) (clauses : List (Clause p)) (dest source : Warrant)
    (absent : boundClause p clauses source = none) :
    acceptsNarrow p clauses dest source = false := by
  simp [acceptsNarrow, absent]

example (p : Profile) (clauses : List (Clause p)) (dest source : Warrant)
    (absent : boundClause p clauses dest = none) :
    acceptsNarrow p clauses dest source = false := by
  simp [acceptsNarrow, absent]

-- No contract on the overridden base.narrow field is needed.
example (p : Profile) (clauses : List (Clause p)) (base : Admission) (dest source : Warrant) :
    (withNarrowing p clauses base).narrow dest source = acceptsNarrow p clauses dest source := rfl

example (p : Profile) (clauses : List (Clause p)) (snapshot : Snapshot) :
    BaseValidatorSound p clauses Admission.refuseAll snapshot := by
  constructor <;> intros <;> contradiction

example (p : Profile) (clauses : List (Clause p)) (base : Admission)
    (snapshot : Snapshot) (unique : (snapshot.warrants.map (·.id)).Nodup)
    (contracts : BaseValidatorSound p clauses base snapshot) :
    ValidatorSound (withNarrowing p clauses base) snapshot (WarrantMeaning p clauses snapshot) :=
  withNarrowing_validator_sound p clauses base snapshot unique contracts

-- Checked narrowing cannot bootstrap any graph when all root/rule validators refuse.
example (p : Profile) (clauses : List (Clause p)) (snapshot : Snapshot) (claim : Nat) :
    held (evaluate (withNarrowing p clauses Admission.refuseAll) snapshot) claim = false := by
  have sound : ValidatorSound (withNarrowing p clauses Admission.refuseAll) snapshot
      (fun _ => False) := by
    constructor
    · intros; contradiction
    · intros; contradiction
    · intros; contradiction
    · intros; contradiction
  cases bit : held (evaluate (withNarrowing p clauses Admission.refuseAll) snapshot) claim with
  | false => rfl
  | true =>
    have impossible := evaluate_held_truth_composition
      (withNarrowing p clauses Admission.refuseAll) snapshot
      (fun _ => False) (fun _ => False) sound (by intros; assumption) claim bit
    exact impossible.elim

example (p : Profile) (base : Admission) (events : List Event)
    (state : RuntimeState) (claim : Nat)
    (contracts : BaseValidatorSound p [] base state.snapshot)
    (success : fold (withNarrowing p [] base) events = .ok state) :
    held state claim = false := by
  cases bit : held state claim with
  | false => rfl
  | true =>
    rcases (fold_held_meaning p [] base events state claim contracts success bit).1 with
      ⟨c, present, _⟩
    simp at present

-- Runtime narrowing depends on the exact source warrant ID, not source claim key.
example (p : Profile) (clauses : List (Clause p)) (base : Admission)
    (snapshot : Snapshot) (dest source : Warrant) (id : Nat)
    (eligible : live snapshot dest = true) (evidence : dest.evidence = .narrow id)
    (found : lookupWarrant snapshot id = some source)
    (accepted : acceptsNarrow p clauses dest source = true) :
    requirements (withNarrowing p clauses base) snapshot dest = some [id] := by
  simp [requirements, eligible, evidence, found, withNarrowing, accepted]

example (p : Profile) (clauses : List (Clause p)) (base : Admission)
    (snapshot : Snapshot) (dest : Warrant) (id : Nat)
    (eligible : live snapshot dest = true) (evidence : dest.evidence = .narrow id)
    (absent : lookupWarrant snapshot id = none) :
    requirements (withNarrowing p clauses base) snapshot dest = none := by
  simp [requirements, eligible, evidence, absent]

example (p : Profile) (clauses : List (Clause p)) (snapshot : Snapshot)
    (events : List Event) (w : Warrant) (present : w ∈ snapshot.warrants)
    (resolved : resolve events = .ok snapshot)
    (meaning : WarrantMeaning p clauses snapshot w.id) : ClaimMeaning p clauses w.claim :=
  warrant_meaning_claim p clauses snapshot
    (resolve_warrant_ids_nodup events snapshot resolved) w present meaning

end GP50.Semantic.NarrowingAdmissionControls
