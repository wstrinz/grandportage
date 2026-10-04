import GP50.AdmissionProofs
open GP50

-- Pure proof controls: no executable admission helper or new runtime code.
theorem refuseAll_validator_sound (snapshot : Snapshot) (Truth : Nat → Prop) :
    ValidatorSound Admission.refuseAll snapshot Truth := by
  constructor
  · intro w present data accepted
    simp [Admission.refuseAll] at accepted
  · intro w present declaration accepted
    simp [Admission.refuseAll] at accepted
  · intro w present premises side accepted
    simp [Admission.refuseAll] at accepted
  · intro w present source sourcePresent accepted
    simp [Admission.refuseAll] at accepted

-- The validator contracts are essential: an unconditional false receipt cannot
-- satisfy them for any warrant present in the snapshot.
example (snapshot : Snapshot) (w : Warrant) (present : w ∈ snapshot.warrants)
    (admission : Admission) (data : String) (accepted : admission.receipt w data = true) :
    ¬ ValidatorSound admission snapshot (fun _ => False) := by
  intro sound
  exact sound.receipt w present data accepted

example (snapshot : Snapshot) (id : Nat) :
    id ∉ (evaluate Admission.refuseAll snapshot).supports := by
  intro supported
  exact evaluate_supported_truth Admission.refuseAll snapshot (fun _ => False)
    (refuseAll_validator_sound snapshot (fun _ => False)) id supported

example (snapshot : Snapshot) (claim : Nat) :
    held (evaluate Admission.refuseAll snapshot) claim ≠ true := by
  intro heldClaim
  exact evaluate_held_truth_composition Admission.refuseAll snapshot
    (fun _ => False) (fun _ => False)
    (refuseAll_validator_sound snapshot (fun _ => False))
    (fun _ _ impossible => impossible) claim heldClaim

-- Concrete structural controls retain requested IDs and repeated dependencies.
example (binding : Binding) :
    let w : Warrant := {id := 7, claim := 1, version := 1, binding, evidence := .assertion}
    let snapshot : Snapshot := {domain := [], currents := [], warrants := [w], retracted := [], successors := []}
    lookupWarrant snapshot 7 = some w := by rfl

example (binding : Binding) :
    let w : Warrant := {id := 7, claim := 1, version := 1, binding, evidence := .assertion}
    let snapshot : Snapshot := {domain := [], currents := [], warrants := [w], retracted := [], successors := []}
    [7,7].mapM (lookupWarrant snapshot) = some [w,w] := by rfl

example (binding : Binding) :
    let w : Warrant := {id := 7, claim := 1, version := 1, binding, evidence := .assertion}
    let snapshot : Snapshot := {domain := [], currents := [], warrants := [w], retracted := [], successors := []}
    [7,8].mapM (lookupWarrant snapshot) = none := by rfl

example (snapshot : Snapshot) (premises : List Warrant)
    (mapped : [7,7].mapM (lookupWarrant snapshot) = some premises) :
    premises.map (·.id) = [7,7] :=
  lookup_mapM_ids snapshot [7,7] premises mapped

example (snapshot : Snapshot) (dependencies : List Nat) (premises : List Warrant)
    (Truth : Nat → Prop)
    (mapped : dependencies.mapM (lookupWarrant snapshot) = some premises)
    (supported : ∀ id ∈ dependencies, Truth id) :
    ∀ premise ∈ premises, Truth premise.id :=
  lookup_mapM_truth snapshot dependencies premises Truth mapped supported

#print axioms refuseAll_validator_sound
#print axioms GP50.evaluate_supported_truth
#print axioms GP50.evaluate_held_truth_composition

-- Rule contracts use the actual records recovered from the resolved snapshot.
example (snapshot : Snapshot) (dependencies : List Nat) (premises : List Warrant)
    (mapped : dependencies.mapM (lookupWarrant snapshot) = some premises) :
    ∀ premise ∈ premises, premise ∈ snapshot.warrants :=
  lookup_mapM_members snapshot dependencies premises mapped
