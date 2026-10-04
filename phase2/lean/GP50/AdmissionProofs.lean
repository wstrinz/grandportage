import GP50.Runtime
import GP50.ClosureProofs
namespace GP50

-- Erased validator contracts about warrant truth, not blanket node soundness.
-- Concrete admission/binding correctness and claim projection remain separate.
structure ValidatorSound (admission : Admission) (snapshot : Snapshot)
    (Truth : Nat → Prop) : Prop where
  receipt : ∀ w ∈ snapshot.warrants, ∀ data,
    admission.receipt w data = true → Truth w.id
  proof : ∀ w ∈ snapshot.warrants, ∀ declaration,
    admission.proof w declaration = true → Truth w.id
  rule : ∀ w ∈ snapshot.warrants, ∀ premises side,
    admission.rule w premises side = true →
      (∀ premise ∈ premises, premise ∈ snapshot.warrants) →
      (∀ premise ∈ premises, Truth premise.id) → Truth w.id
  narrow : ∀ w ∈ snapshot.warrants, ∀ source ∈ snapshot.warrants,
    admission.narrow w source = true → Truth source.id → Truth w.id

theorem lookupWarrant_id (snapshot : Snapshot) (id : Nat) (w : Warrant)
    (found : lookupWarrant snapshot id = some w) : w.id = id := by
  have matchedId : (w.id == id) = true :=
    List.find?_some (p := fun candidate : Warrant => candidate.id == id) found
  exact eq_of_beq matchedId

theorem lookupWarrant_member (snapshot : Snapshot) (id : Nat) (w : Warrant)
    (found : lookupWarrant snapshot id = some w) : w ∈ snapshot.warrants :=
  List.mem_of_find?_eq_some found

theorem lookup_mapM_ids (snapshot : Snapshot) (dependencies : List Nat)
    (premises : List Warrant)
    (mapped : dependencies.mapM (lookupWarrant snapshot) = some premises) :
    premises.map (·.id) = dependencies := by
  induction dependencies generalizing premises with
  | nil =>
    simp at mapped
    subst premises
    rfl
  | cons id rest ih =>
    cases headLookup : lookupWarrant snapshot id with
    | none => simp [List.mapM_cons, headLookup] at mapped
    | some head =>
      cases tailLookup : rest.mapM (lookupWarrant snapshot) with
      | none => simp [List.mapM_cons, headLookup, tailLookup] at mapped
      | some tail =>
        have listEq : head :: tail = premises := by
          simpa [List.mapM_cons, headLookup, tailLookup] using mapped
        subst premises
        simp [lookupWarrant_id snapshot id head headLookup, ih tail tailLookup]

theorem lookup_mapM_truth (snapshot : Snapshot) (dependencies : List Nat)
    (premises : List Warrant) (Truth : Nat → Prop)
    (mapped : dependencies.mapM (lookupWarrant snapshot) = some premises)
    (supported : ∀ id ∈ dependencies, Truth id) :
    ∀ premise ∈ premises, Truth premise.id := by
  intro premise present
  apply supported premise.id
  rw [← lookup_mapM_ids snapshot dependencies premises mapped]
  exact List.mem_map.mpr ⟨premise, present, rfl⟩

theorem lookup_mapM_members (snapshot : Snapshot) (dependencies : List Nat)
    (premises : List Warrant)
    (mapped : dependencies.mapM (lookupWarrant snapshot) = some premises) :
    ∀ premise ∈ premises, premise ∈ snapshot.warrants := by
  induction dependencies generalizing premises with
  | nil =>
    simp at mapped
    subst premises
    simp
  | cons id rest ih =>
    cases headLookup : lookupWarrant snapshot id with
    | none => simp [List.mapM_cons, headLookup] at mapped
    | some head =>
      cases tailLookup : rest.mapM (lookupWarrant snapshot) with
      | none => simp [List.mapM_cons, headLookup, tailLookup] at mapped
      | some tail =>
        have listEq : head :: tail = premises := by
          simpa [List.mapM_cons, headLookup, tailLookup] using mapped
        subst premises
        intro premise present
        rcases List.mem_cons.mp present with equal | present
        · subst premise
          exact lookupWarrant_member snapshot id head headLookup
        · exact ih tail tailLookup premise present

theorem requirements_truth (admission : Admission) (snapshot : Snapshot)
    (Truth : Nat → Prop) (sound : ValidatorSound admission snapshot Truth)
    (w : Warrant) (present : w ∈ snapshot.warrants) (dependencies : List Nat)
    (admitted : requirements admission snapshot w = some dependencies)
    (supported : ∀ id ∈ dependencies, Truth id) : Truth w.id := by
  cases liveValue : live snapshot w with
  | false => simp [requirements, liveValue] at admitted
  | true =>
    cases evidence : w.evidence with
    | receipt data =>
      cases accepted : admission.receipt w data with
      | false => simp [requirements, liveValue, evidence, accepted] at admitted
      | true => exact sound.receipt w present data accepted
    | theoremWarrant declaration =>
      cases accepted : admission.proof w declaration with
      | false => simp [requirements, liveValue, evidence, accepted] at admitted
      | true => exact sound.proof w present declaration accepted
    | derived declared side =>
      cases mapped : declared.mapM (lookupWarrant snapshot) with
      | none => simp [requirements, liveValue, evidence, mapped] at admitted
      | some premises =>
        cases accepted : admission.rule w premises side with
        | false => simp [requirements, liveValue, evidence, mapped, accepted] at admitted
        | true =>
          have dependenciesEq : declared = dependencies := by
            simpa [requirements, liveValue, evidence, mapped, accepted] using admitted
          apply sound.rule w present premises side accepted
            (lookup_mapM_members snapshot declared premises mapped)
          apply lookup_mapM_truth snapshot declared premises Truth mapped
          intro id member
          exact supported id (dependenciesEq ▸ member)
    | narrow dependency =>
      cases found : lookupWarrant snapshot dependency with
      | none => simp [requirements, liveValue, evidence, found] at admitted
      | some source =>
        cases accepted : admission.narrow w source with
        | false => simp [requirements, liveValue, evidence, found, accepted] at admitted
        | true =>
          have dependenciesEq : [dependency] = dependencies := by
            simpa [requirements, liveValue, evidence, found, accepted] using admitted
          apply sound.narrow w present source (lookupWarrant_member snapshot dependency source found) accepted
          apply supported source.id
          rw [lookupWarrant_id snapshot dependency source found, ← dependenciesEq]
          simp
    | citation text => simp [requirements, liveValue, evidence] at admitted
    | assertion => simp [requirements, liveValue, evidence] at admitted
    | attempt status => simp [requirements, liveValue, evidence] at admitted

theorem supportNodes_local_truth (admission : Admission) (snapshot : Snapshot)
    (Truth : Nat → Prop) (sound : ValidatorSound admission snapshot Truth) :
    ∀ node ∈ supportNodes admission snapshot, ∀ dependencies,
      node.premises = some dependencies →
        (∀ id ∈ dependencies, Truth id) → Truth node.id := by
  intro node present dependencies admitted supported
  simp only [supportNodes, List.mem_map] at present
  rcases present with ⟨w, present, rfl⟩
  exact requirements_truth admission snapshot Truth sound w present dependencies admitted supported

theorem evaluate_supported_truth (admission : Admission) (snapshot : Snapshot)
    (Truth : Nat → Prop) (sound : ValidatorSound admission snapshot Truth) :
    ∀ id ∈ (evaluate admission snapshot).supports, Truth id :=
  closure_sound (supportNodes admission snapshot) Truth
    (supportNodes_local_truth admission snapshot Truth sound)

-- Separate composition step: warrant truth must be projected soundly to claims.
-- This is not a concrete statement/profile or full heldSoundStatement theorem.
theorem projectClaims_truth (snapshot : Snapshot) (supports : List Nat)
    (Truth ClaimMeaning : Nat → Prop)
    (supported : ∀ id ∈ supports, Truth id)
    (projection : ∀ w ∈ snapshot.warrants, Truth w.id → ClaimMeaning w.claim) :
    ∀ claim ∈ projectClaims snapshot supports, ClaimMeaning claim := by
  intro claim member
  simp only [projectClaims, canonicalIds, List.mem_mergeSort, List.mem_eraseDups,
    List.mem_map, List.mem_filter, List.contains_iff_mem] at member
  rcases member with ⟨w, ⟨present, member⟩, rfl⟩
  exact projection w present (supported w.id member)

theorem evaluate_held_truth_composition (admission : Admission) (snapshot : Snapshot)
    (Truth ClaimMeaning : Nat → Prop)
    (sound : ValidatorSound admission snapshot Truth)
    (projection : ∀ w ∈ snapshot.warrants, Truth w.id → ClaimMeaning w.claim)
    (claim : Nat) (heldClaim : held (evaluate admission snapshot) claim = true) :
    ClaimMeaning claim := by
  apply projectClaims_truth snapshot (evaluate admission snapshot).supports Truth ClaimMeaning
    (evaluate_supported_truth admission snapshot Truth sound) projection claim
  exact List.contains_iff_mem.mp heldClaim

#print axioms lookupWarrant_id
#print axioms lookup_mapM_ids
#print axioms requirements_truth
#print axioms supportNodes_local_truth
#print axioms evaluate_supported_truth
#print axioms evaluate_held_truth_composition
end GP50
