import GP50.AdmissionProofs
namespace GP50
-- Domain-independent facts about Except, canonical ids and log resolution.
-- Extracted from the Span stub (Phase 2.5) so kernel proofs never import a stub.

theorem eraseDups_length_le {α : Type} [BEq α] (values : List α) :
    values.eraseDups.length ≤ values.length := by
  cases values with
  | nil => simp
  | cons head tail =>
    rw [List.eraseDups_cons]
    have smaller := eraseDups_length_le (tail.filter fun value => !value == head)
    have bound := List.length_filter_le (fun value => !value == head) tail
    simp only [List.length_cons]
    omega
termination_by values.length
decreasing_by
  have bound := List.length_filter_le (fun value => !value == head) tail
  simp only [List.length_cons]
  omega

theorem nodup_of_eraseDups_length_eq {α : Type} [BEq α] [LawfulBEq α]
    (values : List α) (sameLength : values.eraseDups.length = values.length) :
    values.Nodup := by
  induction values with
  | nil => simp
  | cons head tail ih =>
    have dedupLength : (tail.filter fun value => !value == head).eraseDups.length = tail.length := by
      simpa only [List.eraseDups_cons, List.length_cons, Nat.add_right_cancel_iff] using sameLength
    have dedupBound := eraseDups_length_le (tail.filter fun value => !value == head)
    have filterBound := List.length_filter_le (fun value => !value == head) tail
    have filterLength : (tail.filter fun value => !value == head).length = tail.length := by omega
    have filterSame : (tail.filter fun value => !value == head) = tail :=
      List.filter_sublist.eq_of_length filterLength
    have absent : head ∉ tail := by
      intro present
      have rejected := (List.filter_eq_self.mp filterSame) head present
      simp at rejected
    have tailLength : tail.eraseDups.length = tail.length := by
      simpa only [filterSame] using dedupLength
    exact List.nodup_cons.mpr ⟨absent, ih tailLength⟩

theorem key_unique_of_nodup {α β : Type} (values : List α) (key : α → β)
    (distinct : (values.map key).Nodup) (left right : α)
    (leftPresent : left ∈ values) (rightPresent : right ∈ values)
    (sameKey : key left = key right) : left = right := by
  induction values generalizing left right with
  | nil => simp at leftPresent
  | cons head tail ih =>
    have parts : key head ∉ tail.map key ∧ (tail.map key).Nodup := by
      simpa only [List.map_cons, List.nodup_cons] using distinct
    simp only [List.mem_cons] at leftPresent rightPresent
    rcases leftPresent with rfl | leftTail
    · rcases rightPresent with rfl | rightTail
      · rfl
      · apply False.elim
        apply parts.1
        rw [sameKey]
        exact List.mem_map.mpr ⟨right, rightTail, rfl⟩
    · rcases rightPresent with rfl | rightTail
      · apply False.elim
        apply parts.1
        rw [← sameKey]
        exact List.mem_map.mpr ⟨left, leftTail, rfl⟩
      · exact ih parts.2 left right leftTail rightTail sameKey

@[simp] theorem except_bind_ok {α β : Type} (a : α) (f : α → Except String β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] theorem except_bind_error {α β : Type} (e : String) (f : α → Except String β) :
    (Except.error e >>= f) = Except.error e := rfl
@[simp] theorem except_map_ok {α β : Type} (a : α) (f : α → β) :
    (f <$> (Except.ok a : Except String α)) = Except.ok (f a) := rfl
@[simp] theorem except_map_error {α β : Type} (e : String) (f : α → β) :
    (f <$> (Except.error e : Except String α)) = Except.error e := rfl

theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] (values : List α) :
    values.eraseDups.Nodup := by
  cases valuesEq : values with
  | nil => simp
  | cons head tail =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    constructor
    · intro present
      have filtered := List.mem_filter.mp (List.mem_eraseDups.mp present)
      simp at filtered
    · exact eraseDups_nodup (tail.filter fun value => !value == head)
termination_by values.length
decreasing_by
  have bound := List.length_filter_le (fun value => !value == head) tail
  simp_all only [List.length_cons]
  omega

theorem canonicalIds_nodup (values : List Nat) : (canonicalIds values).Nodup :=
  (List.mergeSort_perm values.eraseDups (fun a b => a ≤ b)).symm.nodup
    (eraseDups_nodup values)

theorem eraseDups_mem_source {α : Type} [BEq α] (values : List α) (x : α)
    (member : x ∈ values.eraseDups) : x ∈ values := by
  cases valuesEq : values with
  | nil => simp [valuesEq] at member
  | cons head tail =>
    rw [valuesEq, List.eraseDups_cons] at member
    rcases List.mem_cons.mp member with equal | present
    · exact List.mem_cons.mpr (Or.inl equal)
    · exact List.mem_cons.mpr (Or.inr
        (List.mem_filter.mp (eraseDups_mem_source _ x present)).1)
termination_by values.length
decreasing_by
  have bound := List.length_filter_le (fun value => !value == head) tail
  simp_all only [List.length_cons]
  omega

theorem warrantFor_id (values : List Warrant) (id : Nat) (w : Warrant)
    (found : warrantFor values id = .ok w) : w.id = id := by
  unfold warrantFor at found
  split at found <;> try contradiction
  rename_i value restEq
  have eqValue : value = w := Except.ok.inj found
  subst w
  have member : value ∈ (values.filter fun w => w.id == id).eraseDups := by rw [restEq]; simp
  exact eq_of_beq (List.mem_filter.mp (eraseDups_mem_source _ _ member)).2

theorem warrantFor_mapM_ids (values : List Warrant) (ids : List Nat)
    (warrants : List Warrant)
    (mapped : ids.mapM (warrantFor values) = .ok warrants) :
    warrants.map (·.id) = ids := by
  induction ids generalizing warrants with
  | nil => change Except.ok [] = Except.ok warrants at mapped; cases mapped; rfl
  | cons id rest ih =>
    cases headLookup : warrantFor values id with
    | error message => simp [List.mapM_cons, headLookup] at mapped
    | ok head =>
      cases tailLookup : rest.mapM (warrantFor values) with
      | error message => simp [List.mapM_cons, headLookup, tailLookup] at mapped
      | ok tail =>
        have listEq : head :: tail = warrants := by
          simpa [List.mapM_cons, headLookup, tailLookup] using mapped
        subst warrants
        simp [warrantFor_id values id head headLookup, ih tail tailLookup]

theorem except_return_constant {α β : Type} (action : Except String α)
    (expected actual : β)
    (success : (action >>= fun _ => Except.ok expected) = Except.ok actual) :
    expected = actual := by
  cases action with
  | error e => contradiction
  | ok a => exact Except.ok.inj success

theorem resolve_warrant_ids (events : List Event) (snapshot : Snapshot)
    (resolved : resolve events = .ok snapshot) :
    snapshot.warrants.map (·.id) = canonicalIds ((warrantsIn events).map (·.id)) := by
  unfold resolve at resolved
  cases currentMap : (canonicalIds ((currentsIn events).map (·.claim))).mapM
      (currentFor (currentsIn events)) with
  | error message => simp only [currentMap, except_bind_error] at resolved; contradiction
  | ok currents =>
    simp only [currentMap, except_bind_ok] at resolved
    cases warrantMap : (canonicalIds ((warrantsIn events).map (·.id))).mapM
        (warrantFor (warrantsIn events)) with
    | error message => simp only [warrantMap, except_bind_error] at resolved; contradiction
    | ok warrants =>
      simp only [warrantMap, except_bind_ok] at resolved
      have snapshotEq := except_return_constant _ _ _ resolved
      have warrantsEq := congrArg Snapshot.warrants snapshotEq
      rw [← warrantsEq]
      exact warrantFor_mapM_ids _ _ _ warrantMap


theorem resolve_warrant_ids_nodup (events : List Event) (snapshot : Snapshot)
    (resolved : resolve events = .ok snapshot) :
    (snapshot.warrants.map (·.id)).Nodup := by
  rw [resolve_warrant_ids events snapshot resolved]
  exact canonicalIds_nodup _
end GP50
