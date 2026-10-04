import GP50.ResolveProofs
namespace GP50.EventOrder

private theorem binding_beq (a b : Binding) : instBEqBinding.beq a b = true ↔ a = b := by
  cases a; cases b
  simp [instBEqBinding.beq, Bool.and_eq_true, beq_iff_eq]

private theorem lawfulBinding : LawfulBEq Binding := {
  rfl := binding_beq _ _ |>.mpr rfl
  eq_of_beq := binding_beq _ _ |>.mp }
attribute [local instance] lawfulBinding

private theorem status_beq (a b : AttemptStatus) : instBEqAttemptStatus.beq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [instBEqAttemptStatus.beq, AttemptStatus.ctorIdx]
private theorem lawfulAttemptStatus : LawfulBEq AttemptStatus := {
  rfl := status_beq _ _ |>.mpr rfl
  eq_of_beq := status_beq _ _ |>.mp }
attribute [local instance] lawfulAttemptStatus

private theorem evidence_beq (a b : Evidence) : instBEqEvidence.beq a b = true ↔ a = b := by
  cases a <;> cases b <;>
    simp [instBEqEvidence.beq, beq_iff_eq]
private theorem lawfulEvidence : LawfulBEq Evidence := {
  rfl := evidence_beq _ _ |>.mpr rfl
  eq_of_beq := evidence_beq _ _ |>.mp }
attribute [local instance] lawfulEvidence

private theorem warrant_beq (a b : Warrant) : instBEqWarrant.beq a b = true ↔ a = b := by
  cases a; cases b
  simp [instBEqWarrant.beq, Bool.and_eq_true, beq_iff_eq]
private theorem lawfulWarrant : LawfulBEq Warrant := {
  rfl := warrant_beq _ _ |>.mpr rfl
  eq_of_beq := warrant_beq _ _ |>.mp }
attribute [local instance] lawfulWarrant

private theorem current_beq (a b : Current) : instBEqCurrent.beq a b = true ↔ a = b := by
  cases a; cases b
  simp [instBEqCurrent.beq, Bool.and_eq_true, beq_iff_eq]
private theorem lawfulCurrent : LawfulBEq Current := {
  rfl := current_beq _ _ |>.mpr rfl
  eq_of_beq := current_beq _ _ |>.mp }
attribute [local instance] lawfulCurrent

theorem sorted_nodup_eq_of_mem_iff {α : Type} (le : α → α → Bool)
    (anti : ∀ a b, le a b = true → le b a = true → a = b)
    (left right : List α) (leftSorted : left.Pairwise fun a b => le a b = true)
    (rightSorted : right.Pairwise fun a b => le a b = true)
    (leftUnique : left.Nodup) (rightUnique : right.Nodup)
    (same : ∀ a, a ∈ left ↔ a ∈ right) : left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons b bs => have impossible := (same b).mpr List.mem_cons_self; simp at impossible
  | cons a as ih =>
    cases right with
    | nil => have impossible := (same a).mp List.mem_cons_self; simp at impossible
    | cons b bs =>
      have ab : a = b := by
        have am := (same a).mp List.mem_cons_self
        have bm := (same b).mpr List.mem_cons_self
        rcases List.mem_cons.mp am with equal | am
        · exact equal
        rcases List.mem_cons.mp bm with equal | bm
        · exact equal.symm
        exact anti a b (List.rel_of_pairwise_cons leftSorted bm)
          (List.rel_of_pairwise_cons rightSorted am)
      subst b
      have tailSame : ∀ x, x ∈ as ↔ x ∈ bs := by
        intro x
        have ax := (List.nodup_cons.mp leftUnique).1
        have bx := (List.nodup_cons.mp rightUnique).1
        constructor
        · intro present
          rcases List.mem_cons.mp ((same x).mp (List.mem_cons_of_mem _ present)) with equal | found
          · subst x; exact (ax present).elim
          · exact found
        · intro present
          rcases List.mem_cons.mp ((same x).mpr (List.mem_cons_of_mem _ present)) with equal | found
          · subst x; exact (bx present).elim
          · exact found
      exact congrArg (List.cons a) (ih bs leftSorted.tail rightSorted.tail
        (List.nodup_cons.mp leftUnique).2 (List.nodup_cons.mp rightUnique).2 tailSame)

theorem canonicalIds_eq_of_mem_iff (left right : List Nat)
    (same : ∀ id, id ∈ left ↔ id ∈ right) : canonicalIds left = canonicalIds right := by
  apply sorted_nodup_eq_of_mem_iff (fun a b => a ≤ b)
  · intro a b ab ba
    exact Nat.le_antisymm (of_decide_eq_true ab) (of_decide_eq_true ba)
  · exact List.pairwise_mergeSort (by intros; simp_all; omega) (by intros; simp; omega) _
  · exact List.pairwise_mergeSort (by intros; simp_all; omega) (by intros; simp; omega) _
  · exact canonicalIds_nodup left
  · exact canonicalIds_nodup right
  · intro id
    simpa only [canonicalIds, List.mem_mergeSort, List.mem_eraseDups] using same id


private theorem singleton_of_set_eq {α : Type} (xs : List α) (a : α)
    (unique : xs.Nodup) (same : ∀ x, x ∈ xs ↔ x = a) : xs = [a] := by
  cases xs with
  | nil => have h := (same a).mpr rfl; simp at h
  | cons b bs =>
    have ba := (same b).mp List.mem_cons_self
    subst b
    have empty : bs = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x present
      have xa := (same x).mp (List.mem_cons_of_mem _ present)
      subst x
      exact (List.nodup_cons.mp unique).1 present
    rw [empty]

private theorem dedup_singleton_iff {α : Type} [BEq α] [LawfulBEq α]
    (xs : List α) (a : α) :
    xs.eraseDups = [a] ↔ ∀ x, x ∈ xs ↔ x = a := by
  constructor
  · intro h x
    rw [← List.mem_eraseDups, h]
    simp
  · intro h
    apply singleton_of_set_eq _ _ (eraseDups_nodup xs)
    intro x
    simpa only [List.mem_eraseDups] using h x

private theorem dedup_select_eq {α : Type} [BEq α] [LawfulBEq α]
    (left right : List α) (missing conflict : String)
    (same : ∀ x, x ∈ left ↔ x ∈ right) :
    (match left.eraseDups with
      | [x] => Except.ok x | [] => Except.error missing | _ => Except.error conflict) =
    (match right.eraseDups with
      | [x] => Except.ok x | [] => Except.error missing | _ => Except.error conflict) := by
  have singleton : ∀ x, left.eraseDups = [x] ↔ right.eraseDups = [x] := by
    intro x
    simp only [dedup_singleton_iff]
    constructor <;> intro h y
    · exact (same y).symm.trans (h y)
    · exact (same y).trans (h y)
  have empty : left.eraseDups = [] ↔ right.eraseDups = [] := by
    simp only [List.eq_nil_iff_forall_not_mem, List.mem_eraseDups]
    exact forall_congr' fun x => not_congr (same x)
  cases hl : left.eraseDups with
  | nil => rw [(empty.mp hl)]
  | cons a as =>
    cases as with
    | nil => rw [(singleton a).mp hl]
    | cons b bs =>
      cases hr : right.eraseDups with
      | nil => have h := empty.mpr hr; rw [hl] at h; simp at h
      | cons c cs =>
        cases cs with
        | nil => have h := (singleton c).mpr hr; rw [hl] at h; simp at h
        | cons d ds => rfl

private theorem max_fold_le (xs : List Current) (initial bound : Nat) :
    xs.foldl (fun n v => max n v.version) initial ≤ bound ↔
    initial ≤ bound ∧ ∀ v ∈ xs, v.version ≤ bound := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, Nat.max_le, List.mem_cons, forall_eq_or_imp, and_assoc]

private theorem max_fold_eq (left right : List Current)
    (same : ∀ v, v ∈ left ↔ v ∈ right) :
    left.foldl (fun n v => max n v.version) 0 =
    right.foldl (fun n v => max n v.version) 0 := by
  apply Nat.le_antisymm
  · apply (max_fold_le _ _ _).mpr
    have h := (max_fold_le right 0 _).mp (Nat.le_refl _)
    exact ⟨h.1, fun v hv => h.2 v ((same v).mp hv)⟩
  · apply (max_fold_le _ _ _).mpr
    have h := (max_fold_le left 0 _).mp (Nat.le_refl _)
    exact ⟨h.1, fun v hv => h.2 v ((same v).mpr hv)⟩


theorem currentFor_eq_of_mem_iff (left right : List Current)
    (same : ∀ v, v ∈ left ↔ v ∈ right) (claim : Nat) :
    currentFor left claim = currentFor right claim := by
  let lm := left.filter (fun v => v.claim == claim)
  let rm := right.filter (fun v => v.claim == claim)
  have matching : ∀ v, v ∈ lm ↔ v ∈ rm := by
    intro v; simp only [lm, rm, List.mem_filter]; rw [same v]
  have newest := max_fold_eq lm rm matching
  let lf := lm.filter (fun v => v.version == rm.foldl (fun n v => max n v.version) 0)
  let rf := rm.filter (fun v => v.version == rm.foldl (fun n v => max n v.version) 0)
  have sf : ∀ v, v ∈ lf ↔ v ∈ rf := by
    intro v; simp only [lf, rf, List.mem_filter]; rw [matching v]
  have h := dedup_select_eq lf rf s!"missing current binding: {claim}"
    s!"conflicting current bindings: {claim}" sf
  unfold currentFor
  dsimp only
  change (match (lm.filter (fun v => v.version == lm.foldl (fun n v => max n v.version) 0)).eraseDups with
    | [v] => pure v | [] => throw s!"missing current binding: {claim}"
    | _ => throw s!"conflicting current bindings: {claim}") = _
  rw [newest]
  change (match lf.eraseDups with
    | [v] => pure v | [] => throw s!"missing current binding: {claim}"
    | _ => throw s!"conflicting current bindings: {claim}") =
    (match rf.eraseDups with
    | [v] => pure v | [] => throw s!"missing current binding: {claim}"
    | _ => throw s!"conflicting current bindings: {claim}")
  cases hl : lf.eraseDups with
  | nil =>
    cases hr : rf.eraseDups with
    | nil => rfl
    | cons b bs => cases bs <;> simpa only [hl, hr, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] using h
  | cons a as =>
    cases as <;> cases hr : rf.eraseDups with
    | nil => simpa only [hl, hr, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] using h
    | cons b bs => cases bs <;> simpa only [hl, hr, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] using h

theorem warrantFor_eq_of_mem_iff (left right : List Warrant)
    (same : ∀ v, v ∈ left ↔ v ∈ right) (id : Nat) :
    warrantFor left id = warrantFor right id := by
  let lf := left.filter (fun w => w.id == id)
  let rf := right.filter (fun w => w.id == id)
  have sf : ∀ v, v ∈ lf ↔ v ∈ rf := by
    intro v; simp only [lf, rf, List.mem_filter]; rw [same v]
  have h := dedup_select_eq lf rf s!"missing warrant: {id}"
    s!"conflicting warrant contents: {id}" sf
  unfold warrantFor
  change (match lf.eraseDups with
    | [v] => Except.ok v | [] => Except.error s!"missing warrant: {id}"
    | _ => Except.error s!"conflicting warrant contents: {id}") =
    (match rf.eraseDups with
    | [v] => Except.ok v | [] => Except.error s!"missing warrant: {id}"
    | _ => Except.error s!"conflicting warrant contents: {id}")
  cases hl : lf.eraseDups with
  | nil =>
    cases hr : rf.eraseDups with
    | nil => rfl
    | cons b bs => cases bs <;> simpa only [hl, hr, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] using h
  | cons a as =>
    cases as <;> cases hr : rf.eraseDups with
    | nil => simpa only [hl, hr, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] using h
    | cons b bs => cases bs <;> simpa only [hl, hr, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] using h

private theorem map_set_eq {α β : Type} (f : α → β) (left right : List α)
    (same : ∀ x, x ∈ left ↔ x ∈ right) : ∀ y, y ∈ left.map f ↔ y ∈ right.map f := by
  intro y
  simp only [List.mem_map]
  constructor <;> rintro ⟨x, hx, hxy⟩
  · exact ⟨x, (same x).mp hx, hxy⟩
  · exact ⟨x, (same x).mpr hx, hxy⟩

private theorem filterMap_set_eq {α β : Type} (f : α → Option β) (left right : List α)
    (same : ∀ x, x ∈ left ↔ x ∈ right) : ∀ y, y ∈ left.filterMap f ↔ y ∈ right.filterMap f := by
  intro y
  simp only [List.mem_filterMap]
  constructor <;> rintro ⟨x, hx, hxy⟩
  · exact ⟨x, (same x).mp hx, hxy⟩
  · exact ⟨x, (same x).mpr hx, hxy⟩

private theorem canonicalLinks_eq (left right : List (Nat × Nat))
    (same : ∀ edge, edge ∈ left ↔ edge ∈ right) :
    left.eraseDups.mergeSort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)) =
    right.eraseDups.mergeSort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)) := by
  apply sorted_nodup_eq_of_mem_iff (fun (a b : Nat × Nat) => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2))
  · intro a b ab ba
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ab ba
    apply Prod.ext <;> omega
  · apply List.pairwise_mergeSort
    · intro a b c ab bc
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at *
      omega
    · intro a b
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      omega
  · apply List.pairwise_mergeSort
    · intro a b c ab bc
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at *
      omega
    · intro a b
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      omega
  · exact (List.mergeSort_perm _ _).symm.nodup (eraseDups_nodup left)
  · exact (List.mergeSort_perm _ _).symm.nodup (eraseDups_nodup right)
  · intro edge
    simpa only [List.mem_mergeSort, List.mem_eraseDups] using same edge

-- Equality of event membership permits arbitrary permutation and repeated events.
-- The equality includes deterministic diagnostics, not only successful snapshots.
theorem resolve_eq_of_mem_iff (left right : List Event)
    (same : ∀ event, event ∈ left ↔ event ∈ right) :
    resolve left = resolve right := by
  have cs : ∀ c, c ∈ currentsIn left ↔ c ∈ currentsIn right :=
    filterMap_set_eq _ left right same
  have ws : ∀ w, w ∈ warrantsIn left ↔ w ∈ warrantsIn right :=
    filterMap_set_eq _ left right same
  have ci := canonicalIds_eq_of_mem_iff _ _ (map_set_eq Current.claim _ _ cs)
  have wi := canonicalIds_eq_of_mem_iff _ _ (map_set_eq Warrant.id _ _ ws)
  have cf : currentFor (currentsIn left) = currentFor (currentsIn right) :=
    funext (currentFor_eq_of_mem_iff _ _ cs)
  have wf : warrantFor (warrantsIn left) = warrantFor (warrantsIn right) :=
    funext (warrantFor_eq_of_mem_iff _ _ ws)
  have retracted := canonicalIds_eq_of_mem_iff _ _
    (filterMap_set_eq (fun e => GP50.resolve.match_1 (fun _ => Option Nat) e (fun target => some target) (fun _ => none)) left right same)
  have links := canonicalLinks_eq _ _
    (filterMap_set_eq (fun e => GP50.resolve.match_3 (fun _ => Option (Nat × Nat)) e (fun a b => some (a,b)) (fun _ => none)) left right same)
  have declared := filterMap_set_eq
    (fun e => GP50.resolve.match_7 (fun _ => Option Nat) e (fun key => some key) (fun _ => none)) left right same
  have domain := canonicalIds_eq_of_mem_iff
    ((left.filterMap fun e => GP50.resolve.match_7 (fun _ => Option Nat) e (fun key => some key) (fun _ => none)) ++
      canonicalIds ((currentsIn right).map Current.claim))
    ((right.filterMap fun e => GP50.resolve.match_7 (fun _ => Option Nat) e (fun key => some key) (fun _ => none)) ++
      canonicalIds ((currentsIn right).map Current.claim))
    (by intro id; simp only [List.mem_append]; rw [declared id])
  unfold resolve
  dsimp only
  simp only [ci, wi, cf, wf]
  congr 1
  funext currents
  congr 1
  funext warrants
  rw [retracted, links, domain]

theorem fold_eq_of_mem_iff (admission : Admission) (left right : List Event)
    (same : ∀ event, event ∈ left ↔ event ∈ right) :
    fold admission left = fold admission right := by
  unfold fold
  rw [resolve_eq_of_mem_iff left right same]

theorem resolve_perm (left right : List Event) (perm : left.Perm right) :
    resolve left = resolve right :=
  resolve_eq_of_mem_iff left right (fun _ => perm.mem_iff)

theorem fold_perm (admission : Admission) (left right : List Event)
    (perm : left.Perm right) : fold admission left = fold admission right :=
  fold_eq_of_mem_iff admission left right (fun _ => perm.mem_iff)

theorem resolve_duplicate (events : List Event) (event : Event) :
    resolve (event :: event :: events) = resolve (event :: events) :=
  resolve_eq_of_mem_iff _ _ (by intro e; simp only [List.mem_cons]; grind)

theorem fold_duplicate (admission : Admission) (events : List Event) (event : Event) :
    fold admission (event :: event :: events) = fold admission (event :: events) :=
  fold_eq_of_mem_iff admission _ _ (by intro e; simp only [List.mem_cons]; grind)

#print axioms resolve_eq_of_mem_iff
#print axioms fold_eq_of_mem_iff
#print axioms resolve_perm
#print axioms fold_duplicate
end GP50.EventOrder
