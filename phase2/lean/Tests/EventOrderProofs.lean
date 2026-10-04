import GP50.EventOrderProofs
open GP50 GP50.EventOrder
-- All event kinds, arbitrary admissions, and malformed logs remain covered.
example (adm : Admission) (a b : Event) (tail : List Event) :
    fold adm (a :: b :: tail) = fold adm (b :: a :: tail) :=
  fold_perm adm _ _ (List.Perm.swap b a tail)
example (adm : Admission) (event : Event) (tail : List Event) :
    fold adm (event :: event :: tail) = fold adm (event :: tail) :=
  fold_duplicate adm tail event
example (adm : Admission) (left right : List Event)
    (same : ∀ event, event ∈ left ↔ event ∈ right)
    (s : RuntimeState) (ok : fold adm left = .ok s) :
    fold adm right = .ok s := by
  rw [← fold_eq_of_mem_iff adm left right same]; exact ok
example (left right : List Event)
    (same : ∀ event, event ∈ left ↔ event ∈ right)
    (error : String) (bad : resolve left = .error error) :
    resolve right = .error error := by
  rw [← resolve_eq_of_mem_iff left right same]; exact bad
example (adm : Admission) (events : List Event) (id : Nat) :
    fold adm (.retract id :: .retract id :: events) =
    fold adm (.retract id :: events) := fold_duplicate adm events (.retract id)
example (adm : Admission) (events : List Event) (a b : Nat) :
    fold adm (.supersede a b :: .supersede a b :: events) =
    fold adm (.supersede a b :: events) := fold_duplicate adm events (.supersede a b)
example (a b : Current) (claim : Nat) : currentFor [a,b,a] claim = currentFor [b,a] claim :=
  currentFor_eq_of_mem_iff _ _ (by intro v; simp only [List.mem_cons, List.mem_nil_iff]; grind) claim
example (a b : Warrant) (id : Nat) : warrantFor [a,b,a] id = warrantFor [b,a] id :=
  warrantFor_eq_of_mem_iff _ _ (by intro v; simp only [List.mem_cons, List.mem_nil_iff]; grind) id
#check (inferInstance : LawfulBEq Nat)
#check LawfulBEq
#print axioms resolve_eq_of_mem_iff
#print axioms fold_eq_of_mem_iff
