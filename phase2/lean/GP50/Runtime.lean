import GP50.Events
import GP50.Closure
namespace GP50
-- Capabilities come from registered validators, never a log's success Boolean.
-- A theorem-name string is inert unless a binder validates it through proof.
structure Admission where
  receipt : Warrant → String → Bool
  proof : Warrant → String → Bool
  rule : Warrant → List Warrant → String → Bool
  narrow : Warrant → Warrant → Bool

def Admission.refuseAll : Admission :=
  ⟨fun _ _ => false, fun _ _ => false, fun _ _ _ => false, fun _ _ => false⟩

def lookupWarrant (snapshot : Snapshot) (id : Nat) : Option Warrant :=
  snapshot.warrants.find? fun w => w.id == id

def requirements (admission : Admission) (snapshot : Snapshot)
    (warrant : Warrant) : Option (List Nat) :=
  if !live snapshot warrant then none else
  match warrant.evidence with
  | .receipt data => if admission.receipt warrant data then some [] else none
  | .theoremWarrant declaration =>
    if admission.proof warrant declaration then some [] else none
  | .derived dependencies side =>
    match dependencies.mapM (lookupWarrant snapshot) with
    | none => none
    | some premises =>
      if admission.rule warrant premises side then some dependencies else none
  | .narrow dependency =>
    match lookupWarrant snapshot dependency with
    | none => none
    | some premise =>
      if admission.narrow warrant premise then some [dependency] else none
  | .citation _ | .assertion | .attempt _ => none

def supportNodes (admission : Admission) (snapshot : Snapshot) : List SupportNode :=
  snapshot.warrants.map fun w => ⟨w.id, requirements admission snapshot w⟩

def projectClaims (snapshot : Snapshot) (supports : List Nat) : List Nat :=
  canonicalIds ((snapshot.warrants.filter fun w => supports.contains w.id).map (·.claim))

structure RuntimeState where
  snapshot : Snapshot
  supports : List Nat
  claims : List Nat
  deriving Repr, BEq, DecidableEq

def evaluate (admission : Admission) (snapshot : Snapshot) : RuntimeState :=
  let supports := closure (supportNodes admission snapshot)
  ⟨snapshot, supports, projectClaims snapshot supports⟩

def fold (admission : Admission) (events : List Event) : Except String RuntimeState := do
  return evaluate admission (← resolve events)

def held (state : RuntimeState) (claim : Nat) : Bool :=
  state.claims.contains claim
-- Conflict/release policy is a separate step; it must not filter this closure.
end GP50
