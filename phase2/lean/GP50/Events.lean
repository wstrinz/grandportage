import Std
namespace GP50
structure Binding where
  statementHash : String
  scopeHash : String
  modelHash : String
  inputHashes : List String
  authority : String
  authorityVersion : Nat
  kernelVersion : Nat
  deriving Repr, BEq, DecidableEq
inductive AttemptStatus where
  | absent | failed | timeout
  deriving Repr, BEq, DecidableEq
inductive Evidence where
  | receipt (data : String)
  | theoremWarrant (declaration : String)
  | derived (premises : List Nat) (sideReceipt : String)
  | narrow (premise : Nat)
  | citation (text : String)
  | assertion
  | attempt (status : AttemptStatus)
  deriving Repr, BEq, DecidableEq
structure Warrant where
  id : Nat
  claim : Nat
  version : Nat
  binding : Binding
  evidence : Evidence
  deriving Repr, BEq, DecidableEq
structure Current where
  claim : Nat
  version : Nat
  binding : Binding
  deriving Repr, BEq, DecidableEq
inductive Event where
  | declareClaim (claim : Nat)
  | current (value : Current)
  | warrant (value : Warrant)
  | retract (target : Nat)
  | supersede (target successor : Nat)
  deriving Repr, BEq, DecidableEq
structure Snapshot where
  domain : List Nat
  currents : List Current
  warrants : List Warrant
  retracted : List Nat
  successors : List (Nat × Nat)
  deriving Repr, BEq, DecidableEq
def canonicalIds (xs : List Nat) : List Nat :=
  xs.eraseDups.mergeSort (fun a b => a ≤ b)
def currentsIn (events : List Event) : List Current :=
  events.filterMap fun e => match e with | .current c => some c | _ => none
def warrantsIn (events : List Event) : List Warrant :=
  events.filterMap fun e => match e with | .warrant w => some w | _ => none
def currentFor (values : List Current) (claim : Nat) : Except String Current := do
  let matching := values.filter fun v => v.claim == claim
  let newest := matching.foldl (fun n v => max n v.version) 0
  match (matching.filter fun v => v.version == newest).eraseDups with
  | [value] => return value
  | [] => throw s!"missing current binding: {claim}"
  | _ => throw s!"conflicting current bindings: {claim}"
def warrantFor (values : List Warrant) (id : Nat) : Except String Warrant :=
  match (values.filter fun w => w.id == id).eraseDups with
  | [value] => .ok value
  | [] => .error s!"missing warrant: {id}"
  | _ => .error s!"conflicting warrant contents: {id}"
def follows (links : List (Nat × Nat)) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | n+1, source, target =>
    links.any fun edge => edge.1 == source &&
      (edge.2 == target || follows links n edge.2 target)
def resolve (events : List Event) : Except String Snapshot := do
  let cs := currentsIn events
  let ws := warrantsIn events
  let currentIds := canonicalIds (cs.map (·.claim))
  let currents ← currentIds.mapM (currentFor cs)
  let warrantIds := canonicalIds (ws.map (·.id))
  let warrants ← warrantIds.mapM (warrantFor ws)
  let retracted := canonicalIds (events.filterMap fun e =>
    match e with | .retract target => some target | _ => none)
  let links := (events.filterMap fun e =>
    match e with | .supersede a b => some (a,b) | _ => none).eraseDups.mergeSort
      (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2))
  for (a,b) in links do
    if a == b then throw s!"self supersession: {a}"
    if !warrantIds.contains a || !warrantIds.contains b then
      throw s!"missing supersession endpoint: {a}->{b}"
    if retracted.contains a then throw s!"withdrawal and replacement: {a}"
    if follows links links.length b a then throw s!"supersession cycle: {a}"
  let declared := events.filterMap fun e =>
    match e with | .declareClaim key => some key | _ => none
  return {
    domain := canonicalIds (declared ++ currentIds)
    currents := currents
    warrants := warrants
    retracted := retracted
    successors := links }
def live (snapshot : Snapshot) (warrant : Warrant) : Bool :=
  snapshot.domain.contains warrant.claim &&
  !snapshot.retracted.contains warrant.id &&
  !(snapshot.successors.any fun edge => edge.1 == warrant.id) &&
  snapshot.currents.any fun c =>
    c.claim == warrant.claim && c.version == warrant.version &&
    c.binding == warrant.binding
-- Liveness is custody eligibility, not evidence validation or held authority.
def eligibleIds (snapshot : Snapshot) : List Nat :=
  (snapshot.warrants.filter (live snapshot)).map (·.id)
end GP50
