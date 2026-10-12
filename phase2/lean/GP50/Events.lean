import Std
import GP50.Closure
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
-- Post-G4 Track K: hash-indexed twin; the `csimp` lemma changes compiled code only.
def canonicalIdsFast (xs : List Nat) : List Nat :=
  (eraseDupsHash xs).mergeSort (fun a b => a ≤ b)
@[csimp] theorem canonicalIds_eq_canonicalIdsFast : @canonicalIds = @canonicalIdsFast := by
  funext xs
  simp only [canonicalIds, canonicalIdsFast, eraseDups_eq_eraseDupsHash]
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
-- Post-G4 Track K: `resolveFast` groups by key once and tests membership by hash. It keeps
-- `resolve`'s order of checks, so its errors are identical; `resolve_eq_resolveFast` proves it.
def groupBy {α} (key : α → Nat) (xs : List α) : Std.HashMap Nat (List α) :=
  xs.foldr (fun x m => m.insert (key x) (x :: m.getD (key x) [])) ∅
theorem groupBy_getD {α} (key : α → Nat) (xs : List α) (k : Nat) :
    (groupBy key xs).getD k [] = xs.filter fun x => key x == k := by
  induction xs with
  | nil => simp [groupBy]
  | cons x xs ih =>
    simp only [groupBy, List.foldr_cons] at ih ⊢
    rw [Std.HashMap.getD_insert, List.filter_cons]
    split <;> rename_i hx
    · rw [beq_iff_eq.mp hx, ih]
    · exact ih
def followsIdx (next : Std.HashMap Nat (List (Nat × Nat))) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | n+1, source, target =>
    (next.getD source []).any fun edge => edge.1 == source &&
      (edge.2 == target || followsIdx next n edge.2 target)
theorem followsIdx_eq (links : List (Nat × Nat)) :
    ∀ n source target, followsIdx (groupBy (·.1) links) n source target =
      follows links n source target
  | 0, _, _ => rfl
  | n+1, source, target => by
    simp only [followsIdx, follows, groupBy_getD, List.any_filter, followsIdx_eq links n]
    congr 1
    funext edge
    cases edge.1 == source <;> rfl
theorem currentFor_filter (cs : List Current) (claim : Nat) :
    currentFor (cs.filter fun c => c.claim == claim) claim = currentFor cs claim := by
  simp only [currentFor, List.filter_filter, Bool.and_self]
theorem warrantFor_filter (ws : List Warrant) (id : Nat) :
    warrantFor (ws.filter fun w => w.id == id) id = warrantFor ws id := by
  simp only [warrantFor, List.filter_filter, Bool.and_self]
def resolveFast (events : List Event) : Except String Snapshot := do
  let cs := currentsIn events
  let ws := warrantsIn events
  let byClaim := groupBy (·.claim) cs
  let byId := groupBy (·.id) ws
  let currentIds := canonicalIds (cs.map (·.claim))
  let currents ← currentIds.mapM fun k => currentFor (byClaim.getD k []) k
  let warrantIds := canonicalIds (ws.map (·.id))
  let warrants ← warrantIds.mapM fun k => warrantFor (byId.getD k []) k
  let retracted := canonicalIds (events.filterMap fun e =>
    match e with | .retract target => some target | _ => none)
  let links := (eraseDupsHash (events.filterMap fun e =>
    match e with | .supersede a b => some (a,b) | _ => none)).mergeSort
      (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2))
  let warrantSet := Std.HashSet.ofList warrantIds
  let retractedSet := Std.HashSet.ofList retracted
  let next := groupBy (·.1) links
  for (a,b) in links do
    if a == b then throw s!"self supersession: {a}"
    if !warrantSet.contains a || !warrantSet.contains b then
      throw s!"missing supersession endpoint: {a}->{b}"
    if retractedSet.contains a then throw s!"withdrawal and replacement: {a}"
    if followsIdx next links.length b a then throw s!"supersession cycle: {a}"
  let declared := events.filterMap fun e =>
    match e with | .declareClaim key => some key | _ => none
  return {
    domain := canonicalIds (declared ++ currentIds)
    currents := currents
    warrants := warrants
    retracted := retracted
    successors := links }
@[csimp] theorem resolve_eq_resolveFast : @resolve = @resolveFast := by
  funext events
  simp only [resolve, resolveFast, groupBy_getD, currentFor_filter, warrantFor_filter,
    Std.HashSet.contains_ofList, followsIdx_eq, eraseDups_eq_eraseDupsHash]
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
