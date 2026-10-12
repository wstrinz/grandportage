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

-- Post-G4 Track K: the compiled fold indexes a snapshot once instead of scanning it per warrant.
-- `supportNodes` and `projectClaims` are unchanged; their `csimp` twins are proved equal.
structure SnapshotIndex where
  domain : Std.HashSet Nat
  retracted : Std.HashSet Nat
  superseded : Std.HashSet Nat
  currents : Std.HashMap Nat (List Current)
  warrants : Std.HashMap Nat Warrant

def firstById (ws : List Warrant) : Std.HashMap Nat Warrant :=
  ws.foldr (fun w m => m.insert w.id w) ∅

theorem firstById_get (ws : List Warrant) (id : Nat) :
    (firstById ws)[id]? = ws.find? fun w => w.id == id := by
  induction ws with
  | nil => simp [firstById]
  | cons w ws ih =>
    simp only [firstById, List.foldr_cons] at ih ⊢
    rw [Std.HashMap.getElem?_insert, List.find?_cons]
    cases w.id == id <;> simp [ih]

def SnapshotIndex.of (snapshot : Snapshot) : SnapshotIndex :=
  ⟨.ofList snapshot.domain, .ofList snapshot.retracted,
    .ofList (snapshot.successors.map (·.1)), groupBy (·.claim) snapshot.currents,
    firstById snapshot.warrants⟩

def liveIdx (index : SnapshotIndex) (warrant : Warrant) : Bool :=
  index.domain.contains warrant.claim &&
  !index.retracted.contains warrant.id &&
  !index.superseded.contains warrant.id &&
  (index.currents.getD warrant.claim []).any fun c =>
    c.claim == warrant.claim && c.version == warrant.version &&
    c.binding == warrant.binding

theorem contains_map_fst (links : List (Nat × Nat)) (id : Nat) :
    (links.map (·.1)).contains id = links.any fun edge => edge.1 == id := by
  induction links with
  | nil => rfl
  | cons edge links ih =>
    simp only [List.map_cons, List.contains_cons, List.any_cons, ih, BEq.comm (a := id)]

theorem liveIdx_of (snapshot : Snapshot) : liveIdx (SnapshotIndex.of snapshot) = live snapshot := by
  funext warrant
  simp only [liveIdx, live, SnapshotIndex.of, Std.HashSet.contains_ofList, groupBy_getD,
    List.any_filter, contains_map_fst]
  congr 2
  funext c
  cases c.claim == warrant.claim <;> rfl

-- Runner surfaces (Presentation, LifecycleRunner) import this module, so this twin reaches them.
def eligibleIdsFast (snapshot : Snapshot) : List Nat :=
  let index := SnapshotIndex.of snapshot
  (snapshot.warrants.filter (liveIdx index)).map (·.id)

@[csimp] theorem eligibleIds_eq_eligibleIdsFast : @eligibleIds = @eligibleIdsFast := by
  funext snapshot
  simp only [eligibleIds, eligibleIdsFast, liveIdx_of]

def requirementsWith (admission : Admission) (isLive : Warrant → Bool)
    (lookup : Nat → Option Warrant) (warrant : Warrant) : Option (List Nat) :=
  if !isLive warrant then none else
  match warrant.evidence with
  | .receipt data => if admission.receipt warrant data then some [] else none
  | .theoremWarrant declaration =>
    if admission.proof warrant declaration then some [] else none
  | .derived dependencies side =>
    match dependencies.mapM lookup with
    | none => none
    | some premises =>
      if admission.rule warrant premises side then some dependencies else none
  | .narrow dependency =>
    match lookup dependency with
    | none => none
    | some premise =>
      if admission.narrow warrant premise then some [dependency] else none
  | .citation _ | .assertion | .attempt _ => none

theorem requirements_eq_requirementsWith (admission : Admission) (snapshot : Snapshot) :
    requirements admission snapshot =
      requirementsWith admission (live snapshot) (lookupWarrant snapshot) := rfl

def supportNodesFast (admission : Admission) (snapshot : Snapshot) : List SupportNode :=
  let index := SnapshotIndex.of snapshot
  snapshot.warrants.map fun w =>
    ⟨w.id, requirementsWith admission (liveIdx index) (fun id => index.warrants[id]?) w⟩

@[csimp] theorem supportNodes_eq_supportNodesFast : @supportNodes = @supportNodesFast := by
  funext admission snapshot
  have lookup : (fun id => (SnapshotIndex.of snapshot).warrants[id]?) = lookupWarrant snapshot := by
    funext id
    exact firstById_get snapshot.warrants id
  simp only [supportNodes, supportNodesFast, requirements_eq_requirementsWith, liveIdx_of, lookup]

def projectClaimsFast (snapshot : Snapshot) (supports : List Nat) : List Nat :=
  let supported := Std.HashSet.ofList supports
  canonicalIds ((snapshot.warrants.filter fun w => supported.contains w.id).map (·.claim))

@[csimp] theorem projectClaims_eq_projectClaimsFast : @projectClaims = @projectClaimsFast := by
  funext snapshot supports
  simp only [projectClaims, projectClaimsFast, Std.HashSet.contains_ofList]

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
