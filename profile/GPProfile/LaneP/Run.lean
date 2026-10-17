import GPProfile.LaneP.Bridge
import GPProfile.LaneP.Withdraw
import Lean.Data.Json

/-!
The Lane P runner behind `tools/gp_lanep.py` (`gp_ledgerp run <plan.json>`). Python serialises the
ledger's registered codes, the current bind's report, the P claims and their records; this runner builds
the clauses, bindings and Kernel events, folds under `LaneP.admission`, and computes the views:

- **tier:** the held tier (Comparator receipt 1, theorem 2, bridge 3, a discharge the weaker of its two
  premises, a weakening its source's), and the best tier along any path including recorded-only steps,
  which never hold;
- **fidelity:** the lowest over the statement and its premises;
- **OVERSTATED:** a presentation whose tag is above the earned tier, or which drops a mathematical
  premise (a tag of tier 7 asserts nothing and is never overstated). Leaving out an open *process*
  condition (a pending review, merge, wording fix or fidelity review) is not OVERSTATED: it is reported
  as `conditionsOpen` (GP 0.52 P2);
- **frontier:** premise codes no held claim settles, ranked by the claims whose scope contains them.

Every held verdict comes from the Kernel fold (`fold_held_meaningP`, with bridges
`fold_held_meaningP_bridged`); withdrawn claims are not held (`run_withdrawn`). Mathlib-free.
-/

namespace GPProfile.LaneP.Run
open Lean GP50 GPProfile.LaneP

inductive Support where
  | none
  | thm (declaration : String)
  /-- From the claim `(s, S ∪ {h})` keyed `source` and the claim `(h, T)` keyed `by`. -/
  | discharge (source by_ : Nat)
  /-- Weakening (Kernel narrowing) from the claim keyed `source`. -/
  | weaken (source : Nat)
  /-- A Comparator receipt (tier 1), checked against the binder-class record `declaration`. -/
  | cmp (declaration : String)
  /-- A bridge (tier 3): the claim's statement code is a bridge code, held by its re-folded 3a/3b claim. -/
  | bridge
  deriving Repr, BEq

def Support.slot : Support → Option Nat
  | .none => Option.none
  | .thm _ => some 0
  | .discharge _ _ => some 1
  | .weaken _ => some 2
  | .cmp _ => some 4
  | .bridge => some 5

/-- A recorded-only warrant: the tier it shows (0 when it earns none, as a sketch) and its digest. -/
structure Recorded where
  tier : Nat
  digest : String
  deriving Repr, BEq

structure Item where
  key : Nat
  stmt : Nat
  scope : List Nat
  support : Support
  recorded : List Recorded
  /-- Reviewers' conditions on recorded hand proofs: OPEN premises a presentation must state. -/
  conditions : List Nat
  /-- Open process conditions (reviews, merges, wording, fidelity reviews): shown, never OVERSTATED. -/
  process : List Nat
  /-- Each presentation's tag tier and the premises it states. -/
  presentations : List (Nat × List Nat)

structure CodeInfo where
  code : Nat
  hash : String
  stamp : String
  current : Option (String × String)
  fidelity : Nat

structure Plan where
  codes : List CodeInfo
  records : List Record
  items : List Item
  withdrawn : List Nat
  bridges : List Bridge := []

/-! ## Clauses, bindings and events -/

def Plan.registered (p : Plan) (c : Nat) : String × String :=
  match p.codes.find? (·.code == c) with
  | some i => (i.hash, i.stamp)
  | none => ("unregistered", "unregistered")

def Plan.binding (p : Plan) (i : Item) : Binding :=
  { statementHash := s!"P:{i.stmt}:{(p.registered i.stmt).1}"
    scopeHash := ",".intercalate (i.scope.map fun c => s!"{c}:{(p.registered c).1}")
    modelHash := "gp-lanep/v1", inputHashes := [(p.registered i.stmt).2], authority := "lanep"
    authorityVersion := 1, kernelVersion := 1 }

def Plan.clauses (p : Plan) : List Clause := p.items.map fun i => ⟨i.key, 1, p.binding i, i.stmt, i.scope⟩

def Plan.identity (p : Plan) : Identity :=
  ⟨p.codes.map fun i => (i.code, i.hash, i.stamp), p.codes.filterMap fun i => i.current.map (i.code, ·)⟩

/-- The warrant id a premise reference points at: the referenced claim's support slot, or slot 15,
which no claim files, when it has none. -/
def Plan.primary (p : Plan) (k : Nat) : Nat :=
  pWarrantId k (((p.items.find? (·.key == k)).bind (·.support.slot)).getD 15)

def citeDigest (rs : List Recorded) : String :=
  ";".intercalate ((rs.map fun r => s!"{r.tier}:{r.digest}").mergeSort (· ≤ ·))

def Plan.warrants (p : Plan) (i : Item) : List Warrant :=
  let b := p.binding i
  let support : List Warrant := match i.support with
    | .none => []
    | .thm d => [⟨pWarrantId i.key 0, i.key, 1, b, .theoremWarrant d⟩]
    | .discharge k1 k2 => [⟨pWarrantId i.key 1, i.key, 1, b, .derived [p.primary k1, p.primary k2] "discharge"⟩]
    | .weaken k1 => [⟨pWarrantId i.key 2, i.key, 1, b, .narrow (p.primary k1)⟩]
    | .cmp d => [⟨pWarrantId i.key 4, i.key, 1, b, .theoremWarrant d⟩]
    | .bridge => [⟨pWarrantId i.key 5, i.key, 1, b, .theoremWarrant s!"bridge:{i.stmt}"⟩]
  support ++ if i.recorded.isEmpty then [] else [⟨pWarrantId i.key 3, i.key, 1, b, .citation (citeDigest i.recorded)⟩]

def Plan.events (p : Plan) : List Event :=
  p.items.flatMap fun i => [.declareClaim i.key, .current ⟨i.key, 1, p.binding i⟩] ++ (p.warrants i).map .warrant

/-- The binder's theorem and receipt records, then one record per bridge (`bridgeRecord`). -/
def Plan.allRecords (p : Plan) : List Record := p.records ++ p.bridges.map bridgeRecord

def Plan.admission (p : Plan) : Admission := LaneP.admission p.clauses p.identity p.allRecords

def Plan.fold (p : Plan) : Except String RuntimeState :=
  GP50.fold p.admission (p.events ++ withdrawEventsP p.withdrawn)

theorem events_noSupersede (p : Plan) : GPProfile.Withdraw.NoSupersede p.events := by
  intro e he a b heq
  subst heq
  simp only [Plan.events, List.mem_flatMap, List.mem_append, List.mem_cons, List.mem_map] at he
  obtain ⟨i, -, he⟩ := he
  rcases he with (h | h | h) | ⟨w, -, h⟩ <;> cases h

theorem events_ids (p : Plan) : ProfileIdsP p.events := by
  intro w hw
  simp only [Plan.events, List.mem_flatMap, List.mem_append, List.mem_cons, List.mem_map,
    Event.warrant.injEq] at hw
  obtain ⟨i, -, hw⟩ := hw
  rcases hw with (h | h | h) | ⟨w', hw', rfl⟩
  · cases h
  · cases h
  · simp at h
  · simp only [Plan.warrants, List.mem_append] at hw'
    rcases hw' with hs | hc
    · cases hsup : i.support <;> simp only [hsup, List.mem_singleton, List.not_mem_nil] at hs <;>
        subst hs <;> exact ⟨_, by decide, rfl⟩
    · split at hc
      · simp at hc
      · simp only [List.mem_singleton] at hc
        subst hc
        exact ⟨3, by decide, rfl⟩

/-- W3P for every run: a withdrawn claim is not held. -/
theorem run_withdrawn (p : Plan) (s : RuntimeState) (h : p.fold = .ok s) {k : Nat} (hk : k ∈ p.withdrawn) :
    held s k = false :=
  withdraw_unholdsP _ _ _ (events_noSupersede p) (events_ids p) hk s h

/-! ## Views -/

def Plan.item? (p : Plan) (k : Nat) : Option Item := p.items.find? (·.key == k)

def maxOpt : Option Nat → Option Nat → Option Nat
  | some a, some b => some (max a b)
  | _, _ => none

def minOpt : Option Nat → Option Nat → Option Nat
  | some a, some b => some (min a b)
  | some a, none => some a
  | none, b => b

/-- One round of tier propagation. `held` restricts to warrants the fold supports; otherwise every
statically admitted step counts, and recorded-only warrants count at their tier. -/
def Plan.tierStep (p : Plan) (state : RuntimeState) (heldOnly : Bool) (t : List (Nat × Option Nat)) :
    List (Nat × Option Nat) :=
  let a := p.admission
  let look (k : Nat) : Option Nat := (t.lookup k).join
  let clause (k : Nat) : Option Clause := p.clauses.find? (·.key == k)
  -- Held: the fold supports the warrant. Best: its step is admitted on the clauses alone (the premise
  -- claims may rest on recorded-only warrants, which never hold) and the claim is not withdrawn.
  let ok (w : Warrant) (static : Bool) : Bool :=
    if heldOnly then state.supports.contains w.id else static && !p.withdrawn.contains w.claim
  p.items.map fun i =>
    let fromSupport : Option Nat := match p.warrants i, i.support with
      | w :: _, .thm d => if ok w (a.proof w d) then some 2 else none
      | w :: _, .cmp d => if ok w (a.proof w d) then some 1 else none
      | w :: _, .bridge => if ok w (a.proof w s!"bridge:{i.stmt}") then some 3 else none
      | w :: _, .discharge k1 k2 =>
        let static := match clause i.key, clause k1, clause k2 with
          | some c, some c1, some c2 => dischargeOk c c1 c2
          | _, _, _ => false
        if ok w static then maxOpt (look k1) (look k2) else none
      | w :: _, .weaken k1 =>
        let static := match clause i.key, clause k1 with
          | some c, some c1 => Semantic.checkNarrow ops c c1
          | _, _ => false
        if ok w static then look k1 else none
      | _, _ => none
    let fromRecorded : Option Nat :=
      if heldOnly || p.withdrawn.contains i.key then none
      else i.recorded.foldl (fun acc r => if r.tier == 0 then acc else minOpt acc (some r.tier)) none
    (i.key, minOpt fromSupport fromRecorded)

def Plan.tiers (p : Plan) (state : RuntimeState) (heldOnly : Bool) : List (Nat × Option Nat) :=
  (List.range (p.items.length + 1)).foldl (fun t _ => p.tierStep state heldOnly t)
    (p.items.map fun i => (i.key, none))

def Plan.fidelity (p : Plan) (c : Nat) : Nat := ((p.codes.find? (·.code == c)).map (·.fidelity)).getD 0

def itemJson (p : Plan) (state : RuntimeState) (heldT bestT : List (Nat × Option Nat)) (i : Item) : Json :=
  let h := held state i.key
  let ht := (heldT.lookup i.key).join
  let bt := (bestT.lookup i.key).join
  let earned := ((if h then ht else bt).getD 7)
  -- A tag of tier 7 (conjecture, open) asserts nothing, so it overstates nothing. Process conditions left out
  -- are open conditions, not an overstatement.
  let over := i.presentations.map fun (tag, prem) =>
    tag < 7 && (tag < earned || !sub (i.scope ++ i.conditions) prem)
  let condOpen := i.presentations.map fun (tag, prem) => tag < 7 && !sub i.process prem
  let settled := i.scope.filterMap fun c =>
    (p.items.find? fun j => j.stmt == c && held state j.key && sub j.scope (i.scope.erase c)).map
      fun j => Json.arr #[toJson c, toJson j.key]
  let fid := (i.stmt :: i.scope).foldl (fun m c => min m (p.fidelity c)) 3
  let supported := (p.warrants i).filter (state.supports.contains ·.id) |>.map (·.id)
  Json.mkObj [("key", toJson i.key), ("held", toJson h), ("tier", toJson ht), ("best", toJson bt),
    ("earned", toJson earned), ("overstated", toJson over), ("conditionsOpen", toJson condOpen),
    ("settled", Json.arr settled.toArray),
    ("fidelity", toJson fid), ("supported", toJson supported),
    ("proofAccepted", toJson (match p.warrants i, i.support with
      | w :: _, .thm d | w :: _, .cmp d => p.admission.proof w d
      | w :: _, .bridge => p.admission.proof w s!"bridge:{i.stmt}"
      | _, _ => false))]

def frontier (p : Plan) (state : RuntimeState) : List (Nat × Nat) :=
  let live := p.items.filter fun i => !p.withdrawn.contains i.key
  let codes := canonicalIds (live.flatMap (·.scope))
  let open_ := codes.filter fun c => !(p.items.any fun j => j.stmt == c && j.scope.isEmpty && held state j.key)
  let counted := open_.map fun c => (c, (live.filter (·.scope.contains c)).length)
  counted.mergeSort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 ≤ b.1)

def run (p : Plan) : Except String Json := do
  let state ← p.fold
  let heldT := p.tiers state true
  let bestT := p.tiers state false
  pure (Json.mkObj [("schema", "gp-ledgerp-run/v1"),
    ("items", Json.arr (p.items.map (itemJson p state heldT bestT)).toArray),
    ("frontier", Json.arr ((frontier p state).map fun (c, n) => Json.mkObj [("code", toJson c), ("unlocks", toJson n)]).toArray)])

/-! ## JSON -/

def need {α : Type} (o : Except String α) (msg : String) : Except String α :=
  match o with
  | .ok a => pure a
  | .error e => throw s!"{msg}: {e}"

def nats (j : Json) (k : String) : Except String (List Nat) := do
  (← (← j.getObjVal? k).getArr?).toList.mapM Json.getNat?

def support (j : Json) : Except String Support :=
  match j.getObjVal? "support" with
  | .error _ | .ok .null => pure .none
  | .ok s => do
    match ← s.getObjValAs? String "kind" with
    | "theorem" => pure (.thm (← s.getObjValAs? String "decl"))
    | "discharge" => pure (.discharge (← s.getObjValAs? Nat "from") (← s.getObjValAs? Nat "by"))
    | "weaken" => pure (.weaken (← s.getObjValAs? Nat "from"))
    | "comparator" => pure (.cmp (← s.getObjValAs? String "decl"))
    | "bridge" => pure .bridge
    | k => throw s!"unknown support kind {k}"

def item (j : Json) : Except String Item := do
  let recorded ← (← (← j.getObjVal? "recorded").getArr?).toList.mapM fun r => do
    pure (⟨← r.getObjValAs? Nat "tier", ← r.getObjValAs? String "digest"⟩ : Recorded)
  let pres ← (← (← j.getObjVal? "presentations").getArr?).toList.mapM fun r => do
    pure (← r.getObjValAs? Nat "tier", canonicalIds (← nats r "premises"))
  let opt (k : String) : Except String (List Nat) := match j.getObjVal? k with
    | .ok _ => nats j k
    | .error _ => pure []
  pure ⟨← j.getObjValAs? Nat "key", ← j.getObjValAs? Nat "stmt", canonicalIds (← nats j "scope"),
    ← support j, recorded, canonicalIds (← opt "conditions"), canonicalIds (← opt "process"), pres⟩

def codeInfo (j : Json) : Except String CodeInfo := do
  let current ← match j.getObjVal? "current" with
    | .ok .null | .error _ => pure none
    | .ok c => pure (some (← c.getObjValAs? String "hash", ← c.getObjValAs? String "stamp"))
  pure ⟨← j.getObjValAs? Nat "code", ← j.getObjValAs? String "hash", ← j.getObjValAs? String "stamp", current,
    (j.getObjValAs? Nat "fidelity").toOption.getD 0⟩

def record (j : Json) : Except String Record := do
  pure ⟨← j.getObjValAs? String "declaration", ← j.getObjValAs? Nat "stmt", ← nats j "premises",
    ← j.getObjValAs? Bool "ok"⟩

/-- A bridge: its code, its literal, and the 3a/3b part (3b surface inputs) re-folded for it. -/
def bridge (j : Json) : Except String Bridge := do
  pure ⟨← j.getObjValAs? Nat "code", ← j.getObjValAs? String "lit",
    ← need (GPProfile.Real.LedgerRun3.plan3 (← j.getObjVal? "plan")) "bridged part"⟩

def plan (j : Json) : Except String Plan := do
  let bridges ← match j.getObjVal? "bridges" with
    | .ok bs => need (bs.getArr? >>= (·.toList.mapM bridge)) "bridges"
    | .error _ => pure []
  pure ⟨← need ((← j.getObjVal? "codes").getArr? >>= (·.toList.mapM codeInfo)) "codes",
    ← need ((← j.getObjVal? "records").getArr? >>= (·.toList.mapM record)) "records",
    ← need ((← j.getObjVal? "claims").getArr? >>= (·.toList.mapM item)) "claims",
    ← nats j "withdrawn", bridges⟩

end GPProfile.LaneP.Run

open GPProfile.LaneP.Run in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["run", path] =>
    let text ← IO.FS.readFile path
    let o := match Lean.Json.parse text >>= plan with
      | .error e => Lean.Json.mkObj [("elaboration", Lean.toJson e)]
      | .ok p => match run p with
        | .ok o => o
        | .error e => Lean.Json.mkObj [("error", Lean.toJson e)]
    IO.println o.compress
    return 0
  | ["bridge", path] =>
    -- One bridge's verdict, `bridgeOk` (0.54): gp caches it by the SHA-256 of the bridge input and gives the fold
    -- the bridge's record (`bridgeRecord`) with it, so a bridged ledger is re-folded once per change.
    let text ← IO.FS.readFile path
    let o := match Lean.Json.parse text >>= bridge with
      | .error e => Lean.Json.mkObj [("elaboration", Lean.toJson e)]
      | .ok b => Lean.Json.mkObj [("ok", Lean.toJson (GPProfile.LaneP.bridgeOk b))]
    IO.println o.compress
    return 0
  | _ => IO.eprintln "usage: gp_ledgerp run <plan.json> | gp_ledgerp bridge <bridge.json>"; return 2
