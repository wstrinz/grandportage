import GP50.Entry
import GP50.Presentation
import GP50.AdmissionProofs
import GP50.SpanSoundnessProofs
namespace ConditionalPartition
open GP50 Lean

-- Names are the literal parent/left/right objects in the three selected fixtures.
structure World (Point : Type) where
  parent : Point → Prop
  left : Point → Prop
  right : Point → Prop
inductive Formula where
  | leftEmpty | rightEmpty | exhaustive | parentEmpty
  deriving DecidableEq
def denotation {Point : Type} : Formula → World Point → Prop
  | .leftEmpty, world => ∀ x, ¬world.left x
  | .rightEmpty, world => ∀ x, ¬world.right x
  | .exhaustive, world => ∀ x, world.parent x → world.left x ∨ world.right x
  | .parentEmpty, world => ∀ x, ¬world.parent x
def Hypotheses {Point : Type} (left right verified : Bool) (world : World Point) : Prop :=
  (left = true → denotation .leftEmpty world) ∧
  (right = true → denotation .rightEmpty world) ∧
  (verified = true → denotation .exhaustive world)
def Means (Point : Type) (left right verified : Bool) (formula : Formula) : Prop :=
  ∀ world : World Point, Hypotheses left right verified world → denotation formula world

theorem left_assumption_sound (Point : Type) (left right verified : Bool)
    (given : left = true) : Means Point left right verified .leftEmpty :=
  fun _ hypotheses => hypotheses.1 given
theorem right_assumption_sound (Point : Type) (left right verified : Bool)
    (given : right = true) : Means Point left right verified .rightEmpty :=
  fun _ hypotheses => hypotheses.2.1 given
theorem coverage_assumption_sound (Point : Type) (left right verified : Bool)
    (given : verified = true) : Means Point left right verified .exhaustive :=
  fun _ hypotheses => hypotheses.2.2 given
theorem partition_composition_sound (Point : Type) (left right verified : Bool)
    (le : Means Point left right verified .leftEmpty)
    (re : Means Point left right verified .rightEmpty)
    (cover : Means Point left right verified .exhaustive) :
    Means Point left right verified .parentEmpty := by
  intro world hypotheses x present
  rcases cover world hypotheses x present with inLeft | inRight
  · exact le world hypotheses x inLeft
  · exact re world hypotheses x inRight

def statement : Nat → String
  | 1 => "left branch is empty"
  | 2 => "right branch is empty"
  | 3 => "the parent is empty"
  | 4 => "parent is covered by [left,right]"
  | _ => "unregistered"
def binding (source : String) (claim : Nat) : Binding :=
  ⟨statement claim,source,"contexts=[parent,left,right];partition=parent:[left,right]",
    [source],"test-only-named-partition-assumptions",1,1⟩
def left (source : String) : Warrant :=
  ⟨10,1,1,binding source 1,.receipt "given:left branch is empty"⟩
def right (source : String) : Warrant :=
  ⟨20,2,1,binding source 2,.receipt "given:right branch is empty"⟩
def coverage (source : String) : Warrant :=
  ⟨40,4,1,binding source 4,.receipt "given:exhaustive parent:[left,right]"⟩
def target (source : String) (dependencies : List Nat := [10,20,40]) : Warrant :=
  ⟨30,3,1,binding source 3,.derived dependencies "named-partition-composition"⟩
def admission (source : String) (lg rg verified : Bool) : Admission :=
  {Admission.refuseAll with
    receipt := fun w name =>
      (lg && decide (w = left source ∧ name = "given:left branch is empty")) ||
      (rg && decide (w = right source ∧ name = "given:right branch is empty")) ||
      (verified && decide (w = coverage source ∧ name = "given:exhaustive parent:[left,right]"))
    rule := fun w premises name =>
      decide (w = target source ∧ premises = [left source,right source,coverage source] ∧
        name = "named-partition-composition")}
theorem admitted_rule_exact (source : String) (lg rg verified : Bool)
    (w : Warrant) (premises : List Warrant) (side : String)
    (accepted : (admission source lg rg verified).rule w premises side = true) :
    w = target source ∧ premises = [left source,right source,coverage source] ∧
      side = "named-partition-composition" := of_decide_eq_true accepted

theorem omitted_argument_refused (source : String) (lg rg verified : Bool)
    (dependencies : List Nat) (different : dependencies ≠ [10,20,40])
    (premises : List Warrant) (side : String) :
    (admission source lg rg verified).rule (target source dependencies) premises side = false := by
  cases checked : (admission source lg rg verified).rule (target source dependencies) premises side with
  | false => rfl
  | true =>
    have exactRecord := (admitted_rule_exact source lg rg verified _ premises side checked).1
    have evidence := congrArg Warrant.evidence exactRecord
    have same : dependencies = [10,20,40] := (Evidence.derived.inj evidence).1
    exact (different same).elim

theorem all_given_semantically_empty (Point : Type) : Means Point true true true .parentEmpty :=
  partition_composition_sound Point true true true
    (left_assumption_sound Point true true true rfl)
    (right_assumption_sound Point true true true rfl)
    (coverage_assumption_sound Point true true true rfl)

def ClaimMeaning (Point : Type) (lg rg verified : Bool) : Nat → Prop
  | 1 => Means Point lg rg verified .leftEmpty
  | 2 => Means Point lg rg verified .rightEmpty
  | 3 => Means Point lg rg verified .parentEmpty
  | 4 => Means Point lg rg verified .exhaustive
  | _ => False
private def Truth (Point : Type) (lg rg verified : Bool) (snapshot : Snapshot) (id : Nat) : Prop :=
  ∀ w ∈ snapshot.warrants, w.id = id → ClaimMeaning Point lg rg verified w.claim
private theorem lift_truth (Point : Type) (lg rg verified : Bool) (snapshot : Snapshot)
    (unique : (snapshot.warrants.map (·.id)).Nodup) (w : Warrant) (present : w ∈ snapshot.warrants)
    (meaning : ClaimMeaning Point lg rg verified w.claim) :
    Truth Point lg rg verified snapshot w.id := by
  intro other otherPresent sameId
  have equal := key_unique_of_nodup snapshot.warrants (fun w => w.id) unique
    other w otherPresent present sameId
  exact equal ▸ meaning

theorem actual_validator_sound (Point : Type) (source : String) (lg rg verified : Bool)
    (snapshot : Snapshot) (unique : (snapshot.warrants.map (·.id)).Nodup) :
    ValidatorSound (admission source lg rg verified) snapshot (Truth Point lg rg verified snapshot) := by
  constructor
  · intro w present name accepted
    simp only [admission, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at accepted
    rcases accepted with (⟨given, same, _⟩ | ⟨given, same, _⟩) | ⟨given, same, _⟩
    · subst w
      exact lift_truth Point lg rg verified snapshot unique _ present
        (left_assumption_sound Point lg rg verified given)
    · subst w
      exact lift_truth Point lg rg verified snapshot unique _ present
        (right_assumption_sound Point lg rg verified given)
    · subst w
      exact lift_truth Point lg rg verified snapshot unique _ present
        (coverage_assumption_sound Point lg rg verified given)
  · intro w present name accepted; contradiction
  · intro w present premises name accepted members truePremises
    have checked := of_decide_eq_true accepted
    rcases checked with ⟨same, samePremises, _⟩
    subst w; subst premises
    have lp := members (left source) (by simp)
    have rp := members (right source) (by simp)
    have cp := members (coverage source) (by simp)
    have lt := truePremises (left source) (by simp) (left source) lp rfl
    have rt := truePremises (right source) (by simp) (right source) rp rfl
    have ct := truePremises (coverage source) (by simp) (coverage source) cp rfl
    exact lift_truth Point lg rg verified snapshot unique _ present
      (partition_composition_sound Point lg rg verified lt rt ct)
  · intro w present premise premisePresent accepted meaning; contradiction

theorem actual_fold_held_sound (Point : Type) (source : String) (lg rg verified : Bool)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission source lg rg verified) events = .ok state)
    (holds : held state claim = true) : ClaimMeaning Point lg rg verified claim := by
  unfold fold at folded
  cases resolved : resolve events with
  | error e => simp [resolved] at folded
  | ok snapshot =>
    rw [resolved] at folded
    have same := Except.ok.inj folded
    subst state
    exact evaluate_held_truth_composition _ snapshot (Truth Point lg rg verified snapshot)
      (ClaimMeaning Point lg rg verified)
      (actual_validator_sound Point source lg rg verified snapshot
        (resolve_warrant_ids_nodup events snapshot resolved))
      (fun w present meaning => meaning w present rfl) claim holds

example (Point : Type) (source : String) (lg rg verified : Bool)
    (events : List Event) (state : RuntimeState)
    (folded : fold (admission source lg rg verified) events = .ok state)
    (holds : held state 3 = true) : Means Point lg rg verified .parentEmpty :=
  actual_fold_held_sound Point source lg rg verified events state 3 folded holds

-- Missing right emptiness cannot be repaired by the exhaustive assumption alone.
example : ¬ Means Bool true false true .parentEmpty := by
  intro h
  let world : World Bool := ⟨fun _ => True, fun _ => False, fun _ => True⟩
  have assumptions : Hypotheses true false true world := by
    constructor
    · intro _ x; exact id
    · constructor
      · intro impossible; contradiction
      · intro _ x _; exact Or.inr trivial
  exact h world assumptions true trivial

def bindingJson (b : Binding) : Json := Json.mkObj [
  ("statementHash",toJson b.statementHash),("scopeHash",toJson b.scopeHash),
  ("modelHash",toJson b.modelHash),("inputHashes",toJson b.inputHashes),
  ("authority",toJson b.authority),("authorityVersion",toJson b.authorityVersion),
  ("kernelVersion",toJson b.kernelVersion)]
def warrantJson (w : Warrant) : Json :=
  let evidence := match w.evidence with
    | .receipt name => Json.mkObj [("kind",toJson "receipt"),("data",toJson name)]
    | .derived deps side => Json.mkObj [("kind",toJson "derived"),("premises",toJson deps),("sideReceipt",toJson side)]
    | _ => Json.mkObj [("kind",toJson "unregistered")]
  Json.mkObj [("id",toJson w.id),("claim",toJson w.claim),("version",toJson w.version),
    ("binding",bindingJson w.binding),("evidence",evidence)]
def currentJson (c : Current) : Json := Json.mkObj [
  ("claim",toJson c.claim),("version",toJson c.version),("binding",bindingJson c.binding)]
def snapshotJson (s : Snapshot) : Json := Json.mkObj [
  ("domain",toJson s.domain),("currents",toJson (s.currents.map currentJson)),
  ("warrants",toJson (s.warrants.map warrantJson)),("retracted",toJson s.retracted),
  ("successors",toJson s.successors)]

def strings (value : Json) : Except String (List String) := do
  let arr ← value.getArr?
  arr.toList.mapM Json.getStr?

def run (text digest mode : String) : Except String Json := do
  let json ← Decoder.parseUnique text
  Decoder.exactFields json ["schema_version","id","seed","title","situation","inputs",
    "attempted_conclusion","expected","scope_or_region","sources"]
  let version ← (← json.getObjVal? "schema_version").getNat?
  if version != 1 then throw "unsupported fixture schema"
  let caseId ← (← json.getObjVal? "id").getStr?
  if caseId != "GP-X183" && caseId != "GP-X184" && caseId != "GP-X186" then throw "uncommissioned case"
  let inputs ← json.getObjVal? "inputs"
  Decoder.exactFields inputs ["contexts","premises","conclusion_class","conclusion_text","cover"]
  let contexts ← strings (← inputs.getObjVal? "contexts")
  if contexts != ["parent","left","right"] then throw "wrong named context/model"
  let cls ← (← inputs.getObjVal? "conclusion_class").getStr?
  let conclusion ← (← inputs.getObjVal? "conclusion_text").getStr?
  if cls != "empty" || conclusion != "the parent is empty" then throw "unregistered conclusion"
  let cover ← inputs.getObjVal? "cover"
  Decoder.exactFields cover ["parent","branches","include_exhaustiveness_premise","verification_assumption"]
  let parent ← (← cover.getObjVal? "parent").getStr?
  let branches ← strings (← cover.getObjVal? "branches")
  if parent != "parent" || branches != ["left","right"] then throw "wrong selected partition"
  let includeCover ← (← cover.getObjVal? "include_exhaustiveness_premise").getBool?
  let verification ← (← cover.getObjVal? "verification_assumption").getStr?
  if verification != "exhaustive" then throw "unsupported verification assumption"
  let premises ← (← inputs.getObjVal? "premises").getArr?
  let mut lg := false
  let mut rg := false
  let mut dependencyIds : List Nat := []
  for premise in premises do
    Decoder.exactFields premise ["context","statement_class","statement"]
    let context ← (← premise.getObjVal? "context").getStr?
    let pclass ← (← premise.getObjVal? "statement_class").getStr?
    let content ← (← premise.getObjVal? "statement").getStr?
    if pclass != "empty" then throw "unregistered premise class"
    if context == "left" && content == "left branch is empty" then
      if lg then throw "duplicate source premise"
      lg := true
      dependencyIds := dependencyIds ++ [10]
    else if context == "right" && content == "right branch is empty" then
      if rg then throw "duplicate source premise"
      rg := true
      dependencyIds := dependencyIds ++ [20]
    else throw "wrong selected branch/statement"
  if includeCover then dependencyIds := dependencyIds ++ [40]
  let verified := mode != "unverified_cover"
  let mut roots := (if lg then [left digest] else []) ++ (if rg then [right digest] else []) ++
    (if verified then [coverage digest] else [])
  let mut destination := target digest dependencyIds
  if mode == "withheld_right" then roots := roots.filter fun w => w.id != 20
  if mode == "omit_exhaustive_argument" then destination := target digest (dependencyIds.filter (· != 40))
  if mode == "wrong_branch" then roots := roots.map fun w =>
    if w.id == 20 then {w with binding := {w.binding with statementHash := "left branch is empty"}} else w
  if mode == "wrong_model" then roots := roots.map fun w =>
    if w.id == 40 then {w with binding := {w.binding with modelHash := "contexts=[parent,left,other]"}} else w
  if mode == "wrong_binding" then roots := roots.map fun w =>
    if w.id == 10 then {w with binding := {w.binding with scopeHash := "different-source"}} else w
  if mode == "wrong_premise_id" then roots := roots.map fun w =>
    if w.id == 20 then {w with id := 99} else w
  if !(["normal","reverse","duplicates","withheld_right","omit_exhaustive_argument",
        "wrong_branch","wrong_model","wrong_binding","wrong_premise_id","unverified_cover"].contains mode) then
    throw "unknown control mode"
  let records := roots ++ [destination]
  let mut events := records.flatMap fun w => [.current ⟨w.claim,1,w.binding⟩,.warrant w]
  if mode == "reverse" then events := events.reverse
  if mode == "duplicates" then events := events ++ events
  let state ← fold (admission digest lg rg verified) events
  return Json.mkObj [("conditional",toJson true),("case",toJson caseId),("source_digest",toJson digest),
    ("mode",toJson mode),("literal_inputs",inputs),("conclusion",toJson conclusion),
    ("given",toJson ((if lg then ["left branch is empty"] else []) ++
      (if rg then ["right branch is empty"] else []) ++ (if verified then ["exhaustive parent:[left,right]"] else []))),
    ("argument_dependency_ids",toJson (match destination.evidence with | .derived deps _ => deps | _ => [])),
    ("state",stateJson state),("snapshot",snapshotJson state.snapshot)]

#print axioms actual_validator_sound
#print axioms actual_fold_held_sound
#print axioms partition_composition_sound
end ConditionalPartition

def main (args : List String) : IO UInt32 := do
  match args with
  | [path,digest,mode] =>
    let result := ConditionalPartition.run (← IO.FS.readFile path) digest mode
    IO.println (match result with
      | .ok output => output.compress
      | .error e => (Lean.Json.mkObj [("status",Lean.toJson "MALFORMED"),("error",Lean.toJson e)]).compress)
    return 0
  | _ => return 2
