import GP50.Entry
import GP50.Presentation
import GP50.NarrowingAdmissionProofs
namespace OpenPremiseGuard
open GP50 Lean GP50.Semantic

-- A frozen claim is either model-level or only about a family.
structure ClaimRec where
  id : String
  isModel : Bool
  scope : String
  statement : String
  deriving DecidableEq, BEq
inductive Slot where
  | filled (claim : String)
  | opened (requiredKind place why : String)
  deriving DecidableEq, BEq
structure Inference where
  id : String
  slots : List Slot
  asserted : String
  deriving DecidableEq, BEq
structure Input where
  claims : List ClaimRec
  inference : Inference
  deriving DecidableEq, BEq

def modelClaim (claims : List ClaimRec) (c : String) : Bool := claims.any fun r => r.id == c && r.isModel
-- Every slot must be filled by a model-level claim; open slots and family claims block.
def slotOK (claims : List ClaimRec) : Slot → Bool
  | .filled c => modelClaim claims c
  | .opened _ _ _ => false
def licensed (i : Input) : Bool := i.inference.slots.all (slotOK i.claims)

-- Arbitrary interpretations; family facts and model facts are distinct predicates.
structure World where
  modelTruth : String → Prop
  familyTruth : String → Prop
  openTruth : String → Prop
  concl : String → Prop
def slotMeaning (w : World) : Slot → Prop
  | .filled c => w.modelTruth c
  | .opened _ _ why => w.openTruth why

-- Supplied claims and the inference step are named premises; open slots are not.
structure Hypotheses (i : Input) (w : World) : Prop where
  namedModelClaims : ∀ r ∈ i.claims, r.isModel = true → w.modelTruth r.id
  namedFamilyClaims : ∀ r ∈ i.claims, r.isModel = false → w.familyTruth r.id
  namedInference : (∀ s ∈ i.inference.slots, slotMeaning w s) → w.concl i.inference.id

theorem licensed_slots (i : Input) (ok : licensed i = true) (w : World) (h : Hypotheses i w) :
    ∀ s ∈ i.inference.slots, slotMeaning w s := by
  intro s present
  have each := List.all_eq_true.mp ok s present
  cases s with
  | opened _ _ _ => simp [slotOK] at each
  | filled c =>
    simp only [slotOK,modelClaim,List.any_eq_true,Bool.and_eq_true,beq_iff_eq] at each
    rcases each with ⟨r,member,same,model⟩
    rw [← same]
    exact h.namedModelClaims r member model

inductive Formula where | conclusion (id : String) deriving DecidableEq
def holds : Formula → World → Prop | .conclusion id, w => w.concl id

def profile (i : Input) : Profile where
  Stmt := Formula
  Scope := Unit
  Ctx := World
  same := fun a b => decide (a = b)
  same_sound := fun _ _ h => of_decide_eq_true h
  mem := fun w _ => Hypotheses i w
  le := fun _ _ => true
  le_sound := fun _ _ _ _ present => present
  Holds := holds
  contra := fun _ _ => false
  contra_sound := by intro a b c impossible; contradiction

theorem licensed_conclusion_sound (i : Input) (ok : licensed i = true) :
    Means (profile i) (.conclusion i.inference.id) () :=
  fun w present => present.namedInference (licensed_slots i ok w present)

def statement (i : Input) : String := s!"inference conclusion:{i.inference.id}:{i.inference.asserted}"
def binding (i : Input) (source literal frame : String) : Binding :=
  ⟨statement i,"model-level premises",frame,[source,literal],"test-only-open-premise-guard-contract",1,1⟩
def clauses (i : Input) (source literal frame : String) : List (Clause (profile i)) :=
  [⟨1,1,binding i source literal frame,.conclusion i.inference.id,()⟩]
def inferenceW (i : Input) (source literal frame : String) : Warrant :=
  ⟨1,1,1,binding i source literal frame,.receipt s!"supplied:named-inference:{i.inference.id}"⟩
def custodyW (i : Input) (source literal frame : String) : Warrant :=
  ⟨100,100,1,{binding i source literal frame with statementHash := "custody"},.citation literal⟩
def base (i : Input) (source literal frame : String) : Admission :=
  {Admission.refuseAll with
    receipt := fun w data =>
      decide (w = inferenceW i source literal frame ∧ data = s!"supplied:named-inference:{i.inference.id}") && licensed i}
def admission (i : Input) (source literal frame : String) : Admission :=
  withNarrowing (profile i) (clauses i source literal frame) (base i source literal frame)

theorem actual_base_sound (i : Input) (source literal frame : String) (snapshot : Snapshot) :
    BaseValidatorSound (profile i) (clauses i source literal frame) (base i source literal frame) snapshot := by
  constructor
  · intro w present data accepted
    simp only [base,Bool.and_eq_true,decide_eq_true_eq] at accepted
    rcases accepted with ⟨⟨same,_⟩,ok⟩
    subst w
    refine ⟨inferenceW i source literal frame,present,rfl,⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩⟩
    intro c member key
    simp only [clauses,List.mem_singleton] at member
    subst c
    exact licensed_conclusion_sound i ok
  · intro w present declaration accepted; contradiction
  · intro w present premises side accepted; contradiction

theorem actual_validator_sound (i : Input) (source literal frame : String) (snapshot : Snapshot)
    (unique : (snapshot.warrants.map (·.id)).Nodup) :
    ValidatorSound (admission i source literal frame) snapshot
      (WarrantMeaning (profile i) (clauses i source literal frame) snapshot) :=
  withNarrowing_validator_sound _ _ _ snapshot unique (actual_base_sound i source literal frame snapshot)
theorem actual_fold_held_sound (i : Input) (source literal frame : String)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission i source literal frame) events = .ok state)
    (heldClaim : held state claim = true) : ClaimMeaning (profile i) (clauses i source literal frame) claim := by
  unfold fold at folded
  cases resolved : resolve events with
  | error err => simp [resolved] at folded
  | ok snapshot =>
    rw [resolved] at folded
    have same := Except.ok.inj folded
    subst state
    exact evaluate_held_meaning _ _ _ snapshot (resolve_warrant_ids_nodup events snapshot resolved)
      (actual_base_sound i source literal frame snapshot) claim heldClaim

-- With an open slot, every supplied premise and the inference step can hold while the conclusion fails.
theorem open_slot_blocks (i : Input) (k a why : String) (present : Slot.opened k a why ∈ i.inference.slots) :
    ∃ w, Hypotheses i w ∧ ¬ w.concl i.inference.id :=
  ⟨⟨fun _ => True,fun _ => True,fun _ => False,fun _ => False⟩,
    ⟨fun _ _ _ => trivial,fun _ _ _ => trivial,fun all => all _ present⟩,id⟩
-- A family-level fact never supplies the model-level premise a slot needs.
theorem family_fact_is_not_model_fact (c : String) :
    ∃ w : World, w.familyTruth c ∧ ¬ w.modelTruth c :=
  ⟨⟨fun _ => False,fun _ => True,fun _ => False,fun _ => False⟩,trivial,id⟩

def str (j : Json) (k : String) : Except String String := do (← j.getObjVal? k).getStr?
def decodeFrame (frame : Json) : Except String (List ClaimRec × List Inference) := do
  let mut claims := []
  let mut inferences := []
  for e in (← frame.getArr?).toList do
    match ← str e "ev" with
    | "claim" =>
      let model := (e.getObjVal? "model").toOption
      let family := (e.getObjVal? "family").toOption
      let scope ← match model, family with
        | some m, none => m.getStr? | none, some f => f.getStr? | _, _ => throw "claim needs exactly one model or family"
      claims := claims ++ [⟨← str e "id",model.isSome,scope,← str e "statement"⟩]
    | "inference" =>
      let slots ← (← (← e.getObjVal? "premises").getArr?).toList.mapM fun p => do
        match (p.getObjVal? "claim").toOption with
        | some c =>
          if (← (← p.getObjVal? "path").getArr?).size != 0 then throw "unsupported premise path"
          return Slot.filled (← c.getStr?)
        | none => return Slot.opened (← str p "required_kind") (← str p "at") (← str p "missing_why")
      inferences := inferences ++ [⟨← str e "id",slots,← str e "asserted"⟩]
    | "note" | "model" | "family" => pure ()
    | _ => throw "unknown frozen event"
  return (claims,inferences)

def filledIds (inf : Inference) : List String :=
  inf.slots.filterMap fun | .filled c => some c | _ => none

-- Select the inference each fixture names, and check its stated premises against the frozen slots.
def selectInput (caseId : String) (inputs frame : Json) : Except String Input := do
  let (claims,inferences) ← decodeFrame frame
  let find := fun (id : String) => match inferences.find? (·.id == id) with
    | some inf => Except.ok inf | none => Except.error "inference not in frozen fixture"
  if caseId == "GP-X399" then
    let inf ← find (← str (← inputs.getObjVal? "inference") "id")
    let stated ← (← (← (← inputs.getObjVal? "inference").getObjVal? "premises").getArr?).toList.mapM Json.getStr?
    if stated != filledIds inf then throw "stated premises differ from frozen slots"
    let claimId ← str (← inputs.getObjVal? "claim") "id"
    let family ← str (← inputs.getObjVal? "claim") "family"
    if !(claims.any fun r => r.id == claimId && !r.isModel && r.scope == family) then throw "stated family claim differs"
    return ⟨claims,inf⟩
  let attempt ← str inputs "attempt"
  let infId := (attempt.splitOn ":").headD ""
  let inf ← find infId
  let stated ← if caseId == "GP-X402" then pure [← str inputs "available_premise"]
    else (← (← inputs.getObjVal? "available_premises").getArr?).toList.mapM Json.getStr?
  if stated != filledIds inf then throw "stated premises differ from frozen slots"
  if (← str inputs "model") == "" then throw "missing model"
  return ⟨claims,inf⟩

-- Separate controls: the fixture's own clean inference, supplied bridges, or a dangling reference.
def control (i : Input) (inferences : List Inference) (mode : String) : Except String Input := do
  match mode with
  | "select_INF-X9" => match inferences.find? (·.id == "INF-X9") with
    | some inf => return {i with inference := inf} | none => throw "no INF-X9"
  | "fill_open_slots" =>
    let fills := i.inference.slots.filterMap fun | .opened _ a why => some (⟨s!"SUPPLIED:{why}",true,a,why⟩ : ClaimRec) | _ => none
    let slots := i.inference.slots.map fun | .opened _ _ why => .filled s!"SUPPLIED:{why}" | s => s
    return ⟨i.claims ++ fills,{i.inference with slots := slots}⟩
  | "family_bridge" => return {i with claims := i.claims.map fun r => {r with isModel := true}}
  | "dangling_reference" => return {i with inference := {i.inference with
      slots := i.inference.slots.map fun | .filled _ => .filled "UNKNOWN-CLAIM" | s => s}}
  | _ => return i

def run (text source mode frameText : String) : Except String Json := do
  let literal ← Decoder.parseUnique text
  Decoder.exactFields literal ["schema_version","id","seed","title","situation","inputs",
    "attempted_conclusion","expected","scope_or_region","sources"]
  if (← (← literal.getObjVal? "schema_version").getNat?) != 1 then throw "unsupported fixture schema"
  let caseId ← (← literal.getObjVal? "id").getStr?
  if !(["GP-X399","GP-X402","GP-X403"].contains caseId) then throw "uncommissioned fixture"
  let inputs ← literal.getObjVal? "inputs"
  let frame ← Json.parse frameText
  let i0 ← selectInput caseId inputs frame
  if !(["normal","reverse","duplicates","reverse_duplicates","select_INF-X9","fill_open_slots","family_bridge",
    "dangling_reference"].contains mode) then throw "unknown control mode"
  let i ← control i0 (← decodeFrame frame).2 mode
  let bound := literal.compress
  let frameLiteral := frame.compress
  let records := [inferenceW i source bound frameLiteral,custodyW i source bound frameLiteral]
  let mut events := records.flatMap fun w => [.current ⟨w.claim,w.version,w.binding⟩,.warrant w]
  if mode == "reverse" || mode == "reverse_duplicates" then events := events.reverse
  if mode == "duplicates" || mode == "reverse_duplicates" then events := events ++ events
  let state ← fold (admission i source bound frameLiteral) events
  return Json.mkObj [("case",toJson caseId),("source_digest",toJson source),("mode",toJson mode),
    ("literal_fixture",literal),("bound_literal",toJson bound),("frozen_frame",frame),
    ("inference",toJson i.inference.id),("asserted",toJson i.inference.asserted),
    ("slots",toJson (i.inference.slots.map fun
      | .filled c => Json.mkObj [("claim",toJson c),("model_level",toJson (modelClaim i.claims c))]
      | .opened k a why => Json.mkObj [("required_kind",toJson k),("at",toJson a),("missing_why",toJson why)])),
    ("actual_license_check",toJson (licensed i)),("state",stateJson state)]

#print axioms licensed_slots
#print axioms licensed_conclusion_sound
#print axioms actual_base_sound
#print axioms actual_validator_sound
#print axioms actual_fold_held_sound
#print axioms open_slot_blocks
#print axioms family_fact_is_not_model_fact
end OpenPremiseGuard

def main (args : List String) : IO UInt32 := do
  match args with
  | [path,digest,mode,frame] =>
    let result := OpenPremiseGuard.run (← IO.FS.readFile path) digest mode (← IO.FS.readFile frame)
    IO.println (match result with
      | .ok output => output.compress
      | .error e => (Lean.Json.mkObj [("status",Lean.toJson "MALFORMED"),("error",Lean.toJson e)]).compress)
    return 0
  | _ => return 2
