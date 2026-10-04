import GP50.Entry
import GP50.Presentation
import GP50.SpanSoundnessProofs
namespace RecordedUseCoverage
open GP50 Lean

inductive Axis where | place | order deriving DecidableEq, BEq, Repr
def axisName : Axis → String | .place => "place" | .order => "order"
structure UseRow where
  dimension : Axis
  indices : List String
  description : String
structure Inventory where
  asserted : List Axis
  place : List String
  order : List String
  construction : List UseRow
  conclusion : List UseRow

def represented (inv : Inventory) : Axis → List String
  | .place => inv.place | .order => inv.order
def required (inv : Inventory) (axis : Axis) : List String :=
  ((inv.construction ++ inv.conclusion).filter fun row => decide (row.dimension = axis)).flatMap (·.indices)
def Covered (inv : Inventory) (axis : Axis) : Prop :=
  ∀ label ∈ required inv axis, label ∈ represented inv axis
def AllCovered (inv : Inventory) : Prop := ∀ axis ∈ inv.asserted, Covered inv axis
def checker (inv : Inventory) (axis : Axis) : Bool :=
  (required inv axis).all fun label => decide (label ∈ represented inv axis)
def missing (inv : Inventory) (axis : Axis) : List String :=
  (required inv axis).filter fun label => decide (label ∉ represented inv axis)
def canonical (labels : List String) : List String :=
  labels.eraseDups.mergeSort (fun a b => a ≤ b)

theorem checker_iff (inv : Inventory) (axis : Axis) :
    checker inv axis = true ↔ Covered inv axis := by
  simp [checker,Covered,List.all_eq_true]
theorem missing_iff (inv : Inventory) (axis : Axis) (label : String) :
    label ∈ missing inv axis ↔ label ∈ required inv axis ∧ label ∉ represented inv axis := by
  simp [missing,List.mem_filter]
theorem empty_recorded_uses_covered (inv : Inventory)
    (noConstruction : inv.construction = []) (noConclusion : inv.conclusion = []) : AllCovered inv := by
  intro axis _
  simp [Covered,required,noConstruction,noConclusion]

def binding (source literal : String) (statement : String) : Binding :=
  ⟨statement,"finite-recorded-use-coverage",literal,[source,literal,statement],
    "test-only-exact-recorded-inventory-containment",1,1⟩
def placeW (source literal : String) : Warrant :=
  ⟨10,1,1,binding source literal "recorded coverage:dimension=place",.receipt "recorded-coverage:place"⟩
def orderW (source literal : String) : Warrant :=
  ⟨20,2,1,binding source literal "recorded coverage:dimension=order",.receipt "recorded-coverage:order"⟩
def joint (source literal : String) : Warrant :=
  ⟨30,3,1,binding source literal "all asserted dimensions cover every recorded construction and conclusion use",
    .derived [10,20] "both-recorded-dimensions"⟩
def custody (source literal : String) : Warrant :=
  ⟨100,100,1,binding source literal "complete literal fixture custody",.citation literal⟩

def admission (inv : Inventory) (source literal : String) : Admission :=
  {Admission.refuseAll with
    receipt := fun w data =>
      (decide (w = placeW source literal ∧ data = "recorded-coverage:place") && checker inv .place) ||
      (decide (w = orderW source literal ∧ data = "recorded-coverage:order") && checker inv .order)
    rule := fun w premises data =>
      decide (w = joint source literal ∧ premises = [placeW source literal,orderW source literal] ∧
        data = "both-recorded-dimensions")}

def ClaimTruth (inv : Inventory) (claim : Nat) : Prop :=
  match claim with | 1 => Covered inv .place | 2 => Covered inv .order | 3 => AllCovered inv | _ => False
def WarrantTruth (inv : Inventory) (snapshot : Snapshot) (id : Nat) : Prop :=
  ∃ w ∈ snapshot.warrants, w.id = id ∧ ClaimTruth inv w.claim

theorem warrant_truth_claim (inv : Inventory) (snapshot : Snapshot)
    (unique : (snapshot.warrants.map (·.id)).Nodup) (w : Warrant) (present : w ∈ snapshot.warrants)
    (truth : WarrantTruth inv snapshot w.id) : ClaimTruth inv w.claim := by
  rcases truth with ⟨other,otherPresent,sameId,truth⟩
  have same := key_unique_of_nodup snapshot.warrants (fun w => w.id)
    unique other w otherPresent present sameId
  exact same ▸ truth

theorem actual_validator_sound (inv : Inventory) (source literal : String)
    (snapshot : Snapshot) (unique : (snapshot.warrants.map (·.id)).Nodup) :
    ValidatorSound (admission inv source literal) snapshot (WarrantTruth inv snapshot) := by
  constructor
  · intro w present data accepted
    simp only [admission,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at accepted
    rcases accepted with ⟨⟨same,_⟩,checked⟩ | ⟨⟨same,_⟩,checked⟩
    · subst w
      exact ⟨placeW source literal,present,rfl,(checker_iff inv .place).mp checked⟩
    · subst w
      exact ⟨orderW source literal,present,rfl,(checker_iff inv .order).mp checked⟩
  · intro w present data accepted; contradiction
  · intro w present premises data accepted members truePremises
    simp only [admission,decide_eq_true_eq] at accepted
    rcases accepted with ⟨same,samePremises,_⟩
    subst w; subst premises
    have pc := warrant_truth_claim inv snapshot unique (placeW source literal)
      (members _ (by simp)) (truePremises _ (by simp))
    have oc := warrant_truth_claim inv snapshot unique (orderW source literal)
      (members _ (by simp)) (truePremises _ (by simp))
    refine ⟨joint source literal,present,rfl,?_⟩
    change AllCovered inv
    intro axis _
    cases axis with
    | place => exact pc
    | order => exact oc
  · intro w present premise premisePresent accepted truth; contradiction

theorem actual_fold_held_sound (inv : Inventory) (source literal : String)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission inv source literal) events = .ok state)
    (heldClaim : held state claim = true) : ClaimTruth inv claim := by
  unfold fold at folded
  cases resolved : resolve events with
  | error e => simp [resolved] at folded
  | ok snapshot =>
    rw [resolved] at folded
    have same := Except.ok.inj folded
    subst state
    have unique := resolve_warrant_ids_nodup events snapshot resolved
    exact evaluate_held_truth_composition (admission inv source literal) snapshot
      (WarrantTruth inv snapshot) (ClaimTruth inv)
      (actual_validator_sound inv source literal snapshot unique)
      (warrant_truth_claim inv snapshot unique) claim heldClaim

theorem actual_join_means_all_recorded_uses (inv : Inventory) (source literal : String)
    (events : List Event) (state : RuntimeState)
    (folded : fold (admission inv source literal) events = .ok state)
    (joined : held state 3 = true) : AllCovered inv :=
  actual_fold_held_sound inv source literal events state 3 folded joined

def strings (json : Json) : Except String (List String) := do
  let values ← json.getArr?
  values.toList.mapM fun value => do
    let text ← value.getStr?
    if text.isEmpty then throw "empty literal label"
    return text
def readAxis (name : String) : Except String Axis :=
  match name with | "place" => .ok .place | "order" => .ok .order | _ => .error "unknown dimension identity"
def rows (json : Json) : Except String (List UseRow) := do
  (← json.getArr?).toList.mapM fun row => do
    Decoder.exactFields row ["dimension","indices","description"]
    let axis ← readAxis (← (← row.getObjVal? "dimension").getStr?)
    let labels ← strings (← row.getObjVal? "indices")
    let description ← (← row.getObjVal? "description").getStr?
    return ⟨axis,labels,description⟩
def decodeInventory (inputs : Json) : Except String Inventory := do
  Decoder.exactFields inputs ["scenario","asserted_dimensions","represented_indices","construction_uses","conclusion_uses"]
  if (← (← inputs.getObjVal? "scenario").getStr?) != "coverage_inventory" then throw "wrong structural scenario"
  let axes ← strings (← inputs.getObjVal? "asserted_dimensions")
  if axes != ["place","order"] then throw "wrong asserted dimension identities"
  let declared ← inputs.getObjVal? "represented_indices"
  Decoder.exactFields declared ["place","order"]
  return ⟨← axes.mapM readAxis,← strings (← declared.getObjVal? "place"),
    ← strings (← declared.getObjVal? "order"),← rows (← inputs.getObjVal? "construction_uses"),
    ← rows (← inputs.getObjVal? "conclusion_uses")⟩

def bindingJson (b : Binding) : Json := Json.mkObj [
  ("statementHash",toJson b.statementHash),("scopeHash",toJson b.scopeHash),("modelHash",toJson b.modelHash),
  ("inputHashes",toJson b.inputHashes),("authority",toJson b.authority),
  ("authorityVersion",toJson b.authorityVersion),("kernelVersion",toJson b.kernelVersion)]
def warrantJson (w : Warrant) : Json :=
  let evidence := match w.evidence with
    | .receipt data => Json.mkObj [("kind",toJson "receipt"),("data",toJson data)]
    | .derived deps side => Json.mkObj [("kind",toJson "derived"),("premises",toJson deps),("sideReceipt",toJson side)]
    | .citation text => Json.mkObj [("kind",toJson "citation"),("text",toJson text)]
    | _ => Json.mkObj [("kind",toJson "unregistered")]
  Json.mkObj [("id",toJson w.id),("claim",toJson w.claim),("version",toJson w.version),
    ("binding",bindingJson w.binding),("evidence",evidence)]
def snapshotJson (s : Snapshot) : Json := Json.mkObj [
  ("domain",toJson s.domain),("warrants",toJson (s.warrants.map warrantJson)),
  ("currents",toJson (s.currents.map fun c => Json.mkObj [
    ("claim",toJson c.claim),("version",toJson c.version),("binding",bindingJson c.binding)])),
  ("retracted",toJson s.retracted),("successors",toJson s.successors)]

def run (text digest mode : String) : Except String Json := do
  let literal ← Decoder.parseUnique text
  Decoder.exactFields literal ["schema_version","id","seed","title","situation","inputs",
    "attempted_conclusion","expected","scope_or_region","sources"]
  if (← (← literal.getObjVal? "schema_version").getNat?) != 1 then throw "unsupported fixture schema"
  let caseId ← (← literal.getObjVal? "id").getStr?
  if !(["GP-X193","GP-X194","GP-X195","GP-X196","GP-X197","GP-X198"].contains caseId) then throw "uncommissioned fixture"
  if (← (← literal.getObjVal? "attempted_conclusion").getStr?) !=
      "The recorded uses are covered by the declared index inventory on all asserted dimensions." then throw "wrong structural conclusion"
  let inputs ← literal.getObjVal? "inputs"
  let inv ← decodeInventory inputs
  let bound := literal.compress
  if !(["normal","reverse","duplicates","reverse_duplicates","dimension_collision","withheld_order","wrong_binding"].contains mode)
      then throw "unknown control mode"
  let p := placeW digest bound
  let mut o := orderW digest bound
  if mode == "dimension_collision" then o := {o with id := 10}
  if mode == "wrong_binding" then o := {o with binding := {o.binding with inputHashes := ["corrupt binding"]}}
  let records := [p] ++ (if mode == "withheld_order" then [] else [o]) ++ [joint digest bound,custody digest bound]
  let mut events := records.flatMap fun w => [.current ⟨w.claim,w.version,w.binding⟩,.warrant w]
  if mode == "reverse" || mode == "reverse_duplicates" then events := events.reverse
  if mode == "duplicates" || mode == "reverse_duplicates" then events := events ++ events
  let state ← fold (admission inv digest bound) events
  return Json.mkObj [("case",toJson caseId),("source_digest",toJson digest),("mode",toJson mode),
    ("literal_fixture",literal),("literal_inputs",inputs),("bound_literal",toJson bound),
    ("required_by_dimension",Json.mkObj [("place",toJson (canonical (required inv .place))),("order",toJson (canonical (required inv .order)))]),
    ("missing_by_dimension",Json.mkObj [("place",toJson (canonical (missing inv .place))),("order",toJson (canonical (missing inv .order)))]),
    ("checker_coverage",Json.mkObj [("place",toJson (checker inv .place)),("order",toJson (checker inv .order))]),
    ("joint_dependencies",toJson ([10,20] : List Nat)),("state",stateJson state),("snapshot",snapshotJson state.snapshot)]
#print axioms checker_iff
#print axioms missing_iff
#print axioms empty_recorded_uses_covered
#print axioms actual_validator_sound
#print axioms actual_fold_held_sound
#print axioms actual_join_means_all_recorded_uses
end RecordedUseCoverage

def main (args : List String) : IO UInt32 := do
  match args with
  | [path,digest,mode] =>
    let result := RecordedUseCoverage.run (← IO.FS.readFile path) digest mode
    IO.println (match result with
      | .ok output => output.compress
      | .error e => (Lean.Json.mkObj [("status",Lean.toJson "MALFORMED"),("error",Lean.toJson e)]).compress)
    return 0
  | _ => return 2
