import GP50.Entry
import GP50.Presentation
import GP50.NarrowingAdmissionProofs
namespace ConditionalRoutes
open GP50 Lean
open GP50.Semantic

structure World (Point : Type) where
  tight : Point → Prop
  loose : Point → Prop
  side : Point → Prop
  firstProperty : Point → Prop
  secondProperty : Point → Prop
def Hypotheses {Point : Type} (w : World Point) : Prop :=
  (∀ x, w.loose x → w.firstProperty x) ∧
  (∀ x, w.side x → w.secondProperty x) ∧
  (∀ x, w.tight x → w.loose x) ∧
  (∀ x, w.tight x → w.side x)
inductive Region where | tight | loose | side | theory deriving DecidableEq
-- The two identically worded source premises retain distinct predicate identities.
inductive Formula where | firstProperty | secondProperty | licensedRoutes deriving DecidableEq
def mem {Point : Type} (ctx : World Point × Option Point) (region : Region) : Prop :=
  Hypotheses ctx.1 ∧ match region, ctx.2 with
    | .tight, some x => ctx.1.tight x
    | .loose, some x => ctx.1.loose x
    | .side, some x => ctx.1.side x
    | .theory, none => True
    | _, _ => False
def subset (a b : Region) : Bool :=
  decide (a = b) || decide (a = .tight ∧ (b = .loose ∨ b = .side))
theorem subset_sound (Point : Type) (a b : Region) (ctx : World Point × Option Point)
    (checked : subset a b = true) (present : mem ctx a) : mem ctx b := by
  simp only [subset, Bool.or_eq_true, decide_eq_true_eq] at checked
  rcases checked with same | ⟨same, alternatives⟩
  · exact same ▸ present
  · subst a
    rcases ctx with ⟨world, point⟩
    rcases present with ⟨hyp, here⟩
    cases point with
    | none => contradiction
    | some x =>
      rcases alternatives with same | same
      · subst b; exact ⟨hyp, hyp.2.2.1 x here⟩
      · subst b; exact ⟨hyp, hyp.2.2.2 x here⟩

def holds {Point : Type} (firstRoute secondRoute : Bool)
    (formula : Formula) (ctx : World Point × Option Point) : Prop :=
  match formula with
  | .firstProperty => match ctx.2 with | some x => ctx.1.firstProperty x | none => False
  | .secondProperty => match ctx.2 with | some x => ctx.1.secondProperty x | none => False
  | .licensedRoutes => firstRoute = true ∧ secondRoute = true ∧
      (∀ x, ctx.1.tight x → ctx.1.firstProperty x) ∧
      (∀ x, ctx.1.tight x → ctx.1.secondProperty x)
def profile (Point : Type) (firstRoute secondRoute : Bool) : Profile where
  Stmt := Formula
  Scope := Region
  Ctx := World Point × Option Point
  same := fun a b => decide (a = b)
  same_sound := fun _ _ h => of_decide_eq_true h
  mem := mem
  le := subset
  le_sound := subset_sound Point
  Holds := holds firstRoute secondRoute
  contra := fun _ _ => false
  contra_sound := by intro a b c impossible; contradiction

theorem first_given (Point : Type) (a b : Bool) :
    Means (profile Point a b) .firstProperty .loose := by
  rintro ⟨world, point⟩ ⟨hyp, here⟩
  cases point with
  | none => contradiction
  | some x => exact hyp.1 x here
theorem second_given (Point : Type) (a b : Bool) :
    Means (profile Point a b) .secondProperty .side := by
  rintro ⟨world, point⟩ ⟨hyp, here⟩
  cases point with
  | none => contradiction
  | some x => exact hyp.2.1 x here

theorem routes_composition_sound (Point : Type) (a b : Bool)
    (firstLicensed : a = true) (secondLicensed : b = true)
    (first : Means (profile Point a b) .firstProperty .tight)
    (second : Means (profile Point a b) .secondProperty .tight) :
    Means (profile Point a b) .licensedRoutes .theory := by
  rintro ⟨world, point⟩ ⟨hyp, _⟩
  exact ⟨firstLicensed, secondLicensed,
    fun x here => first (world,some x) ⟨hyp,here⟩,
    fun x here => second (world,some x) ⟨hyp,here⟩⟩

def statement : Formula → String
  | .firstProperty => "premise:first;a universal property;selected-predicate:first"
  | .secondProperty => "premise:second;a universal property;selected-predicate:second"
  | .licensedRoutes => "both premises have licensed routes to the tight context"
def scopeName : Region → String
  | .tight => "tight" | .loose => "loose" | .side => "side" | .theory => "conditional-route-licensing"
def binding (source : String) (formula : Formula) (scope : Region) : Binding :=
  ⟨statement formula,s!"{source}:{scopeName scope}",
    "contexts=[tight,loose,side];first:tight->loose:equations_forgotten;second:tight->side:equations_forgotten",
    [source],"test-only-named-route-assumptions",1,1⟩
def clause (Point : Type) (a b : Bool) (source : String) (key : Nat)
    (formula : Formula) (scope : Region) : Clause (profile Point a b) :=
  ⟨key,1,binding source formula scope,formula,scope⟩
def clauses (Point : Type) (a b : Bool) (source : String) : List (Clause (profile Point a b)) :=
  [clause Point a b source 1 .firstProperty .loose,
   clause Point a b source 2 .secondProperty .side,
   clause Point a b source 11 .firstProperty .tight,
   clause Point a b source 12 .secondProperty .tight,
   clause Point a b source 3 .licensedRoutes .theory]
def first (source : String) : Warrant :=
  ⟨10,1,1,binding source .firstProperty .loose,.receipt "given:loose:a universal property:first"⟩
def second (source : String) : Warrant :=
  ⟨20,2,1,binding source .secondProperty .side,.receipt "given:side:a universal property:second"⟩
def firstRestricted (source : String) : Warrant :=
  ⟨110,11,1,binding source .firstProperty .tight,.narrow 10⟩
def secondRestricted (source : String) : Warrant :=
  ⟨120,12,1,binding source .secondProperty .tight,.narrow 20⟩
def joint (source : String) (dependencies : List Nat := [110,120]) : Warrant :=
  ⟨30,3,1,binding source .licensedRoutes .theory,.derived dependencies "exact-named-route-join"⟩
def base (source : String) (a b : Bool) : Admission :=
  {Admission.refuseAll with
    receipt := fun w data =>
      decide (w = first source ∧ data = "given:loose:a universal property:first") ||
      decide (w = second source ∧ data = "given:side:a universal property:second")
    rule := fun w premises data => a && b &&
      decide (w = joint source ∧ premises = [firstRestricted source,secondRestricted source] ∧
        data = "exact-named-route-join")}
def admission (Point : Type) (source : String) (a b : Bool) : Admission :=
  withNarrowing (profile Point a b) (clauses Point a b source) (base source a b)

theorem admission_point_independent (Point : Type) (source : String) (a b : Bool) :
    admission Point source a b = admission Unit source a b := by
  -- Executables see only ProfileOps, which has no Ctx, so independence is definitional.
  rfl

theorem keys_unique (Point : Type) (a b : Bool) (source : String) :
    ((clauses Point a b source).map (·.key)).Nodup := by
  simp [clauses,clause]
theorem registered_meaning (Point : Type) (a b : Bool) (source : String)
    (c : Clause (profile Point a b)) (present : c ∈ clauses Point a b source)
    (meaning : Means (profile Point a b) c.stmt c.scope) :
    ClaimMeaning (profile Point a b) (clauses Point a b source) c.key := by
  refine ⟨⟨c,present,rfl⟩, ?_⟩
  intro other otherPresent sameKey
  have same := key_unique_of_nodup _ (fun c => c.key) (keys_unique Point a b source)
    other c otherPresent present sameKey
  exact same ▸ meaning

theorem actual_base_sound (Point : Type) (source : String) (a b : Bool)
    (snapshot : Snapshot) (unique : (snapshot.warrants.map (·.id)).Nodup) :
    BaseValidatorSound (profile Point a b) (clauses Point a b source) (base source a b) snapshot := by
  constructor
  · intro w present data accepted
    simp only [base, Bool.or_eq_true, decide_eq_true_eq] at accepted
    rcases accepted with ⟨same,_⟩ | ⟨same,_⟩
    · subst w
      exact ⟨first source,present,rfl, registered_meaning Point a b source
        (clause Point a b source 1 .firstProperty .loose) (by simp [clauses])
        (first_given Point a b)⟩
    · subst w
      exact ⟨second source,present,rfl, registered_meaning Point a b source
        (clause Point a b source 2 .secondProperty .side) (by simp [clauses])
        (second_given Point a b)⟩
  · intro w present data accepted; contradiction
  · intro w present premises data accepted members truePremises
    simp only [base, Bool.and_eq_true, decide_eq_true_eq] at accepted
    rcases accepted with ⟨⟨licensedFirst,licensedSecond⟩,same,samePremises,_⟩
    subst w; subst premises
    have fp := members (firstRestricted source) (by simp)
    have sp := members (secondRestricted source) (by simp)
    have ft := warrant_meaning_claim (profile Point a b) (clauses Point a b source)
      snapshot unique _ fp (truePremises _ (by simp))
    have st := warrant_meaning_claim (profile Point a b) (clauses Point a b source)
      snapshot unique _ sp (truePremises _ (by simp))
    have fm := ft.2 (clause Point a b source 11 .firstProperty .tight) (by simp [clauses]) rfl
    have sm := st.2 (clause Point a b source 12 .secondProperty .tight) (by simp [clauses]) rfl
    exact ⟨joint source,present,rfl,registered_meaning Point a b source
      (clause Point a b source 3 .licensedRoutes .theory) (by simp [clauses])
      (routes_composition_sound Point a b licensedFirst licensedSecond fm sm)⟩

theorem actual_validator_sound (Point : Type) (source : String) (a b : Bool)
    (snapshot : Snapshot) (unique : (snapshot.warrants.map (·.id)).Nodup) :
    ValidatorSound (admission Point source a b) snapshot
      (WarrantMeaning (profile Point a b) (clauses Point a b source) snapshot) :=
  withNarrowing_validator_sound _ _ _ snapshot unique (actual_base_sound Point source a b snapshot unique)
theorem actual_fold_held_sound (Point : Type) (source : String) (a b : Bool)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission Point source a b) events = .ok state)
    (heldClaim : held state claim = true) :
    ClaimMeaning (profile Point a b) (clauses Point a b source) claim := by
  unfold fold at folded
  cases resolved : resolve events with
  | error e => simp [resolved] at folded
  | ok snapshot =>
    rw [resolved] at folded
    have same := Except.ok.inj folded
    subst state
    exact evaluate_held_meaning _ _ _ snapshot (resolve_warrant_ids_nodup events snapshot resolved)
      (actual_base_sound Point source a b snapshot (resolve_warrant_ids_nodup events snapshot resolved))
      claim heldClaim

-- The executable uses Unit; this corollary transfers that exact fold to every Point type.
theorem native_fold_held_sound (Point : Type) (source : String) (a b : Bool)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission Unit source a b) events = .ok state)
    (heldClaim : held state claim = true) :
    ClaimMeaning (profile Point a b) (clauses Point a b source) claim := by
  apply actual_fold_held_sound Point source a b events state claim _ heldClaim
  rw [admission_point_independent Point source a b]
  exact folded

-- Unlike universal truth on an empty region, route licensing is globally required.
example (Point : Type) (source : String)
    (meaning : ClaimMeaning (profile Point true false) (clauses Point true false source) 3) : False := by
  have m := meaning.2 (clause Point true false source 3 .licensedRoutes .theory) (by simp [clauses]) rfl
  let world : World Point := ⟨fun _ => False,fun _ => False,fun _ => False,fun _ => True,fun _ => True⟩
  have hypotheses : Hypotheses world := by
    simp [Hypotheses,world]
  have bad := m (world,none) ⟨hypotheses,trivial⟩
  exact Bool.noConfusion bad.2.1

def bindingJson (b : Binding) : Json := Json.mkObj [
  ("statementHash",toJson b.statementHash),("scopeHash",toJson b.scopeHash),
  ("modelHash",toJson b.modelHash),("inputHashes",toJson b.inputHashes),
  ("authority",toJson b.authority),("authorityVersion",toJson b.authorityVersion),
  ("kernelVersion",toJson b.kernelVersion)]
def warrantJson (w : Warrant) : Json :=
  let evidence := match w.evidence with
    | .receipt data => Json.mkObj [("kind",toJson "receipt"),("data",toJson data)]
    | .narrow dependency => Json.mkObj [("kind",toJson "narrow"),("premise",toJson dependency)]
    | .derived deps side => Json.mkObj [("kind",toJson "derived"),("premises",toJson deps),("sideReceipt",toJson side)]
    | _ => Json.mkObj [("kind",toJson "unregistered")]
  Json.mkObj [("id",toJson w.id),("claim",toJson w.claim),("version",toJson w.version),
    ("binding",bindingJson w.binding),("evidence",evidence)]
def snapshotJson (s : Snapshot) : Json := Json.mkObj [
  ("domain",toJson s.domain),("warrants",toJson (s.warrants.map warrantJson)),
  ("currents",toJson (s.currents.map fun c => Json.mkObj [
    ("claim",toJson c.claim),("version",toJson c.version),("binding",bindingJson c.binding)])),
  ("retracted",toJson s.retracted),("successors",toJson s.successors)]
def strings (j : Json) : Except String (List String) := do
  let values ← j.getArr?
  values.toList.mapM Json.getStr?
def readRoute (route : Json) (expected : String) : Except String Bool := do
  let steps ← route.getArr?
  if steps.isEmpty then return false
  if steps.size != 1 then throw "unsupported route length"
  let step := steps[0]!
  Decoder.exactFields step ["relation","direction"]
  let relation ← (← step.getObjVal? "relation").getStr?
  let direction ← (← step.getObjVal? "direction").getStr?
  if relation != "first" && relation != "second" then throw "unknown selected relation"
  if direction != "reverse" && direction != "forward" then throw "unknown direction"
  return relation == expected && direction == "reverse"
def run (text digest mode : String) : Except String Json := do
  let json ← Decoder.parseUnique text
  Decoder.exactFields json ["schema_version","id","seed","title","situation","inputs",
    "attempted_conclusion","expected","scope_or_region","sources"]
  if (← (← json.getObjVal? "schema_version").getNat?) != 1 then throw "unsupported fixture schema"
  let caseId ← (← json.getObjVal? "id").getStr?
  if caseId != "GP-X177" && caseId != "GP-X178" then throw "uncommissioned case"
  let inputs ← json.getObjVal? "inputs"
  Decoder.exactFields inputs ["contexts","relations","premises","conclusion_class","conclusion_text"]
  if (← strings (← inputs.getObjVal? "contexts")) != ["tight","loose","side"] then throw "wrong selected contexts"
  if (← (← inputs.getObjVal? "conclusion_class").getStr?) != "universal_property" ||
      (← (← inputs.getObjVal? "conclusion_text").getStr?) != statement .licensedRoutes then
    throw "wrong literal conclusion"
  let relations ← (← inputs.getObjVal? "relations").getArr?
  if relations.size != 2 then throw "missing relation"
  for index in [0,1] do
    let relation := relations[index]!
    Decoder.exactFields relation ["name","source","target","relation"]
    if (← (← relation.getObjVal? "name").getStr?) != (if index == 0 then "first" else "second") ||
        (← (← relation.getObjVal? "source").getStr?) != "tight" ||
        (← (← relation.getObjVal? "target").getStr?) != (if index == 0 then "loose" else "side") ||
        (← (← relation.getObjVal? "relation").getStr?) != "equations_forgotten" then
      throw "wrong named relation/model"
  let premises ← (← inputs.getObjVal? "premises").getArr?
  if premises.size != 2 then throw "missing supplied premise"
  let mut licensed : List Bool := []
  for index in [0,1] do
    let premise := premises[index]!
    Decoder.exactFields premise ["context","statement_class","statement","route"]
    if (← (← premise.getObjVal? "context").getStr?) != (if index == 0 then "loose" else "side") ||
        (← (← premise.getObjVal? "statement_class").getStr?) != "universal_property" ||
        (← (← premise.getObjVal? "statement").getStr?) != "a universal property" then
      throw "wrong selected premise/statement"
    licensed := licensed ++ [← readRoute (← premise.getObjVal? "route") (if index == 0 then "first" else "second")]
  let a := licensed[0]!
  let b := licensed[1]!
  let mut roots := [first digest,second digest]
  let mut restricted := (if a then [firstRestricted digest] else []) ++
    (if b then [secondRestricted digest] else [])
  let dependencies := [if a then 110 else 10,if b then 120 else 20]
  if mode == "withheld_second" then roots := roots.filter (·.id != 20)
  if mode == "wrong_binding" then restricted := restricted.map fun w =>
    if w.id == 110 then {w with binding := {w.binding with inputHashes := ["changed"]}} else w
  if mode == "wrong_selected_predicate" then restricted := restricted.map fun w =>
    if w.id == 110 then {w with binding := {w.binding with statementHash := statement .secondProperty}} else w
  if mode == "wrong_dependency" then restricted := restricted.map fun w =>
    if w.id == 110 then {w with evidence := .narrow 20} else w
  if mode == "wrong_model" then restricted := restricted.map fun w =>
    if w.id == 120 then {w with binding := {w.binding with modelHash := "other selected model"}} else w
  if !(["normal","reverse","duplicates","withheld_second","wrong_binding","wrong_selected_predicate",
        "wrong_dependency","wrong_model"].contains mode) then throw "unknown control mode"
  let records := roots ++ restricted ++ [joint digest dependencies]
  let mut events := records.flatMap fun w => [.current ⟨w.claim,1,w.binding⟩,.warrant w]
  if mode == "reverse" then events := events.reverse
  if mode == "duplicates" then events := events ++ events
  let state ← fold (admission Unit digest a b) events
  return Json.mkObj [("conditional",toJson true),("case",toJson caseId),("source_digest",toJson digest),
    ("mode",toJson mode),("literal_inputs",inputs),("conclusion",toJson (statement .licensedRoutes)),
    ("route_licensed",toJson licensed),("route_endpoints",toJson [if a then "tight" else "loose",if b then "tight" else "side"]),
    ("argument_dependency_ids",toJson dependencies),
    ("state",stateJson state),("snapshot",snapshotJson state.snapshot),
    ("named_hypotheses",toJson ["loose: a universal property (first selected predicate)",
      "side: a universal property (second selected predicate)",
      "first: tight subset loose (equations_forgotten)",
      "second: tight subset side (equations_forgotten)"]),
    ("narrow_checker",toJson "GP50.Semantic.acceptsNarrow")]
#print axioms subset_sound
#print axioms routes_composition_sound
#print axioms actual_validator_sound
#print axioms actual_fold_held_sound
#print axioms native_fold_held_sound
end ConditionalRoutes

def main (args : List String) : IO UInt32 := do
  match args with
  | [path,digest,mode] =>
    let result := ConditionalRoutes.run (← IO.FS.readFile path) digest mode
    IO.println (match result with
      | .ok output => output.compress
      | .error e => (Lean.Json.mkObj [("status",Lean.toJson "MALFORMED"),("error",Lean.toJson e)]).compress)
    return 0
  | _ => return 2
