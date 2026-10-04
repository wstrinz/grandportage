import GP50.Entry
import GP50.Presentation
import GP50.NarrowingAdmissionProofs
set_option linter.unusedSimpArgs false
namespace ConditionalPointRoutes
open GP50 Lean GP50.Semantic

structure World (Point : Type) where
  tight : Point → Prop
  loose : Point → Prop
  side : Point → Prop
  universalProperty : Point → Prop
  exhibited : Point

structure Hypotheses {Point : Type} (world : World Point) (extra : Bool) : Prop where
  universal : ∀ x, world.loose x → world.universalProperty x
  sideWitness : world.side world.exhibited
  firstInclusion : ∀ x, world.tight x → world.loose x
  secondInclusion : ∀ x, world.tight x → world.side x
  justifiedTight : extra = true → world.tight world.exhibited

inductive Region where | tight | loose | side | theory deriving DecidableEq
inductive Formula where | universalProperty | sidePoint | tightPoint | licensedRoutes deriving DecidableEq

def mem {Point : Type} (extra : Bool) (ctx : World Point × Option Point) (region : Region) : Prop :=
  Hypotheses ctx.1 extra ∧ match region,ctx.2 with
    | .tight,some x => ctx.1.tight x
    | .loose,some x => ctx.1.loose x
    | .side,some x => ctx.1.side x
    | .theory,none => True
    | _,_ => False

def subset (a b : Region) : Bool :=
  decide (a = b) || decide (a = .tight ∧ (b = .loose ∨ b = .side))

theorem subset_sound (Point : Type) (extra : Bool) (a b : Region) (ctx : World Point × Option Point)
    (checked : subset a b = true) (present : mem extra ctx a) : mem extra ctx b := by
  simp only [subset,Bool.or_eq_true,decide_eq_true_eq] at checked
  rcases checked with same | ⟨same,alternatives⟩
  · exact same ▸ present
  · subst a
    rcases ctx with ⟨world,point⟩
    rcases present with ⟨hyp,here⟩
    cases point with
    | none => contradiction
    | some x =>
      rcases alternatives with same | same
      · subst b; exact ⟨hyp,hyp.firstInclusion x here⟩
      · subst b; exact ⟨hyp,hyp.secondInclusion x here⟩

def holds {Point : Type} (formula : Formula) (ctx : World Point × Option Point) : Prop :=
  match formula with
  | .universalProperty => match ctx.2 with | some x => ctx.1.universalProperty x | none => False
  | .sidePoint => ∃ x, x = ctx.1.exhibited ∧ ctx.1.side x
  | .tightPoint => ∃ x, x = ctx.1.exhibited ∧ ctx.1.tight x
  | .licensedRoutes => (∀ x, ctx.1.tight x → ctx.1.universalProperty x) ∧
      (∃ x, x = ctx.1.exhibited ∧ ctx.1.tight x)

def profile (Point : Type) (extra : Bool) : Profile where
  Stmt := Formula
  Scope := Region
  Ctx := World Point × Option Point
  same := fun a b => decide (a = b)
  same_sound := fun _ _ h => of_decide_eq_true h
  mem := mem extra
  le := subset
  le_sound := subset_sound Point extra
  Holds := holds
  contra := fun _ _ => false
  contra_sound := by intro a b c impossible; contradiction

theorem universal_given (Point : Type) (extra : Bool) :
    Means (profile Point extra) .universalProperty .loose := by
  rintro ⟨world,point⟩ ⟨hyp,here⟩
  cases point with
  | none => contradiction
  | some x => exact hyp.universal x here

theorem side_point_given (Point : Type) (extra : Bool) :
    Means (profile Point extra) .sidePoint .theory := by
  rintro ⟨world,point⟩ ⟨hyp,_⟩
  exact ⟨world.exhibited,rfl,hyp.sideWitness⟩

theorem tight_point_given (Point : Type) (extra : Bool) (justified : extra = true) :
    Means (profile Point extra) .tightPoint .theory := by
  rintro ⟨world,point⟩ ⟨hyp,_⟩
  exact ⟨world.exhibited,rfl,hyp.justifiedTight justified⟩

theorem routes_composition_sound (Point : Type) (extra : Bool)
    (universal : Means (profile Point extra) .universalProperty .tight)
    (point : Means (profile Point extra) .tightPoint .theory) :
    Means (profile Point extra) .licensedRoutes .theory := by
  rintro ⟨world,whereAt⟩ ⟨hyp,_⟩
  exact ⟨fun x here => universal (world,some x) ⟨hyp,here⟩,
    point (world,none) ⟨hyp,trivial⟩⟩

def statement : Formula → String
  | .universalProperty => "universal_property;a universal property;selected-predicate:universal-premise"
  | .sidePoint => "exhibited_point;a point in the relaxed side model;selected-model:side;selected-witness:side-premise"
  | .tightPoint => "exhibited_point;same supplied exhibited point;selected-model:tight;selected-witness:side-premise"
  | .licensedRoutes => "both premises have licensed routes to the tight context"

def scopeName : Region → String
  | .tight => "tight" | .loose => "loose" | .side => "side" | .theory => "global-conditional-theory"

def binding (source : String) (formula : Formula) (scope : Region) : Binding :=
  ⟨statement formula,s!"{source}:{scopeName scope}",
    "contexts=[tight,loose,side];first:tight->loose:equations_forgotten;second:tight->side:equations_forgotten;selected-witness=side-premise",
    [source],"test-only-supplied-universal-and-exhibited-point",1,1⟩

def clause (Point : Type) (extra : Bool) (source : String) (key : Nat)
    (formula : Formula) (scope : Region) : Clause (profile Point extra) :=
  ⟨key,1,binding source formula scope,formula,scope⟩

def clauses (Point : Type) (extra : Bool) (source : String) : List (Clause (profile Point extra)) :=
  [clause Point extra source 1 .universalProperty .loose,
   clause Point extra source 2 .sidePoint .theory,
   clause Point extra source 11 .universalProperty .tight,
   clause Point extra source 12 .tightPoint .theory,
   clause Point extra source 3 .licensedRoutes .theory]

def first (source : String) : Warrant :=
  ⟨10,1,1,binding source .universalProperty .loose,.receipt "given:loose:universal-property"⟩
def second (source : String) : Warrant :=
  ⟨20,2,1,binding source .sidePoint .theory,.receipt "given:side:exhibited-point"⟩
def firstRestricted (source : String) : Warrant :=
  ⟨110,11,1,binding source .universalProperty .tight,.narrow 10⟩
def pointAttempt (source : String) : Warrant :=
  ⟨120,12,1,binding source .tightPoint .theory,.narrow 20⟩
def pointJustified (source : String) : Warrant :=
  ⟨120,12,1,binding source .tightPoint .theory,.receipt "additional:justified-tight-membership-of-same-witness"⟩
def routedPoint (source : String) (extra : Bool) : Warrant :=
  if extra then pointJustified source else pointAttempt source
def dependencies (pointFirst : Bool) : List Nat :=
  if pointFirst then [120,110] else [110,120]
def premiseRecords (source : String) (pointFirst extra : Bool) : List Warrant :=
  if pointFirst then [routedPoint source extra,firstRestricted source]
  else [firstRestricted source,routedPoint source extra]
def joint (source : String) (pointFirst : Bool) : Warrant :=
  ⟨30,3,1,binding source .licensedRoutes .theory,.derived (dependencies pointFirst) "join:universal-and-same-exhibited-point"⟩

def base (source : String) (pointFirst extra : Bool) : Admission :=
  {Admission.refuseAll with
    receipt := fun w data =>
      decide (w = first source ∧ data = "given:loose:universal-property") ||
      decide (w = second source ∧ data = "given:side:exhibited-point") ||
      (extra && decide (w = pointJustified source ∧ data = "additional:justified-tight-membership-of-same-witness"))
    rule := fun w premises data =>
      decide (w = joint source pointFirst ∧ premises = premiseRecords source pointFirst extra ∧
        data = "join:universal-and-same-exhibited-point")}

def admission (Point : Type) (source : String) (pointFirst extra : Bool) : Admission :=
  withNarrowing (profile Point extra) (clauses Point extra source) (base source pointFirst extra)

theorem admission_point_independent (Point : Type) (source : String) (pointFirst extra : Bool) :
    admission Point source pointFirst extra = admission Unit source pointFirst extra := by
  -- Executables see only ProfileOps, which has no Ctx, so independence is definitional.
  rfl

theorem keys_unique (Point : Type) (extra : Bool) (source : String) :
    ((clauses Point extra source).map (·.key)).Nodup := by simp [clauses,clause]

theorem registered_meaning (Point : Type) (extra : Bool) (source : String)
    (c : Clause (profile Point extra)) (present : c ∈ clauses Point extra source)
    (meaning : Means (profile Point extra) c.stmt c.scope) :
    ClaimMeaning (profile Point extra) (clauses Point extra source) c.key := by
  refine ⟨⟨c,present,rfl⟩,?_⟩
  intro other otherPresent sameKey
  have same := key_unique_of_nodup _ (fun c => c.key) (keys_unique Point extra source)
    other c otherPresent present sameKey
  exact same ▸ meaning

theorem actual_base_sound (Point : Type) (source : String) (pointFirst extra : Bool)
    (snapshot : Snapshot) (unique : (snapshot.warrants.map (·.id)).Nodup) :
    BaseValidatorSound (profile Point extra) (clauses Point extra source) (base source pointFirst extra) snapshot := by
  constructor
  · intro w present data accepted
    simp only [base,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at accepted
    rcases accepted with (⟨same,_⟩ | ⟨same,_⟩) | ⟨justified,same,_⟩
    · subst w
      exact ⟨first source,present,rfl,registered_meaning Point extra source
        (clause Point extra source 1 .universalProperty .loose) (by simp [clauses])
        (universal_given Point extra)⟩
    · subst w
      exact ⟨second source,present,rfl,registered_meaning Point extra source
        (clause Point extra source 2 .sidePoint .theory) (by simp [clauses])
        (side_point_given Point extra)⟩
    · subst w
      exact ⟨pointJustified source,present,rfl,registered_meaning Point extra source
        (clause Point extra source 12 .tightPoint .theory) (by simp [clauses])
        (tight_point_given Point extra justified)⟩
  · intro w present data accepted; contradiction
  · intro w present premises data accepted members truePremises
    simp only [base,decide_eq_true_eq] at accepted
    rcases accepted with ⟨same,samePremises,_⟩
    subst w; subst premises
    have fmemb : firstRestricted source ∈ premiseRecords source pointFirst extra := by
      cases pointFirst <;> simp [premiseRecords]
    have pmemb : routedPoint source extra ∈ premiseRecords source pointFirst extra := by
      cases pointFirst <;> simp [premiseRecords]
    have ft := warrant_meaning_claim (profile Point extra) (clauses Point extra source)
      snapshot unique _ (members _ fmemb) (truePremises _ fmemb)
    have pt := warrant_meaning_claim (profile Point extra) (clauses Point extra source)
      snapshot unique _ (members _ pmemb) (truePremises _ pmemb)
    have fm := ft.2 (clause Point extra source 11 .universalProperty .tight) (by simp [clauses]) rfl
    have pointKey : (routedPoint source extra).claim = 12 := by cases extra <;> rfl
    have pm := pt.2 (clause Point extra source 12 .tightPoint .theory) (by simp [clauses]) pointKey.symm
    exact ⟨joint source pointFirst,present,rfl,registered_meaning Point extra source
      (clause Point extra source 3 .licensedRoutes .theory) (by simp [clauses])
      (routes_composition_sound Point extra fm pm)⟩

theorem actual_validator_sound (Point : Type) (source : String) (pointFirst extra : Bool)
    (snapshot : Snapshot) (unique : (snapshot.warrants.map (·.id)).Nodup) :
    ValidatorSound (admission Point source pointFirst extra) snapshot
      (WarrantMeaning (profile Point extra) (clauses Point extra source) snapshot) :=
  withNarrowing_validator_sound _ _ _ snapshot unique (actual_base_sound Point source pointFirst extra snapshot unique)

theorem actual_fold_held_sound (Point : Type) (source : String) (pointFirst extra : Bool)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission Point source pointFirst extra) events = .ok state)
    (heldClaim : held state claim = true) :
    ClaimMeaning (profile Point extra) (clauses Point extra source) claim := by
  unfold fold at folded
  cases resolved : resolve events with
  | error e => simp [resolved] at folded
  | ok snapshot =>
    rw [resolved] at folded
    have same := Except.ok.inj folded
    subst state
    exact evaluate_held_meaning _ _ _ snapshot (resolve_warrant_ids_nodup events snapshot resolved)
      (actual_base_sound Point source pointFirst extra snapshot (resolve_warrant_ids_nodup events snapshot resolved))
      claim heldClaim

theorem native_fold_held_sound (Point : Type) (source : String) (pointFirst extra : Bool)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission Unit source pointFirst extra) events = .ok state)
    (heldClaim : held state claim = true) :
    ClaimMeaning (profile Point extra) (clauses Point extra source) claim := by
  apply actual_fold_held_sound Point source pointFirst extra events state claim _ heldClaim
  rw [admission_point_independent Point source pointFirst extra]
  exact folded

def counterWorld : World Unit :=
  ⟨fun _ => False,fun _ => True,fun _ => True,fun _ => True,()⟩
theorem counterHypotheses : Hypotheses counterWorld false := by
  constructor <;> simp [counterWorld]
theorem side_not_tight_countermodel :
    Means (profile Unit false) .sidePoint .theory ∧
    ¬ Means (profile Unit false) .tightPoint .theory := by
  refine ⟨side_point_given Unit false,?_⟩
  intro alleged
  rcases alleged (counterWorld,none) ⟨counterHypotheses,trivial⟩ with ⟨x,_,bad⟩
  exact bad
def acceptingWorld : World Unit :=
  ⟨fun _ => True,fun _ => True,fun _ => True,fun _ => True,()⟩
theorem accepting_theory_inhabited : mem true (acceptingWorld,none) .theory := by
  refine ⟨?_,trivial⟩
  constructor <;> simp [acceptingWorld]

theorem countermodel_join_not_global : ¬ Means (profile Unit false) .licensedRoutes .theory := by
  intro alleged
  rcases (alleged (counterWorld,none) ⟨counterHypotheses,trivial⟩).2 with ⟨x,_,bad⟩
  exact bad

@[simp] private theorem binding_self (b : Binding) : instBEqBinding.beq b b = true := by
  cases b
  simp [instBEqBinding.beq, Bool.and_eq_true, beq_iff_eq]

@[simp] private theorem binding_self_bool (b : Binding) : (b == b) = true := binding_self b

theorem universal_K2 (Point : Type) (extra : Bool) (source : String) :
    acceptsNarrow (profile Point extra) (clauses Point extra source) (firstRestricted source) (first source) = true := by
  simp [acceptsNarrow,boundClause,checkNarrow,clauses,clause,profile,firstRestricted,first,binding,subset,List.find?,List.eraseDups_cons,instBEqBinding]
theorem point_K2_refused (Point : Type) (extra : Bool) (source : String) :
    acceptsNarrow (profile Point extra) (clauses Point extra source) (pointAttempt source) (second source) = false := by
  simp [acceptsNarrow,boundClause,checkNarrow,clauses,clause,profile,pointAttempt,second,binding,subset,statement,List.find?,List.eraseDups_cons,instBEqBinding]

def bindingJson (b : Binding) : Json := Json.mkObj [
  ("statementHash",toJson b.statementHash),("scopeHash",toJson b.scopeHash),("modelHash",toJson b.modelHash),
  ("inputHashes",toJson b.inputHashes),("authority",toJson b.authority),
  ("authorityVersion",toJson b.authorityVersion),("kernelVersion",toJson b.kernelVersion)]
def warrantJson (w : Warrant) : Json :=
  let evidence := match w.evidence with
    | .receipt data => Json.mkObj [("kind",toJson "receipt"),("data",toJson data)]
    | .narrow dep => Json.mkObj [("kind",toJson "narrow"),("premise",toJson dep)]
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
  (← j.getArr?).toList.mapM Json.getStr?
def run (text digest mode : String) : Except String Json := do
  let json ← Decoder.parseUnique text
  Decoder.exactFields json ["schema_version","id","seed","title","situation","inputs",
    "attempted_conclusion","expected","scope_or_region","sources"]
  if (← (← json.getObjVal? "schema_version").getNat?) != 1 then throw "unsupported fixture schema"
  let caseId ← (← json.getObjVal? "id").getStr?
  if caseId != "GP-X179" && caseId != "GP-X180" then throw "uncommissioned fixture"
  let pointFirst := caseId == "GP-X180"
  let inputs ← json.getObjVal? "inputs"
  Decoder.exactFields inputs ["contexts","relations","premises","conclusion_class","conclusion_text"]
  if (← strings (← inputs.getObjVal? "contexts")) != ["tight","loose","side"] then throw "wrong selected contexts"
  if (← (← inputs.getObjVal? "conclusion_class").getStr?) != "universal_property" ||
      (← (← inputs.getObjVal? "conclusion_text").getStr?) != statement .licensedRoutes then throw "wrong literal conclusion"
  let relations ← (← inputs.getObjVal? "relations").getArr?
  if relations.size != 2 then throw "missing selected relation"
  for index in [0,1] do
    let relation := relations[index]!
    Decoder.exactFields relation ["name","source","target","relation"]
    if (← (← relation.getObjVal? "name").getStr?) != (if index == 0 then "first" else "second") ||
       (← (← relation.getObjVal? "source").getStr?) != "tight" ||
       (← (← relation.getObjVal? "target").getStr?) != (if index == 0 then "loose" else "side") ||
       (← (← relation.getObjVal? "relation").getStr?) != "equations_forgotten" then throw "wrong selected relation/model"
  let premises ← (← inputs.getObjVal? "premises").getArr?
  if premises.size != 2 then throw "missing literal premise"
  for index in [0,1] do
    let pointLeg := if pointFirst then index == 0 else index == 1
    let premise := premises[index]!
    Decoder.exactFields premise ["context","statement_class","statement","route"]
    if (← (← premise.getObjVal? "context").getStr?) != (if pointLeg then "side" else "loose") ||
       (← (← premise.getObjVal? "statement_class").getStr?) != (if pointLeg then "exhibited_point" else "universal_property") ||
       (← (← premise.getObjVal? "statement").getStr?) != (if pointLeg then "a point in the relaxed side model" else "a universal property")
       then throw "wrong literal premise kind/statement/model"
    let route ← (← premise.getObjVal? "route").getArr?
    if route.size != 1 then throw "unsupported literal route length"
    Decoder.exactFields route[0]! ["relation","direction"]
    if (← (← route[0]!.getObjVal? "relation").getStr?) != (if pointLeg then "second" else "first") ||
       (← (← route[0]!.getObjVal? "direction").getStr?) != "reverse" then throw "wrong literal selected route"
  if !(["normal","reverse","duplicates","reverse_duplicates","withheld_universal","withheld_point",
        "wrong_binding","wrong_point_identity","wrong_model","wrong_dependency","pointwise_laundering",
        "justified_tight_membership"].contains mode) then throw "unknown control mode"
  let extra := mode == "justified_tight_membership"
  let mut roots := if pointFirst then [second digest,first digest] else [first digest,second digest]
  if mode == "withheld_universal" then roots := roots.filter (·.id != 10)
  if mode == "withheld_point" then roots := roots.filter (·.id != 20)
  let mut narrowed := firstRestricted digest
  let mut attempted := routedPoint digest extra
  if mode == "wrong_binding" then narrowed := {narrowed with binding := {narrowed.binding with inputHashes := ["changed"]}}
  if mode == "wrong_point_identity" then attempted := {attempted with binding := binding digest .sidePoint .theory}
  if mode == "wrong_model" then attempted := {attempted with binding := {attempted.binding with modelHash := "other selected model"}}
  if mode == "wrong_dependency" then narrowed := {narrowed with evidence := .narrow 20}
  if mode == "pointwise_laundering" then attempted := {attempted with binding := binding digest .sidePoint .tight}
  let records := roots ++ [narrowed,attempted,joint digest pointFirst]
  let mut events := records.flatMap fun w => [.current ⟨w.claim,1,w.binding⟩,.warrant w]
  if mode == "reverse" || mode == "reverse_duplicates" then events := events.reverse
  if mode == "duplicates" || mode == "reverse_duplicates" then events := events ++ events
  let state ← fold (admission Unit digest pointFirst extra) events
  let universalCheck := acceptsNarrow (profile Unit extra) (clauses Unit extra digest) (firstRestricted digest) (first digest)
  let pointCheck := acceptsNarrow (profile Unit extra) (clauses Unit extra digest) (pointAttempt digest) (second digest)
  let licensed := if pointFirst then [state.supports.contains 120,state.supports.contains 110]
    else [state.supports.contains 110,state.supports.contains 120]
  return Json.mkObj [("conditional",toJson true),("case",toJson caseId),("source_digest",toJson digest),
    ("mode",toJson mode),("literal_inputs",inputs),("literal_fixture",json),
    ("state",stateJson state),("snapshot",snapshotJson state.snapshot),
    ("route_licensed",toJson licensed),
    ("narrow_checks",Json.mkObj [("universal",toJson universalCheck),("exhibited_point",toJson pointCheck)]),
    ("argument_dependency_ids",toJson (dependencies pointFirst)),("additional_tight_membership",toJson extra),
    ("point_statement_scope",toJson "global-conditional-theory"),
    ("countermodel",Json.mkObj [("tight_empty",toJson true),("side_inhabited",toJson true),("same_witness_not_tight",toJson true)])]
#print axioms subset_sound
#print axioms side_not_tight_countermodel
#print axioms accepting_theory_inhabited
#print axioms routes_composition_sound
#print axioms admission_point_independent
#print axioms actual_validator_sound
#print axioms actual_fold_held_sound
#print axioms native_fold_held_sound
end ConditionalPointRoutes

def main (args : List String) : IO UInt32 := do
  match args with
  | [path,digest,mode] =>
    let result := ConditionalPointRoutes.run (← IO.FS.readFile path) digest mode
    IO.println (match result with
      | .ok output => output.compress
      | .error e => (Lean.Json.mkObj [("status",Lean.toJson "MALFORMED"),("error",Lean.toJson e)]).compress)
    return 0
  | _ => return 2
