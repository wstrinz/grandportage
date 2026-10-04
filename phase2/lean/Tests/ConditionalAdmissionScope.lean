import GP50.Entry
import GP50.Presentation
import GP50.NarrowingAdmissionProofs
namespace ConditionalAdmissionScope
open GP50 Lean GP50.Semantic

structure Claim where
  coefficientField : String
  polynomial : String
  generator : String
  factors : List Nat
  deriving DecidableEq, BEq
def fixedClaim : Claim := ⟨"Q","a^2+5","a",[2]⟩
def claimDigest := "sha256:8e0e9c4edbfa3978deaa7a2f99aad4abed22e848eed83f93111d50c60fcc6149"
def contractVersion := "synthetic-contract-1"
inductive Kind where | full | quotient | heuristic | label deriving DecidableEq, BEq
inductive Scope where | unconditional | grh deriving DecidableEq, BEq
def kindName : Kind → String
  | .full => "full_class_group" | .quotient => "class_group_is_quotient_of_candidate"
  | .heuristic => "heuristic_assertion" | .label => "producer_full_certification_label"
def scopeName : Scope → String | .unconditional => "assumptions=[]" | .grh => "assumptions=[GRH]"
structure Input where
  claim : Claim
  digest : String
  producerId : String
  producerVersion : String
  kind : Kind
  reach : Scope
  admitted : Bool
  succeeded : Bool
  checkerVersion : Option String
  checkedDigest : Option String
  evidenceStatus : String
  requested : Scope

def registered (i : Input) : Bool := decide
  (i.checkerVersion = some contractVersion ∧ i.producerId = "class-group-contract-fixture" ∧
   i.producerVersion = "1" ∧ i.evidenceStatus = "assumed_for_rule_level_test")
def admissionOK (i : Input) : Bool := i.admitted && registered i
def successOK (i : Input) : Bool := i.succeeded && registered i &&
  decide (i.claim = fixedClaim ∧ i.digest = claimDigest ∧ i.checkedDigest = some claimDigest ∧
    (i.kind = .full ∨ i.kind = .quotient))

-- Arbitrary interpretations, with no number theory encoded or computed here.
structure World where
  grh : Prop
  full : Claim → Prop
  quotient : Claim → Prop
  admitted : String → Prop
  checked : Claim → String → Kind → Scope → Prop

def scopeHolds (w : World) : Scope → Prop | .unconditional => True | .grh => w.grh
def resultHolds (w : World) (c : Claim) : Kind → Prop
  | .full => w.full c | .quotient => w.quotient c | .heuristic => False | .label => False

-- Flags select explicitly supplied premises; the sound contract remains a
-- semantic hypothesis in every context, never an unconditional arithmetic axiom.
structure Hypotheses (i : Input) (w : World) : Prop where
  namedAdmittedPremise : admissionOK i = true → w.admitted contractVersion
  namedSuccessfulBoundCheck : successOK i = true →
    w.checked fixedClaim contractVersion i.kind i.reach
  soundRegisteredContract : ∀ c kind reach,
    w.admitted contractVersion → w.checked c contractVersion kind reach →
    scopeHolds w reach → resultHolds w c kind

inductive Formula where
  | admitted
  | checked (kind : Kind) (reach : Scope)
  | result (claim : Claim) (kind : Kind)
  deriving DecidableEq

def subset (dest source : Scope) : Bool :=
  decide (dest = source ∨ (dest = .grh ∧ source = .unconditional))
theorem subset_sound (i : Input) (a b : Scope) (w : World)
    (checked : subset a b = true)
    (present : Hypotheses i w ∧ scopeHolds w a) : Hypotheses i w ∧ scopeHolds w b := by
  simp only [subset,decide_eq_true_eq] at checked
  rcases checked with same | ⟨same,target⟩
  · exact same ▸ present
  · subst a; subst b; exact ⟨present.1,trivial⟩

def holds (f : Formula) (w : World) : Prop :=
  match f with
  | .admitted => w.admitted contractVersion
  | .checked kind reach => w.checked fixedClaim contractVersion kind reach
  | .result claim kind => resultHolds w claim kind

def profile (i : Input) : Profile where
  Stmt := Formula
  Scope := Scope
  Ctx := World
  same := fun a b => decide (a = b)
  same_sound := fun _ _ h => of_decide_eq_true h
  mem := fun w scope => Hypotheses i w ∧ scopeHolds w scope
  le := subset
  le_sound := subset_sound i
  Holds := holds
  contra := fun _ _ => false
  contra_sound := by intro a b c impossible; contradiction

theorem named_admission_given (i : Input) (given : admissionOK i = true) :
    Means (profile i) .admitted .unconditional := by
  intro w present
  exact present.1.namedAdmittedPremise given
theorem named_success_given (i : Input) (given : successOK i = true) :
    Means (profile i) (.checked i.kind i.reach) .unconditional := by
  intro w present
  exact present.1.namedSuccessfulBoundCheck given
theorem result_from_sound_contract (i : Input)
    (admitted : Means (profile i) .admitted .unconditional)
    (successful : Means (profile i) (.checked i.kind i.reach) .unconditional) :
    Means (profile i) (.result fixedClaim i.kind) i.reach := by
  intro w present
  exact present.1.soundRegisteredContract fixedClaim i.kind i.reach
    (admitted w ⟨present.1,trivial⟩) (successful w ⟨present.1,trivial⟩) present.2

def claimJson (c : Claim) : Json := Json.mkObj [
  ("kind",toJson "class_group_complete"),("number_field",Json.mkObj [
    ("coefficient_field",toJson c.coefficientField),("defining_polynomial",toJson c.polynomial),
    ("generator",toJson c.generator)]),("candidate_group_invariant_factors",toJson c.factors)]
def statement : Formula → String
  | .admitted => "named admitted checker contract:synthetic-contract-1"
  | .checked kind reach => s!"named successful bound check:{claimDigest}:{kindName kind}:{scopeName reach}"
  | .result claim kind => s!"result:{kindName kind}:{claimDigest}:{(claimJson claim).compress}"
def binding (i : Input) (source literal : String) (formula : Formula) (scope : Scope) : Binding :=
  ⟨statement formula,scopeName scope,(claimJson i.claim).compress,[source,literal],
    "test-only-explicit-synthetic-admission-contract",1,1⟩
def clause (i : Input) (source literal : String) (key : Nat) (f : Formula) (s : Scope) : Clause (profile i) :=
  ⟨key,1,binding i source literal f s,f,s⟩
def clauses (i : Input) (source literal : String) : List (Clause (profile i)) :=
  [clause i source literal 5 .admitted .unconditional,
   clause i source literal 6 (.checked i.kind i.reach) .unconditional,
   clause i source literal 1 (.result fixedClaim i.kind) i.reach,
   clause i source literal 2 (.result fixedClaim .full) i.requested]
def admittedW (i : Input) (source literal : String) : Warrant :=
  ⟨5,5,1,binding i source literal .admitted .unconditional,.receipt "supplied:named-admitted-contract"⟩
def checkedW (i : Input) (source literal : String) : Warrant :=
  ⟨6,6,1,binding i source literal (.checked i.kind i.reach) .unconditional,.receipt "supplied:named-successful-bound-check"⟩
def resultW (i : Input) (source literal : String) : Warrant :=
  ⟨10,1,1,binding i source literal (.result fixedClaim i.kind) i.reach,
    .derived [5,6] "sound-bound-result-at-effective-reach"⟩
def targetW (i : Input) (source literal : String) : Warrant :=
  ⟨20,2,1,binding i source literal (.result fixedClaim .full) i.requested,.narrow 10⟩
def custodyW (i : Input) (source literal : String) : Warrant :=
  ⟨100,100,1,binding i source literal (.result i.claim .label) .unconditional,.citation literal⟩
def base (i : Input) (source literal : String) : Admission :=
  {Admission.refuseAll with
    receipt := fun w data =>
      (decide (w = admittedW i source literal ∧ data = "supplied:named-admitted-contract") && admissionOK i) ||
      (decide (w = checkedW i source literal ∧ data = "supplied:named-successful-bound-check") && successOK i)
    rule := fun w premises data =>
      decide (w = resultW i source literal ∧ premises = [admittedW i source literal,checkedW i source literal] ∧
        data = "sound-bound-result-at-effective-reach")}
def admission (i : Input) (source literal : String) : Admission :=
  withNarrowing (profile i) (clauses i source literal) (base i source literal)

theorem registered_meaning (i : Input) (source literal : String)
    (c : Clause (profile i)) (present : c ∈ clauses i source literal)
    (meaning : Means (profile i) c.stmt c.scope) :
    ClaimMeaning (profile i) (clauses i source literal) c.key := by
  refine ⟨⟨c,present,rfl⟩,?_⟩
  intro other otherPresent key
  have unique : ((clauses i source literal).map (·.key)).Nodup := by simp [clauses,clause]
  have same := key_unique_of_nodup (clauses i source literal) (fun c => c.key)
    unique other c otherPresent present key
  exact same ▸ meaning

theorem actual_base_sound (i : Input) (source literal : String) (snapshot : Snapshot)
    (unique : (snapshot.warrants.map (·.id)).Nodup) :
    BaseValidatorSound (profile i) (clauses i source literal) (base i source literal) snapshot := by
  constructor
  · intro w present data accepted
    simp only [base,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at accepted
    rcases accepted with ⟨⟨same,_⟩,given⟩ | ⟨⟨same,_⟩,given⟩
    · subst w
      exact ⟨admittedW i source literal,present,rfl,registered_meaning i source literal
        (clause i source literal 5 .admitted .unconditional) (by simp [clauses])
        (named_admission_given i given)⟩
    · subst w
      exact ⟨checkedW i source literal,present,rfl,registered_meaning i source literal
        (clause i source literal 6 (.checked i.kind i.reach) .unconditional) (by simp [clauses])
        (named_success_given i given)⟩
  · intro w present declaration accepted; contradiction
  · intro w present premises side accepted members truePremises
    simp only [base,decide_eq_true_eq] at accepted
    rcases accepted with ⟨same,samePremises,_⟩
    subst w; subst premises
    have admittedTruth := warrant_meaning_claim (profile i) (clauses i source literal) snapshot unique
      (admittedW i source literal) (members _ (by simp)) (truePremises _ (by simp))
    have st := warrant_meaning_claim (profile i) (clauses i source literal) snapshot unique
      (checkedW i source literal) (members _ (by simp)) (truePremises _ (by simp))
    have am := admittedTruth.2 (clause i source literal 5 .admitted .unconditional) (by simp [clauses]) rfl
    have sm := st.2 (clause i source literal 6 (.checked i.kind i.reach) .unconditional) (by simp [clauses]) rfl
    exact ⟨resultW i source literal,present,rfl,registered_meaning i source literal
      (clause i source literal 1 (.result fixedClaim i.kind) i.reach) (by simp [clauses])
      (result_from_sound_contract i am sm)⟩

theorem actual_validator_sound (i : Input) (source literal : String) (snapshot : Snapshot)
    (unique : (snapshot.warrants.map (·.id)).Nodup) :
    ValidatorSound (admission i source literal) snapshot
      (WarrantMeaning (profile i) (clauses i source literal) snapshot) :=
  withNarrowing_validator_sound _ _ _ snapshot unique (actual_base_sound i source literal snapshot unique)
theorem actual_fold_held_sound (i : Input) (source literal : String)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission i source literal) events = .ok state)
    (heldClaim : held state claim = true) : ClaimMeaning (profile i) (clauses i source literal) claim := by
  unfold fold at folded
  cases resolved : resolve events with
  | error e => simp [resolved] at folded
  | ok snapshot =>
    rw [resolved] at folded
    have same := Except.ok.inj folded
    subst state
    exact evaluate_held_meaning _ _ _ snapshot (resolve_warrant_ids_nodup events snapshot resolved)
      (actual_base_sound i source literal snapshot (resolve_warrant_ids_nodup events snapshot resolved)) claim heldClaim
theorem held_target_is_conditional_full (i : Input) (source literal : String)
    (events : List Event) (state : RuntimeState)
    (folded : fold (admission i source literal) events = .ok state)
    (heldClaim : held state 2 = true) :
    Means (profile i) (.result fixedClaim .full) i.requested :=
  (actual_fold_held_sound i source literal events state 2 folded heldClaim).2
    (clause i source literal 2 (.result fixedClaim .full) i.requested) (by simp [clauses]) rfl

theorem GRH_cannot_be_dropped : ¬ (∀ g f : Prop, (g → f) → f) := by
  intro alleged
  exact alleged False False (fun bad => bad)
theorem quotient_does_not_imply_full : ¬ (∀ quotient full : Prop, quotient → full) := by
  intro alleged
  exact alleged True False trivial
theorem scope_narrowing_direction :
    subset .grh .unconditional = true ∧ subset .unconditional .grh = false := by decide

def readScope (json : Json) : Except String Scope := do
  let xs ← (← json.getArr?).toList.mapM Json.getStr?
  if xs == [] then return .unconditional
  if xs == ["GRH"] then return .grh
  throw "unknown assumption scope"
def nullableString : Json → Except String (Option String)
  | .null => .ok none | value => return some (← value.getStr?)
def decodeInput (json : Json) : Except String Input := do
  Decoder.exactFields json ["fixture_kind","claim","claim_sha256","synthetic_producer","effective_result",
    "supplied_premises","requested_scope_assumptions"]
  if (← (← json.getObjVal? "fixture_kind").getStr?) !=
      "conditional_admission_contract_not_a_real_certifying_run" then throw "wrong conditional fixture kind"
  let c ← json.getObjVal? "claim"
  Decoder.exactFields c ["kind","number_field","candidate_group_invariant_factors"]
  if (← (← c.getObjVal? "kind").getStr?) != "class_group_complete" then throw "wrong bound claim kind"
  let field ← c.getObjVal? "number_field"
  Decoder.exactFields field ["coefficient_field","defining_polynomial","generator"]
  let claim : Claim := ⟨← (← field.getObjVal? "coefficient_field").getStr?,
    ← (← field.getObjVal? "defining_polynomial").getStr?,← (← field.getObjVal? "generator").getStr?,
    ← (← (← c.getObjVal? "candidate_group_invariant_factors").getArr?).toList.mapM Json.getNat?⟩
  let producer ← json.getObjVal? "synthetic_producer"
  Decoder.exactFields producer ["id","version"]
  let result ← json.getObjVal? "effective_result"
  Decoder.exactFields result ["conclusion","assumptions"]
  let kind ← match ← (← result.getObjVal? "conclusion").getStr? with
    | "full_class_group" => pure Kind.full | "class_group_is_quotient_of_candidate" => pure Kind.quotient
    | "heuristic_assertion" => pure Kind.heuristic | "producer_full_certification_label" => pure Kind.label
    | _ => throw "unknown effective result kind"
  let premises ← json.getObjVal? "supplied_premises"
  Decoder.exactFields premises ["checker_admitted","bound_check_succeeded","checker_contract_version",
    "checked_claim_sha256","evidence_status"]
  return ⟨claim,← (← json.getObjVal? "claim_sha256").getStr?,
    ← (← producer.getObjVal? "id").getStr?,← (← producer.getObjVal? "version").getStr?,
    kind,← readScope (← result.getObjVal? "assumptions"),
    ← (← premises.getObjVal? "checker_admitted").getBool?,← (← premises.getObjVal? "bound_check_succeeded").getBool?,
    ← nullableString (← premises.getObjVal? "checker_contract_version"),
    ← nullableString (← premises.getObjVal? "checked_claim_sha256"),
    ← (← premises.getObjVal? "evidence_status").getStr?,
    ← readScope (← json.getObjVal? "requested_scope_assumptions")⟩

def bindingJson (b : Binding) : Json := Json.mkObj [
  ("statementHash",toJson b.statementHash),("scopeHash",toJson b.scopeHash),("modelHash",toJson b.modelHash),
  ("inputHashes",toJson b.inputHashes),("authority",toJson b.authority),
  ("authorityVersion",toJson b.authorityVersion),("kernelVersion",toJson b.kernelVersion)]
def warrantJson (w : Warrant) : Json :=
  let evidence := match w.evidence with
    | .receipt data => Json.mkObj [("kind",toJson "receipt"),("data",toJson data)]
    | .derived deps side => Json.mkObj [("kind",toJson "derived"),("premises",toJson deps),("sideReceipt",toJson side)]
    | .narrow dep => Json.mkObj [("kind",toJson "narrow"),("premise",toJson dep)]
    | .theoremWarrant declaration => Json.mkObj [("kind",toJson "theorem"),("declaration",toJson declaration)]
    | .citation text => Json.mkObj [("kind",toJson "citation"),("text",toJson text)]
    | _ => Json.mkObj [("kind",toJson "unregistered")]
  Json.mkObj [("id",toJson w.id),("claim",toJson w.claim),("version",toJson w.version),
    ("binding",bindingJson w.binding),("evidence",evidence)]
def snapshotJson (s : Snapshot) : Json := Json.mkObj [
  ("domain",toJson s.domain),("warrants",toJson (s.warrants.map warrantJson)),
  ("currents",toJson (s.currents.map fun c => Json.mkObj [
    ("claim",toJson c.claim),("version",toJson c.version),("binding",bindingJson c.binding)])),
  ("retracted",toJson s.retracted),("successors",toJson s.successors)]

def run (text source mode : String) : Except String Json := do
  let literal ← Decoder.parseUnique text
  Decoder.exactFields literal ["schema_version","id","seed","title","situation","inputs",
    "attempted_conclusion","expected","scope_or_region","sources"]
  if (← (← literal.getObjVal? "schema_version").getNat?) != 1 then throw "unsupported fixture schema"
  let caseId ← (← literal.getObjVal? "id").getStr?
  if !(["GP-A27-full","GP-A27-keep-GRH","GP-A27-drop-GRH","GP-A27-partial","GP-A27-heuristic","GP-A27-label"].contains caseId)
    then throw "uncommissioned fixture"
  if (← (← literal.getObjVal? "attempted_conclusion").getStr?) !=
    "Treat the bound candidate class-group data as established in the requested scope under the explicitly supplied premises."
    then throw "wrong conditional attempted conclusion"
  let inputs ← literal.getObjVal? "inputs"
  let i ← decodeInput inputs
  let bound := literal.compress
  if !(["normal","reverse","duplicates","reverse_duplicates","withheld_success","wrong_binding","theorem_pointer",
    "producer_label_only","quotient_laundering"].contains mode) then throw "unknown control mode"
  let a := admittedW i source bound
  let mut s := checkedW i source bound
  if mode == "wrong_binding" then s := {s with binding := {s.binding with inputHashes := ["corrupt binding"]}}
  if mode == "theorem_pointer" then s := {s with evidence := .theoremWarrant "unadmitted_theorem_pointer"}
  if mode == "producer_label_only" then s := {s with evidence := .citation "producer:Proof=Full"}
  let mut target := targetW i source bound
  if mode == "quotient_laundering" then target := {target with binding := binding i source bound (.result fixedClaim i.kind) i.requested}
  let records := [a] ++ (if mode == "withheld_success" then [] else [s]) ++
    [resultW i source bound,target,custodyW i source bound]
  let mut events := records.flatMap fun w => [.current ⟨w.claim,w.version,w.binding⟩,.warrant w]
  if mode == "reverse" || mode == "reverse_duplicates" then events := events.reverse
  if mode == "duplicates" || mode == "reverse_duplicates" then events := events ++ events
  let state ← fold (admission i source bound) events
  return Json.mkObj [("case",toJson caseId),("source_digest",toJson source),("mode",toJson mode),
    ("conditional",toJson true),("literal_fixture",literal),("literal_inputs",inputs),("bound_literal",toJson bound),
    ("bound_claim",claimJson i.claim),("bound_claim_literal",toJson (claimJson i.claim).compress),
    ("fixed_claim_literal",toJson (claimJson fixedClaim).compress),
    ("admission_premise_registered",toJson (admissionOK i)),("successful_bound_check_registered",toJson (successOK i)),
    ("effective_result_kind",toJson (kindName i.kind)),("effective_scope",toJson (scopeName i.reach)),
    ("requested_scope",toJson (scopeName i.requested)),
    ("actual_narrow_check",toJson (acceptsNarrow (profile i) (clauses i source bound) target (resultW i source bound))),
    ("result_dependencies",toJson ([5,6] : List Nat)),("state",stateJson state),("snapshot",snapshotJson state.snapshot)]

#print axioms subset_sound
#print axioms named_admission_given
#print axioms named_success_given
#print axioms result_from_sound_contract
#print axioms actual_base_sound
#print axioms actual_validator_sound
#print axioms actual_fold_held_sound
#print axioms held_target_is_conditional_full
#print axioms GRH_cannot_be_dropped
#print axioms quotient_does_not_imply_full
#print axioms scope_narrowing_direction
end ConditionalAdmissionScope

def main (args : List String) : IO UInt32 := do
  match args with
  | [path,digest,mode] =>
    let result := ConditionalAdmissionScope.run (← IO.FS.readFile path) digest mode
    IO.println (match result with
      | .ok output => output.compress
      | .error e => (Lean.Json.mkObj [("status",Lean.toJson "MALFORMED"),("error",Lean.toJson e)]).compress)
    return 0
  | _ => return 2

