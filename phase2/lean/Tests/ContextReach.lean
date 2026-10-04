import GP50.Entry
import GP50.Presentation
import GP50.NarrowingAdmissionProofs
namespace ContextReach
open GP50 Lean GP50.Semantic

inductive Kind where | empty | nonempty deriving DecidableEq, BEq
def kindName : Kind → String | .empty => "EMPTY" | .nonempty => "NONEMPTY"
inductive Question where | license | record deriving DecidableEq, BEq
-- One emptiness/nonemptiness warrant at its own context and an attempted use at another.
structure Input where
  kind : Kind
  source : String
  target : String
  relation : String
  direct : Option String
  question : Question
  debt : Option String
  deriving DecidableEq, BEq

-- Only the identity context change is licensed; every typed or untyped change is lossy for reach.
def licensed (i : Input) : Bool := decide (i.source = i.target)

-- Arbitrary interpretations: which contexts have points of the model.
structure World where
  points : String → Prop
def fact (k : Kind) (c : String) (w : World) : Prop :=
  match k with | .empty => ¬ w.points c | .nonempty => w.points c

structure Hypotheses (i : Input) (w : World) : Prop where
  namedSourceWarrant : fact i.kind i.source w
  namedDirectTargetWarrant : i.direct.isSome = true → fact i.kind i.target w

inductive Formula where
  | fact (kind : Kind) (context : String)
  | debt (reason : String)
  deriving DecidableEq
def holds : Formula → World → Prop
  | .fact k c, w => fact k c w
  | .debt _, _ => True

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

theorem source_given (i : Input) : Means (profile i) (.fact i.kind i.source) () :=
  fun _ present => present.namedSourceWarrant
theorem direct_given (i : Input) (supplied : i.direct.isSome = true) :
    Means (profile i) (.fact i.kind i.target) () :=
  fun _ present => present.namedDirectTargetWarrant supplied
theorem identity_transport_sound (i : Input) (ok : licensed i = true) :
    Means (profile i) (.fact i.kind i.target) () := by
  have same : i.source = i.target := of_decide_eq_true ok
  rw [← same]
  exact source_given i
theorem debt_is_only_a_record (i : Input) (reason : String) : Means (profile i) (.debt reason) () :=
  fun _ _ => trivial

def statement : Formula → String
  | .fact k c => s!"{kindName k} in context:{c}"
  | .debt r => s!"unanswered context step recorded:{r}"
def binding (i : Input) (source literal : String) (f : Formula) : Binding :=
  ⟨statement f,i.relation,s!"{i.source} -> {i.target}",[source,literal],"test-only-context-reach-contract",1,1⟩
def clauses (i : Input) (source literal : String) : List (Clause (profile i)) :=
  [⟨1,1,binding i source literal (.fact i.kind i.target),.fact i.kind i.target,()⟩,
   ⟨3,1,binding i source literal (.debt (i.debt.getD "none")),.debt (i.debt.getD "none"),()⟩,
   ⟨10,1,binding i source literal (.fact i.kind i.source),.fact i.kind i.source,()⟩]
def sourceW (i : Input) (source literal : String) : Warrant :=
  ⟨10,10,1,binding i source literal (.fact i.kind i.source),.receipt "supplied:named-source-warrant"⟩
def transportW (i : Input) (source literal : String) : Warrant :=
  ⟨1,1,1,binding i source literal (.fact i.kind i.target),.derived [10] "identity-context-transport"⟩
def directW (i : Input) (source literal : String) : Warrant :=
  ⟨11,1,1,binding i source literal (.fact i.kind i.target),.receipt s!"supplied:named-direct-target-warrant:{i.direct.getD "none"}"⟩
def debtW (i : Input) (source literal : String) : Warrant :=
  ⟨3,3,1,binding i source literal (.debt (i.debt.getD "none")),.receipt "recorded:unanswered-context-step"⟩
def custodyW (i : Input) (source literal : String) : Warrant :=
  ⟨100,100,1,binding i source literal (.debt "custody"),.citation literal⟩
def base (i : Input) (source literal : String) : Admission :=
  {Admission.refuseAll with
    receipt := fun w data =>
      decide (w = sourceW i source literal ∧ data = "supplied:named-source-warrant") ||
      (decide (w = directW i source literal ∧ data = s!"supplied:named-direct-target-warrant:{i.direct.getD "none"}") &&
        i.direct.isSome) ||
      (decide (w = debtW i source literal ∧ data = "recorded:unanswered-context-step") && i.debt.isSome)
    rule := fun w premises data =>
      decide (w = transportW i source literal ∧ premises = [sourceW i source literal] ∧
        data = "identity-context-transport") && licensed i}
def admission (i : Input) (source literal : String) : Admission :=
  withNarrowing (profile i) (clauses i source literal) (base i source literal)

theorem registered_meaning (i : Input) (source literal : String)
    (c : Clause (profile i)) (present : c ∈ clauses i source literal)
    (meaning : Means (profile i) c.stmt c.scope) :
    ClaimMeaning (profile i) (clauses i source literal) c.key := by
  refine ⟨⟨c,present,rfl⟩,?_⟩
  intro other otherPresent key
  have unique : ((clauses i source literal).map (·.key)).Nodup := by simp [clauses]
  have same := key_unique_of_nodup (clauses i source literal) (fun c => c.key)
    unique other c otherPresent present key
  exact same ▸ meaning

theorem actual_base_sound (i : Input) (source literal : String) (snapshot : Snapshot) :
    BaseValidatorSound (profile i) (clauses i source literal) (base i source literal) snapshot := by
  constructor
  · intro w present data accepted
    simp only [base,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at accepted
    rcases accepted with (⟨same,_⟩ | ⟨⟨same,_⟩,supplied⟩) | ⟨⟨same,_⟩,_⟩
    · subst w
      exact ⟨sourceW i source literal,present,rfl,registered_meaning i source literal
        ⟨10,1,binding i source literal (.fact i.kind i.source),.fact i.kind i.source,()⟩
        (by simp [clauses]) (source_given i)⟩
    · subst w
      exact ⟨directW i source literal,present,rfl,registered_meaning i source literal
        ⟨1,1,binding i source literal (.fact i.kind i.target),.fact i.kind i.target,()⟩
        (by simp [clauses]) (direct_given i supplied)⟩
    · subst w
      exact ⟨debtW i source literal,present,rfl,registered_meaning i source literal
        ⟨3,1,binding i source literal (.debt (i.debt.getD "none")),.debt (i.debt.getD "none"),()⟩
        (by simp [clauses]) (debt_is_only_a_record i _)⟩
  · intro w present declaration accepted; contradiction
  · intro w present premises side accepted members truePremises
    simp only [base,Bool.and_eq_true,decide_eq_true_eq] at accepted
    rcases accepted with ⟨⟨same,_,_⟩,ok⟩
    subst w
    exact ⟨transportW i source literal,present,rfl,registered_meaning i source literal
      ⟨1,1,binding i source literal (.fact i.kind i.target),.fact i.kind i.target,()⟩
      (by simp [clauses]) (identity_transport_sound i ok)⟩

theorem actual_validator_sound (i : Input) (source literal : String) (snapshot : Snapshot)
    (unique : (snapshot.warrants.map (·.id)).Nodup) :
    ValidatorSound (admission i source literal) snapshot
      (WarrantMeaning (profile i) (clauses i source literal) snapshot) :=
  withNarrowing_validator_sound _ _ _ snapshot unique (actual_base_sound i source literal snapshot)
theorem actual_fold_held_sound (i : Input) (source literal : String)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission i source literal) events = .ok state)
    (heldClaim : held state claim = true) : ClaimMeaning (profile i) (clauses i source literal) claim := by
  unfold fold at folded
  cases resolved : resolve events with
  | error err => simp [resolved] at folded
  | ok snapshot =>
    rw [resolved] at folded
    have same := Except.ok.inj folded
    subst state
    exact evaluate_held_meaning _ _ _ snapshot (resolve_warrant_ids_nodup events snapshot resolved)
      (actual_base_sound i source literal snapshot) claim heldClaim
theorem held_target_fact (i : Input) (source literal : String)
    (events : List Event) (state : RuntimeState)
    (folded : fold (admission i source literal) events = .ok state)
    (heldClaim : held state 1 = true) : Means (profile i) (.fact i.kind i.target) () :=
  (actual_fold_held_sound i source literal events state 1 folded heldClaim).2
    ⟨1,1,binding i source literal (.fact i.kind i.target),.fact i.kind i.target,()⟩ (by simp [clauses]) rfl

-- A fact at one context says nothing about a different context, for either kind.
theorem context_change_not_transported (k : Kind) (s t : String) (different : s ≠ t) :
    ∃ w, fact k s w ∧ ¬ fact k t w := by
  cases k
  · exact ⟨⟨fun c => c ≠ s⟩,fun bad => bad rfl,fun bad => bad (Ne.symm different)⟩
  · exact ⟨⟨fun c => c = s⟩,rfl,fun bad => different bad.symm⟩
-- Recording an unanswered step is not evidence for the target fact.
theorem debt_record_not_transport (k : Kind) (t r : String) : ∃ w, holds (.debt r) w ∧ ¬ fact k t w := by
  cases k
  · exact ⟨⟨fun _ => True⟩,trivial,fun bad => bad trivial⟩
  · exact ⟨⟨fun _ => False⟩,trivial,id⟩

def str (json : Json) (key : String) : Except String String := do (← json.getObjVal? key).getStr?
def nullable (json : Json) (key : String) : Except String (Option String) := do
  match ← json.getObjVal? key with | .null => return none | v => return some (← v.getStr?)
def decodeInput (caseId : String) (json : Json) : Except String Input := do
  if caseId == "GP-A01" then
    Decoder.exactFields json ["context","target_context","warrant"]
    if (← str json "warrant") != "field-specific obstruction" then throw "unknown warrant"
    let s ← str json "context"; let t ← str json "target_context"
    return ⟨.empty,s,t,if s == t then "IDENTITY" else "BASE_EXTENSION",none,.license,none⟩
  if caseId == "GP-A08a" then
    Decoder.exactFields json ["source_context","target_context","extra_certificate"]
    let s ← str json "source_context"; let t ← str json "target_context"
    return ⟨.empty,s,t,if s == t then "IDENTITY" else "SPECIALIZATION",← nullable json "extra_certificate",.license,none⟩
  if caseId == "GP-X283" then
    Decoder.exactFields json ["variables","equations","source_universe","target_universe","relation","question","debt_reason"]
    let _ ← (← (← json.getObjVal? "variables").getArr?).toList.mapM Json.getStr?
    let _ ← (← (← json.getObjVal? "equations").getArr?).toList.mapM Json.getStr?
    if (← str json "relation") != "UNTYPED" then throw "unsupported relation"
    let q ← match ← str json "question" with
      | "license_nonempty_along" => pure Question.license | "record_step" => pure Question.record
      | _ => throw "unknown question"
    return ⟨.nonempty,← str json "source_universe",← str json "target_universe","UNTYPED",none,q,
      some (← str json "debt_reason")⟩
  if caseId == "GP-X14" then
    Decoder.exactFields json ["coefficient_domain","point_universe","claimed_field"]
    let domain ← str json "coefficient_domain"; let t ← str json "claimed_field"
    let s := (← nullable json "point_universe").getD s!"unanchored combinatorial objects over {domain}"
    return ⟨.empty,s,t,if s == t then "IDENTITY" else "UNANCHORED",none,.license,none⟩
  throw "uncommissioned fixture"

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

def run (text source mode : String) : Except String Json := do
  let literal ← Decoder.parseUnique text
  Decoder.exactFields literal ["schema_version","id","seed","title","situation","inputs",
    "attempted_conclusion","expected","scope_or_region","sources"]
  if (← (← literal.getObjVal? "schema_version").getNat?) != 1 then throw "unsupported fixture schema"
  let caseId ← (← literal.getObjVal? "id").getStr?
  let inputs ← literal.getObjVal? "inputs"
  let i ← decodeInput caseId inputs
  let bound := literal.compress
  if !(["normal","reverse","duplicates","reverse_duplicates","withheld_source"].contains mode) then throw "unknown control mode"
  let records := (if mode == "withheld_source" then [] else [sourceW i source bound]) ++ [transportW i source bound] ++
    (if i.direct.isSome then [directW i source bound] else []) ++
    (if i.debt.isSome then [debtW i source bound] else []) ++ [custodyW i source bound]
  let mut events := records.flatMap fun w => [.current ⟨w.claim,w.version,w.binding⟩,.warrant w]
  if mode == "reverse" || mode == "reverse_duplicates" then events := events.reverse
  if mode == "duplicates" || mode == "reverse_duplicates" then events := events ++ events
  let state ← fold (admission i source bound) events
  let asked := if i.question == .record then 3 else 1
  return Json.mkObj [("case",toJson caseId),("source_digest",toJson source),("mode",toJson mode),
    ("literal_fixture",literal),("literal_inputs",inputs),("bound_literal",toJson bound),
    ("kind",toJson (kindName i.kind)),("source_context",toJson i.source),("target_context",toJson i.target),
    ("relation",toJson i.relation),("direct_target_warrant",toJson i.direct),("debt",toJson i.debt),
    ("asked_claim",toJson asked),("actual_license_check",toJson (licensed i)),
    ("state",stateJson state),("snapshot",snapshotJson state.snapshot)]

#print axioms source_given
#print axioms direct_given
#print axioms identity_transport_sound
#print axioms debt_is_only_a_record
#print axioms actual_base_sound
#print axioms actual_validator_sound
#print axioms actual_fold_held_sound
#print axioms held_target_fact
#print axioms context_change_not_transported
#print axioms debt_record_not_transport
end ContextReach

def main (args : List String) : IO UInt32 := do
  match args with
  | [path,digest,mode] =>
    let result := ContextReach.run (← IO.FS.readFile path) digest mode
    IO.println (match result with
      | .ok output => output.compress
      | .error e => (Lean.Json.mkObj [("status",Lean.toJson "MALFORMED"),("error",Lean.toJson e)]).compress)
    return 0
  | _ => return 2
