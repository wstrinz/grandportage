import GP50.Entry
import GP50.Presentation
import GP50.NarrowingAdmissionProofs
namespace ConditionalTheoremTransport
open GP50 Lean GP50.Semantic

inductive Status where | opened | assumed deriving DecidableEq, BEq
def statusName : Status → String | .opened => "OPEN" | .assumed => "ASSUMED"
structure Premise where
  statement : String
  status : Status
  deriving DecidableEq, BEq
-- One conditional statement: a theorem authority or a consuming derivation edge.
structure Endpoints where
  source : String
  target : String
  premises : List Premise
  deriving DecidableEq, BEq
inductive Proposal where | retain | omitPremise | rebindTarget deriving DecidableEq, BEq
def orderEight := "Every omitted transfer term is zero below stage eight times the first live block."
def relaxedSummit := "relaxed seven-coordinate summit point"
structure Input where
  premises : List Premise
  source : String
  target : String
  proposal : Proposal

-- The pinned authority JC.AUTH.ACTUAL_BLOCK_ONE and consumer edge JC.EDGE.SLICE_TO_BLOCK_ONE_ZERO.
-- X61 removes ORDER_EIGHT_BOUNDED from the consumer edge; X62 rebinds the authority target.
def authorityOf (i : Input) : Endpoints :=
  ⟨i.source,if i.proposal = .rebindTarget then relaxedSummit else i.target,i.premises⟩
def edgeOf (i : Input) : Endpoints :=
  ⟨i.source,i.target,if i.proposal = .omitPremise then i.premises.filter (·.statement != orderEight) else i.premises⟩

-- A consuming edge carries the authority's statement only with exactly its endpoints and
-- premise records, matching pinned EDG6/EDG7: no omission, reordering, invention or discharge.
def licensed (authority edge : Endpoints) : Bool := decide (authority = edge)

theorem licensed_sound (a e : Endpoints) (ok : licensed a e = true) :
    a.source = e.source ∧ a.target = e.target ∧ ∀ p ∈ a.premises, p ∈ e.premises := by
  have same : a = e := of_decide_eq_true ok
  subst same
  exact ⟨rfl,rfl,fun _ present => present⟩

-- Arbitrary interpretations. Status is custody metadata; truth depends only on statements.
structure World where
  premise : String → Prop
  reaches : String → String → Prop
def conditional (e : Endpoints) (w : World) : Prop :=
  (∀ p ∈ e.premises, w.premise p.statement) → w.reaches e.source e.target

theorem transport_sound (a e : Endpoints) (w : World) (ok : licensed a e = true)
    (authority : conditional a w) : conditional e w := by
  rcases licensed_sound a e ok with ⟨source,target,covered⟩
  intro given
  rw [← source,← target]
  exact authority fun p present => given p (covered p present)

-- The named Lean theorem remains an explicit semantic hypothesis, never a discharge of its premises.
structure Hypotheses (i : Input) (w : World) : Prop where
  namedConditionalTheorem : conditional (authorityOf i) w

inductive Formula where
  | authority (e : Endpoints)
  | edge (e : Endpoints)
  deriving DecidableEq
def holds : Formula → World → Prop
  | .authority e, w => conditional e w
  | .edge e, w => conditional e w

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

theorem named_theorem_given (i : Input) : Means (profile i) (.authority (authorityOf i)) () :=
  fun _ present => present.namedConditionalTheorem
theorem edge_from_licensed_authority (i : Input) (e : Endpoints)
    (ok : licensed (authorityOf i) e = true)
    (authority : Means (profile i) (.authority (authorityOf i)) ()) : Means (profile i) (.edge e) () :=
  fun w present => transport_sound (authorityOf i) e w ok (authority w present)

def endpointsJson (e : Endpoints) : Json := Json.mkObj [("source",toJson e.source),("target",toJson e.target),
  ("premises",toJson (e.premises.map fun p => Json.mkObj [("statement",toJson p.statement),("status",toJson (statusName p.status))]))]
def statement : Formula → String
  | .authority e => s!"named conditional Lean theorem:{(endpointsJson e).compress}"
  | .edge e => s!"consuming conditional derivation:{(endpointsJson e).compress}"
def binding (i : Input) (source literal : String) (f : Formula) : Binding :=
  ⟨statement f,"BOTH",(endpointsJson (authorityOf i)).compress,[source,literal],
    "test-only-explicit-conditional-theorem-transport",1,1⟩
def clauses (i : Input) (e : Endpoints) (source literal : String) : List (Clause (profile i)) :=
  [⟨5,1,binding i source literal (.authority (authorityOf i)),.authority (authorityOf i),()⟩,
   ⟨1,1,binding i source literal (.edge e),.edge e,()⟩]
def authorityW (i : Input) (source literal : String) : Warrant :=
  ⟨5,5,1,binding i source literal (.authority (authorityOf i)),.receipt "supplied:named-conditional-lean-theorem"⟩
def edgeW (i : Input) (e : Endpoints) (source literal : String) : Warrant :=
  ⟨1,1,1,binding i source literal (.edge e),.derived [5] "licensed-premise-endpoint-transport"⟩
def custodyW (i : Input) (source literal : String) : Warrant :=
  ⟨100,100,1,binding i source literal (.edge (edgeOf i)),.citation literal⟩
def base (i : Input) (e : Endpoints) (source literal : String) : Admission :=
  {Admission.refuseAll with
    receipt := fun w data => decide (w = authorityW i source literal ∧ data = "supplied:named-conditional-lean-theorem")
    rule := fun w premises data =>
      decide (w = edgeW i e source literal ∧ premises = [authorityW i source literal] ∧
        data = "licensed-premise-endpoint-transport") && licensed (authorityOf i) e}
def admission (i : Input) (e : Endpoints) (source literal : String) : Admission :=
  withNarrowing (profile i) (clauses i e source literal) (base i e source literal)

theorem registered_meaning (i : Input) (e : Endpoints) (source literal : String)
    (c : Clause (profile i)) (present : c ∈ clauses i e source literal)
    (meaning : Means (profile i) c.stmt c.scope) :
    ClaimMeaning (profile i) (clauses i e source literal) c.key := by
  refine ⟨⟨c,present,rfl⟩,?_⟩
  intro other otherPresent key
  have unique : ((clauses i e source literal).map (·.key)).Nodup := by simp [clauses]
  have same := key_unique_of_nodup (clauses i e source literal) (fun c => c.key)
    unique other c otherPresent present key
  exact same ▸ meaning

theorem actual_base_sound (i : Input) (e : Endpoints) (source literal : String) (snapshot : Snapshot)
    (unique : (snapshot.warrants.map (·.id)).Nodup) :
    BaseValidatorSound (profile i) (clauses i e source literal) (base i e source literal) snapshot := by
  constructor
  · intro w present data accepted
    simp only [base,decide_eq_true_eq] at accepted
    rcases accepted with ⟨same,_⟩
    subst w
    exact ⟨authorityW i source literal,present,rfl,registered_meaning i e source literal
      ⟨5,1,binding i source literal (.authority (authorityOf i)),.authority (authorityOf i),()⟩
      (by simp [clauses]) (named_theorem_given i)⟩
  · intro w present declaration accepted; contradiction
  · intro w present premises side accepted members truePremises
    simp only [base,Bool.and_eq_true,decide_eq_true_eq] at accepted
    rcases accepted with ⟨⟨same,samePremises,_⟩,ok⟩
    subst w; subst premises
    have at' := warrant_meaning_claim (profile i) (clauses i e source literal) snapshot unique
      (authorityW i source literal) (members _ (by simp)) (truePremises _ (by simp))
    have am := at'.2 ⟨5,1,binding i source literal (.authority (authorityOf i)),.authority (authorityOf i),()⟩
      (by simp [clauses]) rfl
    exact ⟨edgeW i e source literal,present,rfl,registered_meaning i e source literal
      ⟨1,1,binding i source literal (.edge e),.edge e,()⟩ (by simp [clauses])
      (edge_from_licensed_authority i e ok am)⟩

theorem actual_validator_sound (i : Input) (e : Endpoints) (source literal : String) (snapshot : Snapshot)
    (unique : (snapshot.warrants.map (·.id)).Nodup) :
    ValidatorSound (admission i e source literal) snapshot
      (WarrantMeaning (profile i) (clauses i e source literal) snapshot) :=
  withNarrowing_validator_sound _ _ _ snapshot unique (actual_base_sound i e source literal snapshot unique)
theorem actual_fold_held_sound (i : Input) (e : Endpoints) (source literal : String)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission i e source literal) events = .ok state)
    (heldClaim : held state claim = true) : ClaimMeaning (profile i) (clauses i e source literal) claim := by
  unfold fold at folded
  cases resolved : resolve events with
  | error err => simp [resolved] at folded
  | ok snapshot =>
    rw [resolved] at folded
    have same := Except.ok.inj folded
    subst state
    exact evaluate_held_meaning _ _ _ snapshot (resolve_warrant_ids_nodup events snapshot resolved)
      (actual_base_sound i e source literal snapshot (resolve_warrant_ids_nodup events snapshot resolved)) claim heldClaim
theorem held_edge_is_conditional (i : Input) (e : Endpoints) (source literal : String)
    (events : List Event) (state : RuntimeState)
    (folded : fold (admission i e source literal) events = .ok state)
    (heldClaim : held state 1 = true) : Means (profile i) (.edge e) () :=
  (actual_fold_held_sound i e source literal events state 1 folded heldClaim).2
    ⟨1,1,binding i source literal (.edge e),.edge e,()⟩ (by simp [clauses]) rfl

-- Holding the conditional never establishes its target while premises stay open.
theorem open_premises_not_discharged (e : Endpoints) (p : Premise) (present : p ∈ e.premises) :
    ∃ w, conditional e w ∧ ¬ w.reaches e.source e.target :=
  ⟨⟨fun _ => False,fun _ _ => False⟩,fun given => given p present,id⟩
-- Dropping a load-bearing premise asserts a strictly stronger statement.
theorem omitted_premise_not_transported (a e : Endpoints) (p : Premise) (present : p ∈ a.premises)
    (dropped : ∀ q ∈ e.premises, q.statement ≠ p.statement) :
    ∃ w, conditional a w ∧ ¬ conditional e w :=
  ⟨⟨fun s => s ≠ p.statement,fun _ _ => False⟩,
    fun given => (given p present) rfl,fun bad => bad dropped⟩
-- An authority about one endpoint says nothing about another.
theorem rebound_target_not_transported (a e : Endpoints) (different : e.target ≠ a.target) :
    ∃ w, conditional a w ∧ ¬ conditional e w :=
  ⟨⟨fun _ => True,fun _ t => t = a.target⟩,fun _ => rfl,fun bad => different (bad fun _ _ => trivial)⟩

def readStatus : String → Except String Status
  | "OPEN" => .ok .opened | "ASSUMED" => .ok .assumed | _ => .error "unknown premise status"
def decodeInput (json : Json) : Except String Input := do
  Decoder.exactFields json ["premises","source","target","proposal"]
  let premises ← (← (← json.getObjVal? "premises").getArr?).toList.mapM fun p => do
    Decoder.exactFields p ["statement","status"]
    return (⟨← (← p.getObjVal? "statement").getStr?,← readStatus (← (← p.getObjVal? "status").getStr?)⟩ : Premise)
  let proposal ← match ← (← json.getObjVal? "proposal").getStr? with
    | "retain" => pure Proposal.retain | "omit_premise" => pure Proposal.omitPremise
    | "rebind_target" => pure Proposal.rebindTarget | _ => throw "unknown transport proposal"
  return ⟨premises,← (← json.getObjVal? "source").getStr?,← (← json.getObjVal? "target").getStr?,proposal⟩

def bindingJson (b : Binding) : Json := Json.mkObj [
  ("statementHash",toJson b.statementHash),("scopeHash",toJson b.scopeHash),("modelHash",toJson b.modelHash),
  ("inputHashes",toJson b.inputHashes),("authority",toJson b.authority),
  ("authorityVersion",toJson b.authorityVersion),("kernelVersion",toJson b.kernelVersion)]
def warrantJson (w : Warrant) : Json :=
  let evidence := match w.evidence with
    | .receipt data => Json.mkObj [("kind",toJson "receipt"),("data",toJson data)]
    | .derived deps side => Json.mkObj [("kind",toJson "derived"),("premises",toJson deps),("sideReceipt",toJson side)]
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

def extraPremise : Premise := ⟨"An uncommissioned premise invented by the consuming derivation.",.assumed⟩
-- Separate controls perturb only the consuming edge or the authority's evidence form.
def controlEdge (i : Input) (mode : String) : Endpoints :=
  let e := edgeOf i
  match mode with
  | "reorder_edge_premises" => {e with premises := e.premises.reverse}
  | "duplicate_edge_premise" => {e with premises := e.premises ++ e.premises.take 1}
  | "invent_edge_premise" => {e with premises := e.premises ++ [extraPremise]}
  | "discharge_open_premises" => {e with premises := e.premises.map fun p => {p with status := .assumed}}
  | "omit_gauge_premise" => {e with premises := e.premises.dropLast}
  | "rebind_edge_source" => {e with source := relaxedSummit}
  | "rebind_edge_target" => {e with target := relaxedSummit}
  | _ => e

def run (text source mode : String) : Except String Json := do
  let literal ← Decoder.parseUnique text
  Decoder.exactFields literal ["schema_version","id","seed","title","situation","inputs",
    "attempted_conclusion","expected","scope_or_region","sources"]
  if (← (← literal.getObjVal? "schema_version").getNat?) != 1 then throw "unsupported fixture schema"
  let caseId ← (← literal.getObjVal? "id").getStr?
  if !(["GP-X60","GP-X61","GP-X62"].contains caseId) then throw "uncommissioned fixture"
  if (← (← literal.getObjVal? "attempted_conclusion").getStr?) !=
    "Retain the proposed derivation as correctly bound conditional evidence." then throw "wrong transport attempted conclusion"
  if (← (← literal.getObjVal? "scope_or_region").getStr?) != "BOTH" then throw "wrong transport scope"
  let inputs ← literal.getObjVal? "inputs"
  let i ← decodeInput inputs
  let bound := literal.compress
  if !(["normal","reverse","duplicates","reverse_duplicates","withheld_authority","wrong_binding","theorem_pointer",
    "citation_only","reorder_edge_premises","duplicate_edge_premise","invent_edge_premise","discharge_open_premises",
    "omit_gauge_premise","rebind_edge_source","rebind_edge_target"].contains mode) then throw "unknown control mode"
  let e := controlEdge i mode
  let mut a := authorityW i source bound
  if mode == "wrong_binding" then a := {a with binding := {a.binding with inputHashes := ["corrupt binding"]}}
  if mode == "theorem_pointer" then a := {a with evidence := .theoremWarrant "JC.SigmaMarkedBlockOneInstance.actual_blockOne"}
  if mode == "citation_only" then a := {a with evidence := .citation "PACKET_REPORTED_PASS"}
  let records := (if mode == "withheld_authority" then [] else [a]) ++ [edgeW i e source bound,custodyW i source bound]
  let mut events := records.flatMap fun w => [.current ⟨w.claim,w.version,w.binding⟩,.warrant w]
  if mode == "reverse" || mode == "reverse_duplicates" then events := events.reverse
  if mode == "duplicates" || mode == "reverse_duplicates" then events := events ++ events
  let state ← fold (admission i e source bound) events
  return Json.mkObj [("case",toJson caseId),("source_digest",toJson source),("mode",toJson mode),
    ("conditional",toJson true),("literal_fixture",literal),("literal_inputs",inputs),("bound_literal",toJson bound),
    ("authority",endpointsJson (authorityOf i)),("consumer_edge",endpointsJson e),
    ("actual_license_check",toJson (licensed (authorityOf i) e)),
    ("edge_dependencies",toJson ([5] : List Nat)),("state",stateJson state),("snapshot",snapshotJson state.snapshot)]

#print axioms licensed_sound
#print axioms transport_sound
#print axioms named_theorem_given
#print axioms edge_from_licensed_authority
#print axioms actual_base_sound
#print axioms actual_validator_sound
#print axioms actual_fold_held_sound
#print axioms held_edge_is_conditional
#print axioms open_premises_not_discharged
#print axioms omitted_premise_not_transported
#print axioms rebound_target_not_transported
end ConditionalTheoremTransport

def main (args : List String) : IO UInt32 := do
  match args with
  | [path,digest,mode] =>
    let result := ConditionalTheoremTransport.run (← IO.FS.readFile path) digest mode
    IO.println (match result with
      | .ok output => output.compress
      | .error e => (Lean.Json.mkObj [("status",Lean.toJson "MALFORMED"),("error",Lean.toJson e)]).compress)
    return 0
  | _ => return 2
