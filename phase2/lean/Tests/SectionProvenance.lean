import GP50.Entry
import GP50.Presentation
import GP50.NarrowingAdmissionProofs
namespace SectionProvenance
open GP50 Lean GP50.Semantic

inductive Step where | success | rejected deriving DecidableEq, BEq
inductive Mutation where | unchanged | missing | proof deriving DecidableEq, BEq
structure Input where
  sequence : List Step
  mutation : Mutation

-- Pinned v0.37 _section_representation() and the stale mutation from its test, as canonical JSON.
def checkedRep : String := "{\"eliminated\":[\"y\"],\"images\":{\"x\":\"x\",\"y\":\"x^2\"},\"method\":\"polynomial_section_v1\",\"rows\":[{\"cofactors\":[\"1\"],\"source_generator\":\"y*x-1\",\"substituted\":\"x^3-1\"},{\"cofactors\":[\"x\"],\"source_generator\":\"y^2-x\",\"substituted\":\"x^4-x\"}],\"section\":{\"y\":\"x^2\"},\"source_generators\":[\"y*x-1\",\"y^2-x\"],\"source_ring_vars\":[\"y\",\"x\"],\"target_generators\":[\"x^3-1\"],\"target_ring_vars\":[\"x\"]}"
def mutatedRep : String := "{\"eliminated\":[\"y\"],\"images\":{\"x\":\"x\",\"y\":\"x^99\"},\"method\":\"polynomial_section_v1\",\"rows\":[{\"cofactors\":[\"also_forged\"],\"source_generator\":\"y*x-1\",\"substituted\":\"totally_forged\"},{\"cofactors\":[\"x\"],\"source_generator\":\"y^2-x\",\"substituted\":\"x^4-x\"}],\"section\":{\"y\":\"x^99\"},\"source_generators\":[\"y*x-1\",\"y^2-x\"],\"source_ring_vars\":[\"y\",\"x\"],\"target_generators\":[\"x^3-1\"],\"target_ring_vars\":[\"x\"]}"
def sectionVerifier := "verify.elimination_section"
def verifiedName := "VERIFIED_SECTION"
def rejectedName := "CERTIFICATE_REJECTED"
def edgeId := "E:SOURCE->TARGET"

-- A success verdict: who checked which exact representation, and what is stored now.
structure Verdict where
  verifier : String
  verdict : String
  checked : String
  stored : Option String
  deriving DecidableEq, BEq
def storedOf : Mutation → Option String
  | .unchanged => some checkedRep | .missing => none | .proof => some mutatedRep
def bound (v : Verdict) : Bool := decide
  (v.verifier = sectionVerifier ∧ v.verdict = verifiedName ∧ v.checked = checkedRep ∧ v.stored = some v.checked)

-- Arbitrary interpretations; no section arithmetic is encoded or replayed here.
structure World where
  valid : String → Prop
  otherProposalFails : Prop
-- The registered verifier's successful check of exactly the pinned certificate, and the
-- separate rejection of a different proposal, are explicit named hypotheses.
structure Hypotheses (w : World) : Prop where
  namedSectionCheck : w.valid checkedRep
  namedRejection : w.otherProposalFails

inductive Formula where
  | storedSection (stored : Option String)
  | rejection
  deriving DecidableEq
def holds : Formula → World → Prop
  | .storedSection none, _ => False
  | .storedSection (some r), w => w.valid r
  | .rejection, w => w.otherProposalFails

def profile : Profile where
  Stmt := Formula
  Scope := Unit
  Ctx := World
  same := fun a b => decide (a = b)
  same_sound := fun _ _ h => of_decide_eq_true h
  mem := fun w _ => Hypotheses w
  le := fun _ _ => true
  le_sound := fun _ _ _ _ present => present
  Holds := holds
  contra := fun _ _ => false
  contra_sound := by intro a b c impossible; contradiction

theorem bound_stores_checked (v : Verdict) (ok : bound v = true) : v.stored = some checkedRep := by
  simp only [bound,decide_eq_true_eq] at ok
  rcases ok with ⟨_,_,checked,stored⟩
  rw [stored,checked]
theorem bound_section_sound (v : Verdict) (ok : bound v = true) : Means profile (.storedSection v.stored) () := by
  intro w present
  rw [bound_stores_checked v ok]
  exact present.namedSectionCheck
theorem rejection_given : Means profile .rejection () := fun _ present => present.namedRejection

def statement : Formula → String
  | .storedSection none => s!"current exact section certificate:{edgeId}:none"
  | .storedSection (some r) => s!"current exact section certificate:{edgeId}:{r}"
  | .rejection => s!"different proposed section rejected:{edgeId}"
def binding (source literal : String) (f : Formula) : Binding :=
  ⟨statement f,"N/A",edgeId,[source,literal],"test-only-section-provenance-contract",1,1⟩
def clauses (v : Verdict) (source literal : String) : List (Clause profile) :=
  [⟨1,1,binding source literal (.storedSection v.stored),.storedSection v.stored,()⟩,
   ⟨2,1,binding source literal .rejection,.rejection,()⟩]
def receiptData (v : Verdict) : String :=
  s!"{v.verdict}:{v.verifier}:checked={v.checked}:stored={v.stored.getD "none"}"
def successW (v : Verdict) (source literal : String) : Warrant :=
  ⟨10,1,1,binding source literal (.storedSection v.stored),.receipt (receiptData v)⟩
def rejectionW (source literal : String) : Warrant :=
  ⟨20,2,1,binding source literal .rejection,.receipt s!"{rejectedName}:{sectionVerifier}:this different proposed section fails"⟩
def custodyW (source literal : String) : Warrant :=
  ⟨100,100,1,binding source literal (.storedSection none),.citation literal⟩
def base (v : Verdict) (source literal : String) : Admission :=
  {Admission.refuseAll with
    receipt := fun w data =>
      (decide (w = successW v source literal ∧ data = receiptData v) && bound v) ||
      decide (w = rejectionW source literal ∧
        data = s!"{rejectedName}:{sectionVerifier}:this different proposed section fails")}
def admission (v : Verdict) (source literal : String) : Admission :=
  withNarrowing profile (clauses v source literal) (base v source literal)

theorem registered_meaning (v : Verdict) (source literal : String)
    (c : Clause profile) (present : c ∈ clauses v source literal)
    (meaning : Means profile c.stmt c.scope) :
    ClaimMeaning profile (clauses v source literal) c.key := by
  refine ⟨⟨c,present,rfl⟩,?_⟩
  intro other otherPresent key
  have unique : ((clauses v source literal).map (·.key)).Nodup := by simp [clauses]
  have same := key_unique_of_nodup (clauses v source literal) (fun c => c.key)
    unique other c otherPresent present key
  exact same ▸ meaning

theorem actual_base_sound (v : Verdict) (source literal : String) (snapshot : Snapshot) :
    BaseValidatorSound profile (clauses v source literal) (base v source literal) snapshot := by
  constructor
  · intro w present data accepted
    simp only [base,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at accepted
    rcases accepted with ⟨⟨same,_⟩,ok⟩ | ⟨same,_⟩
    · subst w
      exact ⟨successW v source literal,present,rfl,registered_meaning v source literal
        ⟨1,1,binding source literal (.storedSection v.stored),.storedSection v.stored,()⟩
        (by simp [clauses]) (bound_section_sound v ok)⟩
    · subst w
      exact ⟨rejectionW source literal,present,rfl,registered_meaning v source literal
        ⟨2,1,binding source literal .rejection,.rejection,()⟩ (by simp [clauses]) rejection_given⟩
  · intro w present declaration accepted; contradiction
  · intro w present premises side accepted; contradiction

theorem actual_validator_sound (v : Verdict) (source literal : String) (snapshot : Snapshot)
    (unique : (snapshot.warrants.map (·.id)).Nodup) :
    ValidatorSound (admission v source literal) snapshot
      (WarrantMeaning profile (clauses v source literal) snapshot) :=
  withNarrowing_validator_sound _ _ _ snapshot unique (actual_base_sound v source literal snapshot)
theorem actual_fold_held_sound (v : Verdict) (source literal : String)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission v source literal) events = .ok state)
    (heldClaim : held state claim = true) : ClaimMeaning profile (clauses v source literal) claim := by
  unfold fold at folded
  cases resolved : resolve events with
  | error err => simp [resolved] at folded
  | ok snapshot =>
    rw [resolved] at folded
    have same := Except.ok.inj folded
    subst state
    exact evaluate_held_meaning _ _ _ snapshot (resolve_warrant_ids_nodup events snapshot resolved)
      (actual_base_sound v source literal snapshot) claim heldClaim
theorem held_section_is_valid_stored (v : Verdict) (source literal : String)
    (events : List Event) (state : RuntimeState)
    (folded : fold (admission v source literal) events = .ok state)
    (heldClaim : held state 1 = true) : Means profile (.storedSection v.stored) () :=
  (actual_fold_held_sound v source literal events state 1 folded heldClaim).2
    ⟨1,1,binding source literal (.storedSection v.stored),.storedSection v.stored,()⟩ (by simp [clauses]) rfl

-- A successful check of the pinned certificate says nothing about an altered stored object.
theorem mutated_certificate_not_covered : ∃ w : World, Hypotheses w ∧ ¬ w.valid mutatedRep :=
  ⟨⟨fun r => r = checkedRep,True⟩,⟨rfl,trivial⟩,by simp [mutatedRep,checkedRep]⟩
-- A verdict with no stored proof object has no admissible meaning.
theorem missing_object_has_no_meaning : ¬ Means profile (.storedSection none) () := by
  intro means
  exact means ⟨fun r => r = checkedRep,True⟩ ⟨rfl,trivial⟩
-- A rejection of another proposal, without the named section check, establishes no certificate.
theorem rejection_is_not_section : ∃ w : World, w.otherProposalFails ∧ ¬ w.valid checkedRep :=
  ⟨⟨fun _ => False,True⟩,trivial,id⟩

def decodeInput (json : Json) : Except String Input := do
  Decoder.exactFields json ["sequence","mutation"]
  let sequence ← (← (← json.getObjVal? "sequence").getArr?).toList.mapM fun s => do
    match ← s.getStr? with
    | "success" => pure Step.success | "rejected" => pure Step.rejected | _ => throw "unknown verdict step"
  let mutation ← match ← json.getObjVal? "mutation" with
    | .null => pure Mutation.unchanged
    | value => match ← value.getStr? with
      | "missing" => pure Mutation.missing | "proof" => pure Mutation.proof | _ => throw "unknown mutation"
  return ⟨sequence,mutation⟩

def bindingJson (b : Binding) : Json := Json.mkObj [
  ("statementHash",toJson b.statementHash),("scopeHash",toJson b.scopeHash),("modelHash",toJson b.modelHash),
  ("inputHashes",toJson b.inputHashes),("authority",toJson b.authority),
  ("authorityVersion",toJson b.authorityVersion),("kernelVersion",toJson b.kernelVersion)]
def warrantJson (w : Warrant) : Json :=
  let evidence := match w.evidence with
    | .receipt data => Json.mkObj [("kind",toJson "receipt"),("data",toJson data)]
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
  if !(["GP-X173","GP-X174","GP-X175","GP-X176"].contains caseId) then throw "uncommissioned fixture"
  if (← (← literal.getObjVal? "attempted_conclusion").getStr?) !=
    "Use a current exact section certificate for contraction." then throw "wrong section attempted conclusion"
  let inputs ← literal.getObjVal? "inputs"
  let i ← decodeInput inputs
  let bound' := literal.compress
  if !(["normal","reverse","duplicates","reverse_duplicates","groebner_stamp","rejected_verdict_stamp",
    "rejection_as_retraction"].contains mode) then throw "unknown control mode"
  let mut v : Verdict := ⟨sectionVerifier,verifiedName,checkedRep,storedOf i.mutation⟩
  if mode == "groebner_stamp" then v := {v with verifier := "verify.elimination_groebner"}
  if mode == "rejected_verdict_stamp" then v := {v with verdict := rejectedName}
  let records := (i.sequence.eraseDups.map fun
    | .success => successW v source bound' | .rejected => rejectionW source bound') ++ [custodyW source bound']
  let mut events := records.flatMap fun w => [.current ⟨w.claim,w.version,w.binding⟩,.warrant w]
  -- Contrast only: an explicit targeted retraction, unlike a rejection record, does remove support.
  if mode == "rejection_as_retraction" then events := events ++ [.retract 10]
  if mode == "reverse" || mode == "reverse_duplicates" then events := events.reverse
  if mode == "duplicates" || mode == "reverse_duplicates" then events := events ++ events
  let state ← fold (admission v source bound') events
  return Json.mkObj [("case",toJson caseId),("source_digest",toJson source),("mode",toJson mode),
    ("literal_fixture",literal),("literal_inputs",inputs),("bound_literal",toJson bound'),
    ("checked_representation",toJson checkedRep),("stored_representation",toJson v.stored),
    ("verifier",toJson v.verifier),("verdict",toJson v.verdict),("actual_binding_check",toJson (bound v)),
    ("state",stateJson state),("snapshot",snapshotJson state.snapshot)]

#print axioms bound_stores_checked
#print axioms bound_section_sound
#print axioms rejection_given
#print axioms actual_base_sound
#print axioms actual_validator_sound
#print axioms actual_fold_held_sound
#print axioms held_section_is_valid_stored
#print axioms mutated_certificate_not_covered
#print axioms missing_object_has_no_meaning
#print axioms rejection_is_not_section
end SectionProvenance

def main (args : List String) : IO UInt32 := do
  match args with
  | [path,digest,mode] =>
    let result := SectionProvenance.run (← IO.FS.readFile path) digest mode
    IO.println (match result with
      | .ok output => output.compress
      | .error e => (Lean.Json.mkObj [("status",Lean.toJson "MALFORMED"),("error",Lean.toJson e)]).compress)
    return 0
  | _ => return 2
