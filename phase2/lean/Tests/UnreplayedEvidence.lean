import GP50.Entry
import GP50.Presentation
import GP50.NarrowingAdmissionProofs
import GP50.SpanSoundnessProofs
namespace UnreplayedEvidence
open GP50 Lean GP50.Semantic GP50.PolyStub

-- Minimal univariate parser over x: signed sums of c, x, x^n, c*x, c*x^n with c an integer or a/b.
def parseRat (s : String) : Except String Rat :=
  match s.splitOn "/" with
  | [n] => match n.toInt? with | some v => .ok v | none => .error "bad coefficient"
  | [n,d] => match n.toInt?, d.toNat? with
    | some a, some b => if b == 0 then .error "zero denominator" else .ok ((a : Rat) / (b : Rat))
    | _, _ => .error "bad coefficient"
  | _ => .error "bad coefficient"
def parseMonomial (s : String) : Except String (Nat × Rat) := do
  let (coeff,power) := match s.splitOn "*" with
    | [c,p] => (c,p) | [p] => if p.startsWith "x" then ("1",p) else (p,"") | _ => ("","!")
  let c ← parseRat coeff
  if power == "" then return (0,c)
  if power == "x" then return (1,c)
  match power.splitOn "^" with
  | ["x",n] => match n.toNat? with | some e => return (e,c) | none => throw "bad exponent"
  | _ => throw "unsupported monomial"
def parsePoly (s : String) : Except String Polynomial := do
  let text := String.ofList (s.toList.filter (· != ' '))
  if text.isEmpty then throw "empty polynomial"
  let mut terms : List (Bool × String) := []
  let mut current := ""
  let mut negative := false
  for ch in text.toList do
    if (ch == '+' || ch == '-') && current != "" then
      terms := terms ++ [(negative,current)]; current := ""; negative := ch == '-'
    else if ch == '-' && current == "" then negative := !negative
    else if ch == '+' && current == "" then pure ()
    else current := current.push ch
  terms := terms ++ [(negative,current)]
  terms.mapM fun (neg,t) => do
    let (e,c) ← parseMonomial t
    return (e,if neg then -c else c)
def negate (p : Polynomial) : Polynomial := p.map fun (e,c) => (e,-c)
def polyJson (p : Polynomial) : Json := toJson (p.map fun (e,c) => Json.arr #[toJson e,toJson (toString c)])

-- X229: replayable identity versus readable historical execution metadata.
def spanBinding (source literal : String) : Binding :=
  ⟨"identity x^2 = 0 in Q[x]/(x)","formal-univariate-Q","Q[x]",[source,literal],"native-span-stub",1,1⟩

-- Historical execution metadata is never a registered receipt name, so it cannot be admitted.
theorem unregistered_name_refused (clauses : List Span.Clause) (receipts : List Span.Receipt)
    (w : Warrant) (name : String) (absent : receipts.all (fun r => r.name != name) = true) :
    Span.accepts clauses receipts w name = false := by
  unfold Span.accepts
  cases h : Span.wellFormed clauses receipts
  · simp
  · simp only [Bool.true_and,List.any_eq_false]
    intro clause _ ok
    simp only [Bool.and_eq_true,List.any_eq_true] at ok
    rcases ok with ⟨_,receipt,member,fits⟩
    have different := List.all_eq_true.mp absent receipt member
    simp only [beq_iff_eq] at fits
    simp [fits.1.1.1.1] at different
theorem held_identity_is_formal_span (clauses : List Span.Clause) (receipts : List Span.Receipt)
    (events : List Event) (state : RuntimeState)
    (folded : fold (Span.admission clauses receipts) events = .ok state)
    (heldClaim : held state 1 = true) : ∀ clause ∈ clauses, clause.key = 1 → Span.FormalSpan clause :=
  (Span.fold_held_formalSpan clauses receipts events state 1 folded heldClaim).2

-- X65: a localized certificate holds only through a checked verdict on exactly the current data.
structure Stratum where
  current : String
  checked : Option String
  deriving DecidableEq, BEq
structure World where
  localEmpty : String → Prop
structure Hypotheses (s : Stratum) (w : World) : Prop where
  namedCheckedVerdict : ∀ d, s.checked = some d → w.localEmpty d
inductive Formula where | localEmpty (data : String) deriving DecidableEq
def profile (s : Stratum) : Profile where
  Stmt := Formula
  Scope := Unit
  Ctx := World
  same := fun a b => decide (a = b)
  same_sound := fun _ _ h => of_decide_eq_true h
  mem := fun w _ => Hypotheses s w
  le := fun _ _ => true
  le_sound := fun _ _ _ _ present => present
  Holds := fun | .localEmpty d, w => w.localEmpty d
  contra := fun _ _ => false
  contra_sound := by intro a b c impossible; contradiction
def current (s : Stratum) : Bool := s.checked == some s.current
theorem current_verdict_sound (s : Stratum) (ok : current s = true) : Means (profile s) (.localEmpty s.current) () := by
  intro w present
  have same : s.checked = some s.current := by simpa [current] using ok
  exact present.namedCheckedVerdict s.current same
def certBinding (s : Stratum) (source literal : String) : Binding :=
  ⟨s!"local emptiness:{s.current}","chart p, localized","LOCALIZED_UNIT_IDEAL_CERT",[source,literal],"test-only-paxis-verdict-contract",1,1⟩
def clauses (s : Stratum) (source literal : String) : List (Clause (profile s)) :=
  [⟨1,1,certBinding s source literal,.localEmpty s.current,()⟩]
def verdictData (s : Stratum) : String := s!"CERT_VERIFIED:{s.checked.getD "none"}"
def verdictW (s : Stratum) (source literal : String) : Warrant := ⟨10,1,1,certBinding s source literal,.receipt (verdictData s)⟩
def nameW (s : Stratum) (source literal : String) : Warrant :=
  ⟨20,1,1,certBinding s source literal,.citation "certificate:LOCALIZED_UNIT_IDEAL_CERT"⟩
def base (s : Stratum) (source literal : String) : Admission :=
  {Admission.refuseAll with
    receipt := fun w data => decide (w = verdictW s source literal ∧ data = verdictData s) && current s}
def admission (s : Stratum) (source literal : String) : Admission :=
  withNarrowing (profile s) (clauses s source literal) (base s source literal)
theorem actual_base_sound (s : Stratum) (source literal : String) (snapshot : Snapshot) :
    BaseValidatorSound (profile s) (clauses s source literal) (base s source literal) snapshot := by
  constructor
  · intro w present data accepted
    simp only [base,Bool.and_eq_true,decide_eq_true_eq] at accepted
    rcases accepted with ⟨⟨same,_⟩,ok⟩
    subst w
    refine ⟨verdictW s source literal,present,rfl,⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩⟩
    intro c member _
    simp only [clauses,List.mem_singleton] at member
    subst c
    exact current_verdict_sound s ok
  · intro w present declaration accepted; contradiction
  · intro w present premises side accepted; contradiction
theorem actual_fold_held_sound (s : Stratum) (source literal : String)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission s source literal) events = .ok state)
    (heldClaim : held state claim = true) : ClaimMeaning (profile s) (clauses s source literal) claim := by
  unfold fold at folded
  cases resolved : resolve events with
  | error err => simp [resolved] at folded
  | ok snapshot =>
    rw [resolved] at folded
    have same := Except.ok.inj folded
    subst state
    exact evaluate_held_meaning _ _ _ snapshot (resolve_warrant_ids_nodup events snapshot resolved)
      (actual_base_sound s source literal snapshot) claim heldClaim
-- A name alone supplies no hypothesis; a verdict on other data says nothing about the current stratum.
theorem name_alone_no_meaning (d : String) : ∃ w, Hypotheses ⟨d,none⟩ w ∧ ¬ w.localEmpty d :=
  ⟨⟨fun _ => False⟩,⟨fun _ h => by cases h⟩,id⟩
theorem stale_verdict_not_current (d old : String) (different : old ≠ d) :
    ∃ w, Hypotheses ⟨d,some old⟩ w ∧ ¬ w.localEmpty d :=
  ⟨⟨fun x => x = old⟩,⟨fun _ h => by cases h; rfl⟩,fun bad => different bad.symm⟩

def str (j : Json) (k : String) : Except String String := do (← j.getObjVal? k).getStr?
def strs (j : Json) (k : String) : Except String (List String) := do
  (← (← j.getObjVal? k).getArr?).toList.mapM Json.getStr?

def run229 (literal inputs : Json) (source mode : String) : Except String Json := do
  Decoder.exactFields inputs ["model","identity","cofactors","local_backend","historical_identity","raw_artifact","question"]
  let model ← inputs.getObjVal? "model"
  Decoder.exactFields model ["field","variables","equations"]
  if (← str model "field") != "Q" || (← strs model "variables") != ["x"] then throw "unsupported model"
  let identity ← inputs.getObjVal? "identity"
  Decoder.exactFields identity ["left","right"]
  if (← str inputs "question") != "historical_authority" then throw "unknown question"
  let generators ← (← strs model "equations").mapM parsePoly
  let target := (← parsePoly (← str identity "left")) ++ negate (← parsePoly (← str identity "right"))
  let cofactors ← match ← inputs.getObjVal? "cofactors" with
    | .null => pure none | v => pure (some (← ((← v.getArr?).toList.mapM Json.getStr?) >>= (·.mapM parsePoly)))
  let historical := s!"historical-execution:{← str inputs "historical_identity"}:{← str inputs "local_backend"}:{← str inputs "raw_artifact"}"
  let bound := literal.compress
  let b := spanBinding source bound
  let clause : Span.Clause := ⟨1,1,b,generators,target⟩
  let receipts : List Span.Receipt := match cofactors with
    | some cs => [⟨"replayed-cofactors",1,1,b,cs⟩] | none => []
  let records : List Warrant := [⟨20,1,1,b,.receipt historical⟩] ++
    (if cofactors.isSome then [⟨10,1,1,b,.receipt "replayed-cofactors"⟩] else []) ++ [⟨100,100,1,b,.citation bound⟩]
  let mut events := records.flatMap fun w => [.current ⟨w.claim,w.version,w.binding⟩,.warrant w]
  if mode == "reverse" || mode == "reverse_duplicates" then events := events.reverse
  if mode == "duplicates" || mode == "reverse_duplicates" then events := events ++ events
  let state ← fold (Span.admission [clause] receipts) events
  return Json.mkObj [("generators",toJson (generators.map polyJson)),("target",polyJson target),
    ("cofactors",match cofactors with | some cs => toJson (cs.map polyJson) | none => Json.null),
    ("historical_receipt",toJson historical),
    ("actual_replay",toJson (match cofactors with | some cs => replay generators cs target | none => false)),
    ("state",stateJson state)]

def run65 (literal inputs : Json) (source mode : String) : Except String Json := do
  Decoder.exactFields inputs ["variables","generators","guards","denominator_powers","numerator","cofactors",
    "localization_powers","membership_target","coefficient_field","point_universe","chart"]
  let bound := literal.compress
  let original := inputs.compress
  let mutated := match mode with
    | "stale_after_generator_mutation" => inputs.setObjVal! "generators"
        (toJson ["15*t^3+1","10*t*c9_11+14*p*t^2","5*c9_11^2+10*c9_11*p*t+5*p^2*t^2"])
    | "stale_after_guard_mutation" => inputs.setObjVal! "guards" (toJson ["p"])
    | _ => inputs
  let checked := if ["checked_verdict","stale_after_generator_mutation","stale_after_guard_mutation"].contains mode
    then some original else none
  let s : Stratum := ⟨mutated.compress,checked⟩
  let records := (if checked.isSome then [verdictW s source bound] else []) ++ [nameW s source bound]
  let mut events := records.flatMap fun w => [.current ⟨w.claim,w.version,w.binding⟩,.warrant w]
  if mode == "reverse" || mode == "reverse_duplicates" then events := events.reverse
  if mode == "duplicates" || mode == "reverse_duplicates" then events := events ++ events
  let state ← fold (admission s source bound) events
  return Json.mkObj [("current_stratum",toJson s.current),("checked_stratum",toJson s.checked),
    ("actual_currency_check",toJson (current s)),("state",stateJson state)]

def run (text source mode : String) : Except String Json := do
  let literal ← Decoder.parseUnique text
  Decoder.exactFields literal ["schema_version","id","seed","title","situation","inputs",
    "attempted_conclusion","expected","scope_or_region","sources"]
  if (← (← literal.getObjVal? "schema_version").getNat?) != 1 then throw "unsupported fixture schema"
  let caseId ← (← literal.getObjVal? "id").getStr?
  let inputs ← literal.getObjVal? "inputs"
  if !(["normal","reverse","duplicates","reverse_duplicates","checked_verdict","stale_after_generator_mutation",
    "stale_after_guard_mutation"].contains mode) then throw "unknown control mode"
  let body ← if caseId == "GP-X229" then run229 literal inputs source mode
    else if caseId == "GP-X65" then run65 literal inputs source mode else throw "uncommissioned fixture"
  return body.mergeObj (Json.mkObj [("case",toJson caseId),("source_digest",toJson source),("mode",toJson mode),
    ("literal_fixture",literal),("bound_literal",toJson literal.compress)])

#print axioms unregistered_name_refused
#print axioms held_identity_is_formal_span
#print axioms current_verdict_sound
#print axioms actual_base_sound
#print axioms actual_fold_held_sound
#print axioms name_alone_no_meaning
#print axioms stale_verdict_not_current
end UnreplayedEvidence

def main (args : List String) : IO UInt32 := do
  match args with
  | [path,digest,mode] =>
    let result := UnreplayedEvidence.run (← IO.FS.readFile path) digest mode
    IO.println (match result with
      | .ok output => output.compress
      | .error e => (Lean.Json.mkObj [("status",Lean.toJson "MALFORMED"),("error",Lean.toJson e)]).compress)
    return 0
  | _ => return 2
