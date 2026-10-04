import GP50.Entry
import GP50.Presentation
import GP50.NarrowingAdmissionProofs
namespace RuleShape
open GP50 Lean GP50.Semantic

-- A registered one-step rule over named atomic statements.
structure Rule where
  name : String
  premises : List String
  concl : String
  deriving DecidableEq, BEq
structure Input where
  supplied : List String
  rules : List Rule
  goal : String
  deriving DecidableEq, BEq

def fires (T : List String) (r : Rule) : Bool := r.premises.all T.contains
def step (rules : List Rule) (T : List String) : List String := T ++ (rules.filter (fires T)).map (·.concl)
def iterate (rules : List Rule) : Nat → List String → List String
  | 0, T => T
  | n+1, T => iterate rules n (step rules T)
def closure (i : Input) : List String := iterate i.rules (i.rules.length + 1) i.supplied
def derived (i : Input) : Bool := (closure i).contains i.goal
def closed (rules : List Rule) (T : List String) : Bool := rules.all fun r => !fires T r || T.contains r.concl

structure World where
  holds : String → Prop
-- Supplied atoms and registered rules are the named hypotheses; nothing else is assumed.
structure Hypotheses (i : Input) (w : World) : Prop where
  namedSupplied : ∀ a ∈ i.supplied, w.holds a
  namedRules : ∀ r ∈ i.rules, (∀ p ∈ r.premises, w.holds p) → w.holds r.concl

theorem step_sound (i : Input) (w : World) (h : Hypotheses i w) (T : List String)
    (all : ∀ a ∈ T, w.holds a) : ∀ a ∈ step i.rules T, w.holds a := by
  intro a member
  simp only [step,List.mem_append,List.mem_map,List.mem_filter] at member
  rcases member with present | ⟨r,⟨rule,fired⟩,same⟩
  · exact all a present
  · subst same
    apply h.namedRules r rule
    intro p premise
    have inT := List.all_eq_true.mp fired p premise
    exact all p (List.contains_iff_mem.mp inT)
theorem iterate_sound (i : Input) (w : World) (h : Hypotheses i w) :
    ∀ n T, (∀ a ∈ T, w.holds a) → ∀ a ∈ iterate i.rules n T, w.holds a := by
  intro n
  induction n with
  | zero => intro T all; exact all
  | succ n ih => intro T all; exact ih (step i.rules T) (step_sound i w h T all)
theorem closure_sound (i : Input) (w : World) (h : Hypotheses i w) : ∀ a ∈ closure i, w.holds a :=
  iterate_sound i w h _ _ h.namedSupplied
-- A closed set containing every supplied atom but not the goal is a countermodel.
theorem closed_set_countermodel (i : Input) (T : List String)
    (supplied : ∀ a ∈ i.supplied, a ∈ T) (isClosed : closed i.rules T = true) (missing : i.goal ∉ T) :
    ∃ w, Hypotheses i w ∧ ¬ w.holds i.goal := by
  refine ⟨⟨fun a => a ∈ T⟩,⟨supplied,?_⟩,missing⟩
  intro r rule premises
  have each := List.all_eq_true.mp isClosed r rule
  simp only [Bool.or_eq_true,Bool.not_eq_true'] at each
  rcases each with notFired | present
  · have fired : fires T r = true := List.all_eq_true.mpr fun p member => List.contains_iff_mem.mpr (premises p member)
    rw [fired] at notFired; contradiction
  · exact List.contains_iff_mem.mp present

inductive Formula where | atom (a : String) deriving DecidableEq
def profile (i : Input) : Profile where
  Stmt := Formula
  Scope := Unit
  Ctx := World
  same := fun a b => decide (a = b)
  same_sound := fun _ _ h => of_decide_eq_true h
  mem := fun w _ => Hypotheses i w
  le := fun _ _ => true
  le_sound := fun _ _ _ _ present => present
  Holds := fun | .atom a, w => w.holds a
  contra := fun _ _ => false
  contra_sound := by intro a b c impossible; contradiction
theorem derived_goal_sound (i : Input) (ok : derived i = true) : Means (profile i) (.atom i.goal) () :=
  fun w present => closure_sound i w present i.goal (List.contains_iff_mem.mp ok)

def binding (i : Input) (source literal : String) : Binding :=
  ⟨s!"derived:{i.goal}","registered one-step rules",s!"{i.rules.length} rules",[source,literal],"test-only-rule-shape-contract",1,1⟩
def clauses (i : Input) (source literal : String) : List (Clause (profile i)) := [⟨1,1,binding i source literal,.atom i.goal,()⟩]
def goalW (i : Input) (source literal : String) : Warrant := ⟨1,1,1,binding i source literal,.receipt "registered-rule-closure"⟩
def custodyW (i : Input) (source literal : String) : Warrant :=
  ⟨100,100,1,{binding i source literal with statementHash := "custody"},.citation literal⟩
def base (i : Input) (source literal : String) : Admission :=
  {Admission.refuseAll with
    receipt := fun w data => decide (w = goalW i source literal ∧ data = "registered-rule-closure") && derived i}
def admission (i : Input) (source literal : String) : Admission :=
  withNarrowing (profile i) (clauses i source literal) (base i source literal)
theorem actual_base_sound (i : Input) (source literal : String) (snapshot : Snapshot) :
    BaseValidatorSound (profile i) (clauses i source literal) (base i source literal) snapshot := by
  constructor
  · intro w present data accepted
    simp only [base,Bool.and_eq_true,decide_eq_true_eq] at accepted
    rcases accepted with ⟨⟨same,_⟩,ok⟩
    subst w
    refine ⟨goalW i source literal,present,rfl,⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩⟩
    intro c member _
    simp only [clauses,List.mem_singleton] at member
    subst c
    exact derived_goal_sound i ok
  · intro w present declaration accepted; contradiction
  · intro w present premises side accepted; contradiction
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

def str (j : Json) (k : String) : Except String String := do (← j.getObjVal? k).getStr?
def bool (j : Json) (k : String) : Except String Bool := do (← j.getObjVal? k).getBool?
-- Each fixture schema becomes supplied atoms, registered rules and a goal.
def decodeInput (caseId : String) (j : Json) : Except String Input := do
  if caseId == "GP-A14" then
    Decoder.exactFields j ["claim_object","map_source","map_target"]
    let c ← str j "claim_object"; let s ← str j "map_source"; let t ← str j "map_target"
    return ⟨[s!"NONEMPTY {c}"],[⟨s!"inclusion {s}->{t}",[s!"NONEMPTY {s}"],s!"NONEMPTY {t}"⟩],s!"NONEMPTY {t}"⟩
  if caseId == "GP-X04" then
    Decoder.exactFields j ["checked_exhaustive_cover","all_branches_empty"]
    let cover ← bool j "checked_exhaustive_cover"; let all ← bool j "all_branches_empty"
    let branches := ["EMPTY branch-1","EMPTY branch-2"]
    return ⟨if all then branches else branches.take 1,
      if cover then [⟨"checked exhaustive partition",branches,"EMPTY parent"⟩] else [],"EMPTY parent"⟩
  if caseId == "GP-X09" then
    Decoder.exactFields j ["premise_kind","conclusion_kind","extra_rule"]
    let kind := fun (k : String) => match k with
      | "universal predicate" => Except.ok "PREDICATE" | "existence" => .ok "NONEMPTY" | "emptiness" => .ok "EMPTY"
      | _ => .error "unknown claim kind"
    let p ← kind (← str j "premise_kind"); let c ← kind (← str j "conclusion_kind")
    let pure' : Rule := ⟨"pure transport",[s!"{p} source"],s!"{p} target"⟩
    let extra ← match ← j.getObjVal? "extra_rule" with
      | .null => pure [] | v => pure [(⟨← v.getStr?,[s!"{p} target"],s!"{c} target"⟩ : Rule)]
    return ⟨[s!"{p} source"],[pure'] ++ extra,s!"{c} target"⟩
  throw "uncommissioned fixture"

def ruleJson (r : Rule) : Json := Json.mkObj [("name",toJson r.name),("premises",toJson r.premises),("concl",toJson r.concl)]
def run (text source mode : String) : Except String Json := do
  let literal ← Decoder.parseUnique text
  Decoder.exactFields literal ["schema_version","id","seed","title","situation","inputs",
    "attempted_conclusion","expected","scope_or_region","sources"]
  if (← (← literal.getObjVal? "schema_version").getNat?) != 1 then throw "unsupported fixture schema"
  let caseId ← (← literal.getObjVal? "id").getStr?
  let i ← decodeInput caseId (← literal.getObjVal? "inputs")
  if !(["normal","reverse","duplicates","reverse_duplicates"].contains mode) then throw "unknown control mode"
  let bound := literal.compress
  let records := [goalW i source bound,custodyW i source bound]
  let mut events := records.flatMap fun w => [.current ⟨w.claim,w.version,w.binding⟩,.warrant w]
  if mode == "reverse" || mode == "reverse_duplicates" then events := events.reverse
  if mode == "duplicates" || mode == "reverse_duplicates" then events := events ++ events
  let state ← fold (admission i source bound) events
  let T := closure i
  return Json.mkObj [("case",toJson caseId),("source_digest",toJson source),("mode",toJson mode),
    ("literal_fixture",literal),("bound_literal",toJson bound),("supplied",toJson i.supplied),
    ("rules",toJson (i.rules.map ruleJson)),("goal",toJson i.goal),("closure",toJson T),
    ("closure_is_closed",toJson (closed i.rules T)),("actual_derivation",toJson (derived i)),("state",stateJson state)]

#print axioms step_sound
#print axioms iterate_sound
#print axioms closure_sound
#print axioms closed_set_countermodel
#print axioms derived_goal_sound
#print axioms actual_base_sound
#print axioms actual_fold_held_sound
end RuleShape

def main (args : List String) : IO UInt32 := do
  match args with
  | [path,digest,mode] =>
    let result := RuleShape.run (← IO.FS.readFile path) digest mode
    IO.println (match result with
      | .ok output => output.compress
      | .error e => (Lean.Json.mkObj [("status",Lean.toJson "MALFORMED"),("error",Lean.toJson e)]).compress)
    return 0
  | _ => return 2
