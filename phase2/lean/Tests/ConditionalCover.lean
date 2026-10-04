import GP50.Entry
import GP50.Presentation
import GP50.AdmissionProofs
import GP50.SpanSoundnessProofs
namespace ConditionalCover
open GP50 Lean
-- Test-only interpretation of the A16 premise contract; no concrete regions invented.
structure World (Point : Type) where
  parent : Point → Prop
  branches : List (Point → Prop)
inductive Formula where
  | allListedBranchesEmpty | checkedExhaustiveCover | parentEmpty
  deriving DecidableEq
private def denotation {Point : Type} : Formula → World Point → Prop
  | .allListedBranchesEmpty, world => ∀ branch ∈ world.branches, ∀ x, ¬branch x
  | .checkedExhaustiveCover, world => ∀ x, world.parent x → ∃ branch ∈ world.branches, branch x
  | .parentEmpty, world => ∀ x, ¬world.parent x
private def Hypotheses {Point : Type} (branches coverage : Bool) (world : World Point) : Prop :=
  (branches = true → denotation .allListedBranchesEmpty world) ∧
  (coverage = true → denotation .checkedExhaustiveCover world)
def Means (Point : Type) (branches coverage : Bool) (formula : Formula) : Prop :=
  ∀ world : World Point, Hypotheses branches coverage world → denotation formula world

theorem assumption_branches_sound (Point : Type) (branches coverage : Bool)
    (given : branches = true) : Means Point branches coverage .allListedBranchesEmpty :=
  fun _ hypotheses => hypotheses.1 given
theorem assumption_cover_sound (Point : Type) (branches coverage : Bool)
    (given : coverage = true) : Means Point branches coverage .checkedExhaustiveCover :=
  fun _ hypotheses => hypotheses.2 given
theorem cover_rule_sound (Point : Type) (branches coverage : Bool)
    (empty : Means Point branches coverage .allListedBranchesEmpty)
    (cover : Means Point branches coverage .checkedExhaustiveCover) :
    Means Point branches coverage .parentEmpty := by
  intro world hypotheses x present
  rcases cover world hypotheses x present with ⟨branch, member, inBranch⟩
  exact empty world hypotheses branch member x inBranch

def binding (source : String) (claim : Nat) : Binding :=
  ⟨s!"A16-formula-{claim}", source, "anonymous parent and listed branch family", [source],
    "test-only-named-assumptions", 1, 1⟩
def root (source : String) (id claim : Nat) (name : String) : Warrant :=
  ⟨id,claim,1,binding source claim,.receipt name⟩
def left (source : String) : Warrant := root source 10 1 "given:all_listed_branches_empty"
def right (source : String) : Warrant := root source 20 2 "given:checked_exhaustive_cover"
def target (source : String) : Warrant :=
  ⟨30,3,1,binding source 3,.derived [10,20] "conditional-cover"⟩
def admission (source : String) (branches coverage : Bool) : Admission :=
  {Admission.refuseAll with
    receipt := fun w name =>
      (branches && decide (w = left source ∧ name = "given:all_listed_branches_empty")) ||
      (coverage && decide (w = right source ∧ name = "given:checked_exhaustive_cover"))
    rule := fun w premises name =>
      decide (w = target source ∧ premises = [left source,right source] ∧ name = "conditional-cover")}
def ClaimMeaning (Point : Type) (branches coverage : Bool) : Nat → Prop
  | 1 => Means Point branches coverage .allListedBranchesEmpty
  | 2 => Means Point branches coverage .checkedExhaustiveCover
  | 3 => Means Point branches coverage .parentEmpty
  | _ => False
private def Truth (Point : Type) (branches coverage : Bool) (snapshot : Snapshot) (id : Nat) : Prop :=
  ∀ w ∈ snapshot.warrants, w.id = id → ClaimMeaning Point branches coverage w.claim
private theorem lift_truth (Point : Type) (branches coverage : Bool) (snapshot : Snapshot)
    (unique : (snapshot.warrants.map (·.id)).Nodup) (w : Warrant) (present : w ∈ snapshot.warrants)
    (meaning : ClaimMeaning Point branches coverage w.claim) :
    Truth Point branches coverage snapshot w.id := by
  intro other otherPresent sameId
  have equal := key_unique_of_nodup snapshot.warrants (fun w => w.id) unique
    other w otherPresent present sameId
  exact equal ▸ meaning

theorem actual_validator_sound (Point : Type) (source : String) (branches coverage : Bool)
    (snapshot : Snapshot) (unique : (snapshot.warrants.map (·.id)).Nodup) :
    ValidatorSound (admission source branches coverage) snapshot
      (Truth Point branches coverage snapshot) := by
  constructor
  · intro w present name accepted
    simp only [admission, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at accepted
    rcases accepted with ⟨given, same, _⟩ | ⟨given, same, _⟩
    · subst w
      exact lift_truth Point branches coverage snapshot unique _ present
        (assumption_branches_sound Point branches coverage given)
    · subst w
      exact lift_truth Point branches coverage snapshot unique _ present
        (assumption_cover_sound Point branches coverage given)
  · intro w present name accepted; contradiction
  · intro w present premises name accepted members truePremises
    have checked := of_decide_eq_true accepted
    rcases checked with ⟨same, samePremises, _⟩
    subst w; subst premises
    have lp := members (left source) (by simp)
    have rp := members (right source) (by simp)
    have lt := truePremises (left source) (by simp) (left source) lp rfl
    have rt := truePremises (right source) (by simp) (right source) rp rfl
    exact lift_truth Point branches coverage snapshot unique _ present
      (cover_rule_sound Point branches coverage lt rt)
  · intro w present source sourcePresent accepted meaning; contradiction

theorem actual_fold_held_sound (Point : Type) (source : String) (branches coverage : Bool)
    (events : List Event) (state : RuntimeState) (claim : Nat)
    (folded : fold (admission source branches coverage) events = .ok state)
    (holds : held state claim = true) : ClaimMeaning Point branches coverage claim := by
  unfold fold at folded
  cases resolved : resolve events with
  | error e => simp [resolved] at folded
  | ok snapshot =>
    rw [resolved] at folded
    have same := Except.ok.inj folded
    subst state
    exact evaluate_held_truth_composition _ snapshot (Truth Point branches coverage snapshot)
      (ClaimMeaning Point branches coverage)
      (actual_validator_sound Point source branches coverage snapshot
        (resolve_warrant_ids_nodup events snapshot resolved))
      (fun w present meaning => meaning w present rfl) claim holds

example (Point : Type) (source : String) (branches coverage : Bool)
    (events : List Event) (state : RuntimeState)
    (folded : fold (admission source branches coverage) events = .ok state)
    (holds : held state 3 = true) : Means Point branches coverage .parentEmpty :=
  actual_fold_held_sound Point source branches coverage events state 3 folded holds
example (Point : Type) (branches coverage : Bool)
    (empty : Means Point branches coverage .allListedBranchesEmpty)
    (cover : Means Point branches coverage .checkedExhaustiveCover) :
    Means Point branches coverage .parentEmpty :=
  cover_rule_sound Point branches coverage empty cover

def events (source : String) : List Event :=
  [left source,right source,target source].flatMap fun w =>
    [.current ⟨w.claim,1,w.binding⟩,.warrant w]
def run (source digest : String) : Except String Json := do
  let json ← Decoder.parseUnique source
  Decoder.exactFields json ["schema_version","id","seed","title","situation","inputs",
    "attempted_conclusion","expected","scope_or_region","sources"]
  let caseId ← (← json.getObjVal? "id").getStr?
  if caseId != "GP-A16-covered" && caseId != "GP-A16-missing" then throw "uncommissioned case"
  let inputs ← json.getObjVal? "inputs"
  Decoder.exactFields inputs ["all_listed_branches_empty","checked_exhaustive_cover"]
  let branches ← (← inputs.getObjVal? "all_listed_branches_empty").getBool?
  let coverage ← (← inputs.getObjVal? "checked_exhaustive_cover").getBool?
  let state ← fold (admission digest branches coverage) (events digest)
  return Json.mkObj [("state", stateJson state),("conditional",toJson true),
    ("case",toJson caseId),("source_digest",toJson digest),("given",toJson ((if branches then ["all_listed_branches_empty"] else []) ++
      (if coverage then ["checked_exhaustive_cover"] else []))),
    ("literal_inputs",inputs),("conclusion",toJson "the parent is empty")]
#print axioms actual_validator_sound
#print axioms actual_fold_held_sound
end ConditionalCover

def main (args : List String) : IO UInt32 := do
  match args with
  | [path,digest] =>
    let result := ConditionalCover.run (← IO.FS.readFile path) digest
    IO.println (match result with
      | .ok output => output.compress
      | .error e => (Lean.Json.mkObj [("status",Lean.toJson "MALFORMED"),("error",Lean.toJson e)]).compress)
    return 0
  | _ => return 2
