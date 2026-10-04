import GP50.ConflictSoundnessProofs
namespace ConflictControls
open GP50 GP50.Semantic
-- Test-only profile and deliberately unsound admission model a compromised checker.
-- They are not production profiles, admitted checker contracts or corpus passes.
private def profile : Profile where
  Stmt := Bool
  Scope := List Nat
  Ctx := Nat
  same := (· == ·)
  same_sound := by intro a b h; exact eq_of_beq h
  mem := fun c scope => c ∈ scope
  le := fun a b => a.all (b.contains ·)
  le_sound := by
    intro a b c h hc
    exact List.contains_iff_mem.mp ((List.all_eq_true.mp h) c hc)
  Holds := fun stmt _ => stmt = true
  contra := fun a b => a != b
  contra_sound := by intro a b c h ha hb; subst a; subst b; contradiction
private def overlap : Overlap profile where
  Code := Nat
  witness := fun a b => a.find? (b.contains ·)
  sound := by
    intro a b k h
    exact ⟨k, List.mem_of_find?_eq_some h, List.contains_iff_mem.mp (List.find?_some h)⟩
private def unknown : Overlap profile where
  Code := Nat
  witness := fun _ _ => none
  sound := by intro a b k h; contradiction
private def binding (key : Nat) : Binding :=
  ⟨s!"statement-{key}", s!"scope-{key}", "conflict-test-only", [], "unsafe-test-seam", 1, 1⟩
private def clause (key : Nat) (stmt : Bool) (scope : List Nat) : Clause profile :=
  ⟨key, 1, binding key, stmt, scope⟩
private def roots (a b : Clause profile) : List Event :=
  [ .current ⟨a.key,1,a.binding⟩, .current ⟨b.key,1,b.binding⟩,
    .warrant ⟨10,a.key,1,a.binding,.receipt "unsafe"⟩,
    .warrant ⟨20,b.key,1,b.binding,.receipt "unsafe"⟩ ]
private def unsafeAdmission : Admission :=
  {Admission.refuseAll with receipt := fun _ _ => true}
example (p : Profile) (checker : Overlap p) (a b : Clause p)
    (left right : Nat) (finding : ConflictFinding p checker) (code : checker.Code)
    (found : assessConflict p checker a b left right = some finding)
    (inhabited : finding.witness = some code) :
    ¬(Means p a.stmt a.scope ∧ Means p b.stmt b.scope) :=
  confirmed_conflict_excludes_joint_truth p checker a b left right finding code found inhabited
example (p : Profile) (checker : Overlap p) (clauses : List (Clause p)) (state : RuntimeState) :
    (reviewRelease p checker clauses state).state.claims = state.claims :=
  congrArg RuntimeState.claims (release_preserves_complete_state p checker clauses state)
example (p : Profile) (checker : Overlap p) (clauses : List (Clause p)) (adm : Admission)
    (events : List Event) (event : Event) :
    (fold adm (event :: event :: events)).map (reviewRelease p checker clauses) =
    (fold adm (event :: events)).map (reviewRelease p checker clauses) :=
  congrArg (fun result => result.map (reviewRelease p checker clauses))
    (EventOrder.fold_duplicate adm events event)
example (p : Profile) (checker : Overlap p) (clauses : List (Clause p))
    (admission : Admission) (snapshot : Snapshot)
    (sound : ∀ claim, held (evaluate admission snapshot) claim = true → ClaimMeaning p clauses claim)
    (finding : ConflictFinding p checker)
    (present : finding ∈ conflictFindings p checker clauses (evaluate admission snapshot)) :
    finding.witness = none :=
  sound_evaluate_conflict_has_no_witness p checker clauses admission snapshot sound finding present
example (p : Profile) (checker : Overlap p) (clauses : List (Clause p))
    (base : Admission) (events : List Event) (state : RuntimeState)
    (baseSound : BaseValidatorSound p clauses base state.snapshot)
    (folded : fold (withNarrowing p clauses base) events = .ok state)
    (finding : ConflictFinding p checker)
    (present : finding ∈ conflictFindings p checker clauses state) : finding.witness = none :=
  sound_fold_conflict_has_no_witness p checker clauses base events state baseSound folded finding present
private def check (counter : IO.Ref Nat) (label : String) (ok : Bool) : IO Unit := do
  if !ok then throw (IO.userError s!"FAILED: {label}")
  counter.modify (· + 1)
  IO.println s!"PASS: {label}"
def main : IO Unit := do
  let counter ← IO.mkRef 0
  let ensure := check counter
  let a := clause 1 true [1,2]
  let b := clause 2 false [2,3]
  let state ← match GP50.fold unsafeAdmission (roots a b) with
    | .ok value => pure value | .error e => throw (IO.userError e)
  let review := reviewRelease profile overlap [a,b] state
  ensure "compromised-checker test holds both before release review" (state.claims == [1,2])
  ensure "proved inhabited overlap freezes release" (!review.allowed)
  ensure "review preserves full claims and supports" (review.state == state)
  ensure "finding retains exact support IDs and witness"
    (review.findings.any fun f => f.leftSupport == 10 && f.rightSupport == 20 &&
      f.leftClaim == 1 && f.rightClaim == 2 && @BEq.beq (Option Nat) _ f.witness (some (2 : Nat)))
  let unresolved := reviewRelease profile unknown [a,b] state
  ensure "unknown overlap is reported" (unresolved.findings.length == 1)
  ensure "unknown overlap does not freeze" unresolved.allowed
  ensure "unknown overlap supplies no witness" (unresolved.findings.all fun f => f.witness.isNone)
  ensure "disjoint scopes cannot freeze" (reviewRelease profile overlap [a,clause 2 false [3]] state).allowed
  ensure "empty scopes cannot supply an inhabited overlap"
    (reviewRelease profile overlap [clause 1 true [],b] state).allowed
  ensure "same statements produce no finding"
    ((reviewRelease profile overlap [a,clause 2 true [2,3]] state).findings.isEmpty)
  ensure "unsupported warrant cannot cause conflict"
    (reviewRelease profile overlap [a,b] {state with supports := [10]}).findings.isEmpty
  ensure "wrong input binding cannot cause conflict"
    (reviewRelease profile overlap [{a with binding := binding 9},b] state).findings.isEmpty
  ensure "duplicate registry keys refuse finding"
    (reviewRelease profile overlap [a,b,a] state).findings.isEmpty
  let reverse ← match GP50.fold unsafeAdmission (roots a b).reverse with
    | .ok value => pure value | .error e => throw (IO.userError e)
  ensure "release outcome agrees under event reversal"
    ((reviewRelease profile overlap [a,b] reverse).allowed == review.allowed)
  let refused ← match GP50.fold Admission.refuseAll (roots a b) with
    | .ok value => pure value | .error e => throw (IO.userError e)
  ensure "unadmitted evidence cannot seed conflict or held"
    (refused.claims.isEmpty && (reviewRelease profile overlap [a,b] refused).findings.isEmpty)
  IO.println s!"Conflict controls: {← counter.get} passed"
#print axioms confirmed_conflict_excludes_joint_truth
#print axioms release_preserves_complete_state
end ConflictControls

def main : IO Unit := ConflictControls.main
