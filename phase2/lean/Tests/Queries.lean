import GP50.Queries
import GP50.BoundReplay
open GP50 GP50.Span GP50.Queries

private def binding : Binding :=
  ⟨"query-span-x", "formal-Q", "Q[x]", ["x"], "span-test-stub", 1, 1⟩
private def clause (key : Nat) : Clause := ⟨key, 1, binding, [[(1,1)]], [(1,1)]⟩
private def receipt (key : Nat) : Receipt := ⟨s!"good-{key}", key, 1, binding, [[(0,1)]]⟩
private def admitted : Admission := Span.admission ([1,2,3].map clause) ([1,2,3].map receipt)
private def root (id claim : Nat) : Warrant := ⟨id, claim, 1, binding, .receipt s!"good-{claim}"⟩
private def eventsFor (ws : List Warrant) : List Event :=
  ws.flatMap fun w => [.current ⟨w.claim, w.version, w.binding⟩, .warrant w]
private def getState (events : List Event) (admission : Admission := admitted) : IO RuntimeState :=
  match GP50.fold admission events with
  | .ok state => pure state
  | .error error => throw (IO.userError error)
private def ensure (counter : IO.Ref Nat) (name : String) (condition : Bool) : IO Unit := do
  if !condition then throw (IO.userError s!"FAILED: {name}")
  counter.modify (· + 1)
  IO.println s!"PASS: {name}"
private def reversed {α : Type} (values : List α) : List α := values.reverse
private def reasons (admission : Admission) (state : RuntimeState) (claim id : Nat) : List Reason :=
  ((whyNot admission state claim).warrants.find? fun w => w.id == id).map (·.reasons) |>.getD []

-- Explicit test seam: only rule/narrow capabilities are replaced to exercise
-- dependency paths. Receipt roots still use the actual Span validator.
private def dependencySeam : Admission :=
  {admitted with rule := fun _ _ _ => true, narrow := fun _ _ => true}

def main : IO Unit := do
  let counter ← IO.mkRef 0
  let check := ensure counter
  let one := root 10 1
  let supported ← getState (eventsFor [one])
  check "actual Span receipt holds and has no why-not reason"
    (whyNot admitted supported 1 == ⟨1, true, [⟨10, true, []⟩]⟩)
  check "absent claim has no fabricated warrant"
    (whyNot admitted supported 999 == ⟨999, false, []⟩)
  check "domain registration is not caller claiming"
    (earned supported [] [] [] == [⟨1, []⟩])
  check "explicit caller claimed key excludes earned"
    (earned supported [1] [(1,[7])] [7] == [])
  check "unknown claimed keys do not suppress held earned"
    (earned supported [999] [] [] == [⟨1, []⟩])
  check "metadata cannot create an unheld earned key"
    (earned supported [] [(999,[1,2,3])] [1,2,3] == [⟨1, []⟩])
  let noEvidence : List Evidence :=
    [.receipt "unknown", .theoremWarrant "good-1", .citation "good-1", .assertion,
     .attempt .absent, .attempt .failed, .attempt .timeout, .derived [] "unregistered"]
  for evidence in noEvidence do
    let state ← getState (eventsFor [{one with evidence}])
    check s!"opaque refusal diagnostic {repr evidence}"
      (whyNot admitted state 1 == ⟨1, false, [⟨10, false, [.refusedOrUnregisteredEvidence]⟩]⟩)
  let noCurrent ← getState [.declareClaim 1, .warrant one]
  check "inactive missing current custody is not validator rejection"
    (reasons admitted noCurrent 1 10 == [.inactiveCustody])
  let retracted ← getState (eventsFor [one] ++ [.retract 10])
  check "targeted retraction reports inactive custody"
    (reasons admitted retracted 1 10 == [.inactiveCustody])
  check "retracted root absent from earned" (earned retracted [] [(1,[8])] [8] == [])
  let stale ← getState (eventsFor [one] ++ [.current ⟨1, 2, binding⟩])
  check "explicit newer current version makes old custody inactive"
    (reasons admitted stale 1 10 == [.inactiveCustody])
  let changed ← getState (eventsFor [one] ++
    [.current ⟨1, 2, {binding with inputHashes := ["changed"]}⟩])
  check "changed current identity reports inactive custody"
    (reasons admitted changed 1 10 == [.inactiveCustody])
  let independent ← getState (eventsFor [one, root 11 1] ++ [.retract 10])
  check "held status survives one inactive independent warrant"
    (whyNot admitted independent 1 == ⟨1, true,
      [⟨10, false, [.inactiveCustody]⟩, ⟨11, true, []⟩]⟩)
  let failed := {root 11 1 with evidence := .attempt .failed}
  let retry ← getState (eventsFor [one, failed])
  check "failed retry diagnostic coexists with actual held support"
    (whyNot admitted retry 1 == ⟨1, true,
      [⟨10, true, []⟩, ⟨11, false, [.refusedOrUnregisteredEvidence]⟩]⟩)
  let replacement ← getState (eventsFor [one, root 11 1] ++ [.supersede 10 11])
  check "old successor custody inactive and successful successor supported"
    (whyNot admitted replacement 1 == ⟨1, true,
      [⟨10, false, [.inactiveCustody]⟩, ⟨11, true, []⟩]⟩)
  let failedReplacement ← getState (eventsFor [one, failed] ++ [.supersede 10 11])
  check "failed successor never inherits old support"
    (!GP50.held failedReplacement 1 &&
      reasons admitted failedReplacement 1 11 == [.refusedOrUnregisteredEvidence])

  let absent := {one with evidence := .derived [99,98,99] "side"}
  let missing ← getState (eventsFor [absent])
  check "missing premise records are distinct and sorted"
    (reasons admitted missing 1 10 == [.missingPremiseRecord 98, .missingPremiseRecord 99])
  let blocked := {root 20 2 with evidence := .assertion}
  let dependent := {one with evidence := .derived [20,20] "side"}
  let unregistered ← getState (eventsFor [dependent, blocked])
  check "present unsupported premise differs from missing record"
    (reasons admitted unregistered 1 10 ==
      [.refusedOrUnregisteredEvidence, .unsupportedPremise 20])
  let mixed := {one with evidence := .derived [99,20,99,20] "side"}
  let mixedState ← getState (eventsFor [mixed, blocked]) dependencySeam
  check "test seam keeps physical absence separate from unsupported records"
    (reasons dependencySeam mixedState 1 10 ==
      [.missingPremiseRecord 99, .unsupportedPremise 20])
  let supportedDependency ← getState (eventsFor [dependent, root 20 2]) dependencySeam
  check "test seam actual closure admits supported derived dependency"
    (whyNot dependencySeam supportedDependency 1 == ⟨1, true, [⟨10, true, []⟩]⟩)
  let unsupportedDependency ← getState (eventsFor [dependent, blocked]) dependencySeam
  check "test seam admitted rule blocked only by unsupported premise"
    (reasons dependencySeam unsupportedDependency 1 10 == [.unsupportedPremise 20])
  let withdrawnDependency ← getState
    (eventsFor [dependent, root 20 2] ++ [.retract 20]) dependencySeam
  check "test seam premise withdrawal removes dependent support"
    (reasons dependencySeam withdrawnDependency 1 10 == [.unsupportedPremise 20])
  let narrowMissing ← getState (eventsFor [{one with evidence := .narrow 99}]) dependencySeam
  check "test seam narrowing names an absent premise record"
    (reasons dependencySeam narrowMissing 1 10 == [.missingPremiseRecord 99])
  let narrowBlocked ← getState (eventsFor [{one with evidence := .narrow 20}, blocked]) dependencySeam
  check "test seam narrowing distinguishes present unsupported premise"
    (reasons dependencySeam narrowBlocked 1 10 == [.unsupportedPremise 20])
  let cycle ← getState (eventsFor [{one with evidence := .derived [10] "side"}]) dependencySeam
  check "test seam cycle reports unsupported premise and never bootstraps"
    (!GP50.held cycle 1 && reasons dependencySeam cycle 1 10 == [.unsupportedPremise 10])

  let roots := [one, root 20 2, root 30 3]
  let allHeld ← getState (eventsFor roots)
  let links : List (Nat × List Nat) :=
    [(1,[9,8,9]), (2,[7]), (1,[8]), (3,[6,7]), (999,[1,2,3])]
  let ranked : List Earned := [⟨1,[8,9]⟩, ⟨3,[6,7]⟩, ⟨2,[7]⟩]
  check "distinct open obligation count descends with claim-key ties"
    (earned allHeld [] links [6,7,8,9] == ranked)
  check "closed obligations excluded and zero-link claims retained"
    (earned allHeld [] links [7] == [⟨2,[7]⟩, ⟨3,[7]⟩, ⟨1,[]⟩])
  check "caller claimed membership is explicit and duplicates harmless"
    (earned allHeld [1,1] links [6,7,8,9] == [⟨3,[6,7]⟩, ⟨2,[7]⟩])
  check "caller annotation order and duplicates cannot change ranking"
    (earned allHeld [] (links.reverse ++ links) [9,7,6,8,9,7] == ranked)
  check "no open obligations gives stable ascending claim keys"
    (earned allHeld [] links [] == [⟨1,[]⟩, ⟨2,[]⟩, ⟨3,[]⟩])
  let before := allHeld
  let _ := earned allHeld [1] [(3,[55]), (999,[77])] [55,77]
  let _ := whyNot admitted allHeld 999
  check "caller metadata and diagnostics preserve original runtime state" (allHeld == before)
  let duplicatedState := {allHeld with claims := [3,1,2,3,1]}
  check "earned normalizes runtime claim ordering/duplicates"
    (earned duplicatedState [] links [6,7,8,9] == ranked)
  let orderedEvents := eventsFor [failed, root 11 1, one]
  -- Same IDs with conflicting contents must be resolved before queries; use
  -- distinct IDs in valid snapshots for order/duplicate controls.
  let validEvents := eventsFor [one, {root 12 1 with evidence := .attempt .failed}, root 11 1]
  let baseline ← getState validEvents
  let reordered ← getState (reversed validEvents)
  let duplicated ← getState (validEvents ++ validEvents)
  check "why-not invariant under actual event reversal"
    (whyNot admitted baseline 1 == whyNot admitted reordered 1)
  check "why-not invariant under exact duplicate events"
    (whyNot admitted baseline 1 == whyNot admitted duplicated 1)
  check "earned invariant under actual event reversal"
    (earned baseline [] links [7,8,9] == earned reordered [] links [9,8,7])
  check "earned invariant under exact duplicate events"
    (earned baseline [] links [7,8,9] == earned duplicated [] links [7,8,9])
  let reorderedRoots ← getState ((eventsFor roots).reverse)
  check "multi-key earned ranking invariant under actual event reversal"
    (earned reorderedRoots [] links [6,7,8,9] == ranked)
  let duplicatedRoots ← getState (eventsFor roots ++ eventsFor roots)
  check "multi-key earned ranking invariant under exact duplicate events"
    (earned duplicatedRoots [] links [6,7,8,9] == ranked)
  check "conflicting warrant ID remains a resolver error before diagnostics"
    (match GP50.fold admitted orderedEvents with | .error _ => true | .ok _ => false)
  IO.println s!"Queries: {← counter.get} controls passed; dependency rule/narrow paths use an explicit test seam."

#print axioms GP50.Queries.whyNot
#print axioms GP50.Queries.earned
