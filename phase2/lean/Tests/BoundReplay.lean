import GP50.BoundReplayProofs
open GP50 GP50.Span GP50.PolyStub

private def binding : Binding :=
  {statementHash := "span-x", scopeHash := "formal-univariate-Q", modelHash := "Q[x]",
    inputHashes := ["x"], authority := "native-span-stub", authorityVersion := 1, kernelVersion := 1}
private def clause : Clause :=
  {key := 1, version := 1, binding, generators := [[(1,1)]], target := [(1,1),(2,1)]}
private def receipt : Receipt :=
  {name := "good", claim := 1, version := 1, binding, cofactors := [[(0,1),(1,1)]]}
private def warrant (id : Nat := 10) : Warrant :=
  {id, claim := 1, version := 1, binding, evidence := .receipt "good"}
private def currentForWarrant (w : Warrant) : Event :=
  .current {claim := w.claim, version := w.version, binding := w.binding}
private def stateMatches (clauses : List Clause) (receipts : List Receipt)
    (events : List Event) (supports claims : List Nat) : Bool :=
  match GP50.fold (Span.admission clauses receipts) events with
  | .error _ => false
  | .ok state => state.supports == supports && state.claims == claims
private def acceptedRoot (clauses : List Clause) (receipts : List Receipt) (w : Warrant)
    (name : String := "good") : Bool :=
  accepts clauses receipts w name &&
    stateMatches clauses receipts [currentForWarrant w, .warrant w] [w.id] [w.claim]
private def rejectedRoot (clauses : List Clause) (receipts : List Receipt) (w : Warrant)
    (name : String := "good") : Bool :=
  !accepts clauses receipts w name &&
    stateMatches clauses receipts [currentForWarrant w, .warrant w] [] []
private def ensure (counter : IO.Ref Nat) (name : String) (condition : Bool) : IO Unit := do
  if !condition then throw (IO.userError s!"FAILED: {name}")
  counter.modify (· + 1)
  IO.println s!"PASS: {name}"
private def permutations {α : Type} : List α → List (List α)
  | [] => [[]]
  | value :: values => (permutations values).flatMap fun xs =>
    (List.range (xs.length+1)).map fun n => xs.take n ++ [value] ++ xs.drop n

-- Kernel control for the computed duplicate-name policy, independent of Rat evaluation.
example (clauses : List Clause) (receipts : List Receipt)
    (valid : wellFormed clauses receipts = true) :
    (clauses.map (·.key)).Nodup ∧ (receipts.map (·.name)).Nodup :=
  wellFormed_nodup clauses receipts valid

def main : IO Unit := do
  let counter ← IO.mkRef 0
  let check := ensure counter
  check "native exact replay creates actual supported/held claim"
    (acceptedRoot [clause] [receipt] warrant)
  check "registry is well formed" (wellFormed [clause] [receipt])
  check "stale warrant version refuses even with matching current custody"
    (rejectedRoot [clause] [receipt] {warrant with version := 2})
  check "receipt version must match clause"
    (rejectedRoot [clause] [{receipt with version := 2}] warrant)
  check "clause version must match warrant"
    (rejectedRoot [{clause with version := 2}] [receipt] warrant)
  check "all explicitly updated version values match"
    (acceptedRoot [{clause with version := 2}] [{receipt with version := 2}]
      {warrant with version := 2})
  check "warrant claim must match registered key"
    (rejectedRoot [clause] [receipt] {warrant with claim := 2})
  check "receipt claim must match registered key"
    (rejectedRoot [clause] [{receipt with claim := 2}] warrant)
  let changedBindings : List (String × Binding) :=
    [("statementHash", {binding with statementHash := "other-statement"}),
     ("scopeHash", {binding with scopeHash := "other-scope"}),
     ("modelHash", {binding with modelHash := "other-model"}),
     ("inputHashes", {binding with inputHashes := ["x^2"]}),
     ("authority", {binding with authority := "other-validator"}),
     ("authorityVersion", {binding with authorityVersion := 2}),
     ("kernelVersion", {binding with kernelVersion := 2})]
  for (field, changed) in changedBindings do
    check s!"exact warrant binding field {field}, current custody still matches"
      (rejectedRoot [clause] [receipt] {warrant with binding := changed})
    check s!"exact clause binding field {field}"
      (rejectedRoot [{clause with binding := changed}] [receipt] warrant)
    check s!"exact receipt binding field {field}"
      (rejectedRoot [clause] [{receipt with binding := changed}] warrant)
  check "matching binding values permit replay under separate adapter contract"
    (acceptedRoot [{clause with binding := {binding with inputHashes := ["declared-by-adapter"]}}]
      [{receipt with binding := {binding with inputHashes := ["declared-by-adapter"]}}]
      {warrant with binding := {binding with inputHashes := ["declared-by-adapter"]}})
  check "mutated cofactor refuses" (rejectedRoot [clause]
    [{receipt with cofactors := [[(0,2),(1,1)]]}] warrant)
  check "mutated generator refuses" (rejectedRoot
    [{clause with generators := [[(2,1)]]}] [receipt] warrant)
  check "mutated target refuses" (rejectedRoot
    [{clause with target := [(1,2),(2,1)]}] [receipt] warrant)
  check "cofactor count mismatch refuses" (rejectedRoot [clause]
    [{receipt with cofactors := []}] warrant)
  check "configured zero polynomial-span is accepted"
    (acceptedRoot [{clause with generators := [], target := []}]
      [{receipt with cofactors := []}] warrant)
  check "rational fraction replay is bound to actual configured data"
    (acceptedRoot [{clause with generators := [[(0,(1 : Rat)/2)]], target := [(0,1)]}]
      [{receipt with cofactors := [[(0,2)]]}] warrant)
  check "unknown receipt name refuses"
    (rejectedRoot [clause] [receipt] {warrant with evidence := .receipt "missing"} "missing")
  check "missing clause refuses" (rejectedRoot [] [receipt] warrant)
  check "missing receipt refuses" (rejectedRoot [clause] [] warrant)
  check "exact duplicate clause identifier refuses"
    (rejectedRoot [clause,clause] [receipt] warrant)
  check "conflicting duplicate clause identifier refuses"
    (rejectedRoot [clause,{clause with target := []}] [receipt] warrant)
  check "exact duplicate receipt name refuses"
    (rejectedRoot [clause] [receipt,receipt] warrant)
  check "conflicting duplicate receipt name refuses"
    (rejectedRoot [clause] [receipt,{receipt with cofactors := []}] warrant)
  for evidence in [.theoremWarrant "good", .citation "good", .assertion,
      .attempt .absent, .attempt .failed, .attempt .timeout,
      .derived [] "good", .narrow 10] do
    let w := {warrant with evidence}
    check s!"receipt-only admission leaves other capability inactive {repr evidence}"
      (stateMatches [clause] [receipt] [currentForWarrant w, .warrant w] [] [])
  check "receipt acceptance cannot overcome missing current custody"
    (stateMatches [clause] [receipt] [.warrant warrant] [] [])
  check "current input mutation keeps old successful warrant stale"
    (stateMatches [clause] [receipt]
      [.current {claim := 1, version := 1, binding := {binding with inputHashes := ["new"]}},
       .warrant warrant] [] [])
  let targeted : List Event := [currentForWarrant warrant, .warrant warrant,
    .warrant (warrant 11), .retract 10]
  check "ID-targeted retraction preserves independent neighbor"
    (stateMatches [clause] [receipt] targeted [11] [1])
  check "24 targeted retraction permutations preserve result"
    ((permutations targeted).all fun events => stateMatches [clause] [receipt] events [11] [1])
  check "failed retry cannot erase prior independent success"
    (stateMatches [clause] [receipt] [currentForWarrant warrant, .warrant warrant,
      .warrant {warrant 11 with evidence := .attempt .failed}] [10] [1])
  check "retracting only failed retry preserves prior success"
    (stateMatches [clause] [receipt] [currentForWarrant warrant, .warrant warrant,
      .warrant {warrant 11 with evidence := .attempt .failed}, .retract 11] [10] [1])
  check "retracted only successful warrant leaves failed retry without support"
    (stateMatches [clause] [receipt] [currentForWarrant warrant, .warrant warrant,
      .warrant {warrant 11 with evidence := .attempt .failed}, .retract 10] [] [])
  check "explicit failed successor does not gain predecessor authority"
    (stateMatches [clause] [receipt] [currentForWarrant warrant, .warrant warrant,
      .warrant {warrant 11 with evidence := .attempt .failed}, .supersede 10 11] [] [])
  check "conflicting reuse of successful warrant ID is a resolver error"
    (match GP50.fold (Span.admission [clause] [receipt])
      [currentForWarrant warrant, .warrant warrant,
       .warrant {warrant with evidence := .attempt .failed}] with
      | .error _ => true | .ok _ => false)
  IO.println s!"BoundReplay: {← counter.get} controls passed; native formal Rat span scope."

#print axioms GP50.Span.accepts_exact_identity
#print axioms GP50.Span.accepts_unique_clause_meaning
