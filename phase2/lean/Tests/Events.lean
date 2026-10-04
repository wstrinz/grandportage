import GP50.Events
open GP50
instance [BEq e] [BEq a] : BEq (Except e a) where
  beq
    | .ok x, .ok y => x == y
    | .error x, .error y => x == y
    | _, _ => false
def Except.isError (value : Except e a) : Bool :=
  match value with | .error _ => true | .ok _ => false
def binding (input : String := "x") : Binding :=
  { statementHash := "P", scopeHash := "S", modelHash := "M",
    inputHashes := [input], authority := "rat-cofactor", authorityVersion := 1,
    kernelVersion := 1 }
def current (version : Nat := 1) (input : String := "x") : Event :=
  .current { claim := 1, version, binding := binding input }
def warrant (id : Nat := 10) (version : Nat := 1) (input : String := "x")
    (evidence : Evidence := .receipt "unvalidated") : Event :=
  .warrant { id, claim := 1, version, binding := binding input, evidence }
def candidates (events : List Event) : Except String (List Nat) :=
  (resolve events).map eligibleIds
def permute {α : Type} : List α → List (List α)
  | [] => [[]]
  | a::as => (permute as).flatMap fun xs =>
    (List.range (xs.length + 1)).map fun n => xs.take n ++ [a] ++ xs.drop n
def ensure (name : String) (condition : Bool) : IO Unit := do
  if !condition then throw (IO.userError s!"FAILED: {name}")
  IO.println s!"PASS: {name}"
def main : IO Unit := do
  ensure "current positive custody" (candidates [current, warrant] == .ok [10])
  ensure "stale model input" (candidates [current 2 "x^2", warrant] == .ok [])
  ensure "old numeric version" (candidates [current 2, warrant] == .ok [])
  ensure "missing current binding" (candidates [warrant] == .ok [])
  ensure "exact duplicate declaration" (resolve [current, current] == resolve [current])
  ensure "exact duplicate warrant" (resolve [current, warrant, warrant] == resolve [current, warrant])
  ensure "current tie refuses" ((resolve [current, current 1 "y"]).isError)
  ensure "shared ID conflict refuses" ((resolve [current, warrant, warrant 10 1 "y"]).isError)
  ensure "highest explicit version" (candidates [current 1 "x", current 2 "y", warrant 11 2 "y"] == .ok [11])
  ensure "retraction before declaration" (candidates [.retract 10, current, warrant] == .ok [])
  ensure "neighbor survives retraction" (candidates [current, warrant, warrant 11, .retract 10] == .ok [11])
  ensure "supersession retires only predecessor" (candidates [current, warrant, warrant 11, .supersede 10 11] == .ok [11])
  ensure "split retains both successors"
    (candidates [current, warrant, warrant 11, warrant 12, .supersede 10 11, .supersede 10 12] == .ok [11,12])
  ensure "self supersession refuses" ((resolve [current, warrant, .supersede 10 10]).isError)
  ensure "missing successor refuses" ((resolve [current, warrant, .supersede 10 99]).isError)
  ensure "cycle refuses" ((resolve [current, warrant, warrant 11, .supersede 10 11, .supersede 11 10]).isError)
  ensure "withdrawal conflicts with replacement" ((resolve [current, warrant, warrant 11, .retract 10, .supersede 10 11]).isError)
  let staleFirst := [current 2 "x^2", warrant 10, warrant 11 2 "x^2"]
  ensure "stale/current arrival permutation" ((permute staleFirst).all fun xs => candidates xs == .ok [11])
  let replacement := [current, warrant, warrant 11, .supersede 10 11, .retract 99]
  ensure "120 replacement permutations" ((permute replacement).all fun xs => resolve xs == resolve replacement)
  let conflict := [current, warrant, warrant 10 1 "y"]
  ensure "conflict result permutation" ((permute conflict).all fun xs => resolve xs == resolve conflict)
  let attempts := [current, warrant, warrant 11 1 "x" (.attempt .failed)]
  ensure "failed retry cannot replace current success"
    ((permute attempts).all fun xs =>
      match resolve xs with
      | .error _ => false
      | .ok s => (s.warrants.filter fun w => live s w && match w.evidence with
        | .receipt _ => true | _ => false).map (·.id) == [10])
  ensure "binding statement/scope/model/authority exact"
    (([ {binding with statementHash := "Q"}, {binding with scopeHash := "T"},
        {binding with modelHash := "N"}, {binding with inputHashes := ["y"]},
        {binding with authority := "other"}, {binding with authorityVersion := 2},
        {binding with kernelVersion := 2} ] : List Binding).all fun b =>
      candidates [current, .warrant {
        id := 10
        claim := 1
        version := 1
        binding := b
        evidence := .receipt "unvalidated"}] == .ok [])
  IO.println "Event resolver: 22 controls passed; custody eligibility only, no held claim."
