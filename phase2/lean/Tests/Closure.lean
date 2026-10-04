import GP50.ClosureProofs
open GP50
def ensureClosure (name : String) (condition : Bool) : IO Unit := do
  if !condition then throw (IO.userError s!"FAILED: {name}")
  IO.println s!"PASS: {name}"
def root (id : Nat) : SupportNode := {id := id, premises := some []}
def dependent (id : Nat) (deps : List Nat) : SupportNode :=
  {id := id, premises := some deps}
def blocked (id : Nat) : SupportNode := {id := id, premises := none}
def main : IO Unit := do
  ensureClosure "empty domain" (closure [] == [])
  ensureClosure "checked root" (closure [root 10] == [10])
  ensureClosure "blocked source" (closure [blocked 10] == [])
  ensureClosure "earned dependent" (closure [dependent 11 [10], root 10] == [10,11])
  ensureClosure "all premises necessary" (closure [root 10, dependent 11 [10,99]] == [10])
  ensureClosure "absent dependency" (closure [dependent 11 [99]] == [])
  ensureClosure "self cycle" (closure [dependent 10 [10]] == [])
  ensureClosure "two node cycle" (closure [dependent 10 [11], dependent 11 [10]] == [])
  ensureClosure "seeded cycle closes"
    ((closure [root 10, dependent 11 [10], dependent 12 [11,10]]).length == 3)
  ensureClosure "retracted root removes dependent" (closure [blocked 10, dependent 11 [10]] == [])
  ensureClosure "independent support remains"
    (closure [blocked 10, root 11, dependent 12 [11]] == [11,12])
  let chain := (List.range 128).map fun id =>
    if id == 0 then root id else dependent id [id-1]
  ensureClosure "128-step reversed chain"
    ((closure chain.reverse).length == 128 && (closure chain.reverse).contains 127)
  ensureClosure "declared bound reaches saturation"
    (advance chain.reverse (closure chain.reverse) == closure chain.reverse)
  IO.println "Support closure: 13 controls passed; reachability soundness proved, completeness proof pending."
