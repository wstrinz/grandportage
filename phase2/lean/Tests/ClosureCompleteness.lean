import GP50.ClosureCompleteness
open GP50

private def root (id : Nat) : SupportNode := { id := id, premises := some [] }
private def dependent (id : Nat) (deps : List Nat) : SupportNode :=
  { id := id, premises := some deps }
private def blocked (id : Nat) : SupportNode := { id := id, premises := none }

-- Closed terms are checked by the kernel, not native_decide.
example : 2 ∈ closure [dependent 2 [1], dependent 1 [0], root 0] := by decide
example : Reachable [dependent 2 [1], dependent 1 [0], root 0] 2 :=
  (closure_mem_iff_reachable _ _).mp (by decide)
example : ¬ Reachable [dependent 0 [1], dependent 1 [0]] 0 := by
  intro reached
  have member := closure_complete _ _ reached
  exact (by decide : 0 ∉ closure [dependent 0 [1], dependent 1 [0]]) member
example : Reachable [blocked 7, dependent 7 [7], root 7] 7 :=
  (closure_mem_iff_reachable _ _).mp (by decide)

private def ensure (name : String) (condition : Bool) : IO Unit := do
  if !condition then throw (IO.userError s!"FAILED: {name}")
  IO.println s!"PASS: {name}"

-- These are test-only property checks, not additions to the support runtime.
private def saturated (nodes : List SupportNode) : Bool :=
  let result := closure nodes
  nodes.all fun node => !enabled node result || result.contains node.id

private def boundedProperties (nodes : List SupportNode) : Bool :=
  let result := closure nodes
  saturated nodes &&
    result == rounds nodes (nodes.length + 5) &&
    advance nodes result == result &&
    result.all (fun id => nodes.any (fun node => node.id == id))

private def choices (id : Nat) : List SupportNode :=
  [blocked id, root id, dependent id [0], dependent id [1],
   dependent id [2], dependent id [3], dependent id [0,1],
   dependent id [2,3], dependent id [99]]

private def graphs (ids : List Nat) : List (List SupportNode) :=
  match ids with
  | [] => [[]]
  | id :: rest => (choices id).flatMap fun node => (graphs rest).map (node :: ·)

def main : IO Unit := do
  ensure "empty graph is complete and closed" (boundedProperties [])
  ensure "blocked and absent premises cannot bootstrap"
    (closure [blocked 0, dependent 1 [99]] == [])
  ensure "self cycle cannot bootstrap" (closure [dependent 0 [0]] == [])
  ensure "mutual cycle cannot bootstrap"
    (closure [dependent 0 [1], dependent 1 [0]] == [])
  let cycle := (List.range 128).map fun id => dependent id [(id+1)%128]
  ensure "128-node unseeded cycle cannot bootstrap" (closure cycle == [])
  ensure "cycle seeded by independent duplicate-ID root reaches both IDs"
    (closure [dependent 1 [0], dependent 0 [1], root 0] == [0,1])
  ensure "blocked duplicate does not erase independent checked root"
    (closure [blocked 0, root 0, dependent 1 [0]] == [0,1])
  ensure "duplicate conjunction stays blocked without every dependency"
    (closure [root 0, dependent 1 [0,99], dependent 1 [1]] == [0])
  ensure "duplicate alternative with all premises earns support"
    (closure [root 0, dependent 1 [0,99], dependent 1 [0]] == [0,1])
  ensure "None and some [] remain distinct"
    (closure [blocked 9, root 10] == [10])
  let chain := (List.range 512).map fun id =>
    if id == 0 then root id else dependent id [id-1]
  let reversed := chain.reverse
  ensure "512-step reversed chain reaches its terminal at declared bound"
    ((closure reversed).length == 512 && (closure reversed).contains 511)
  ensure "one round below the bound misses the terminal"
    (!(rounds reversed 511).contains 511)
  ensure "long chain is saturated and matches extra rounds" (boundedProperties reversed)
  ensure "every dependency of a conjunctive branch is required"
    (closure [root 0, dependent 2 [0,1], blocked 1] == [0])
  let uniqueGraphs := graphs [0,1,2,3]
  ensure "6561 four-ID graphs satisfy saturation, extra-fuel and domain properties"
    (uniqueGraphs.length == 6561 && uniqueGraphs.all boundedProperties)
  let duplicateGraphs := graphs [0,0,1,1]
  ensure "6561 duplicate-ID graphs satisfy the same properties"
    (duplicateGraphs.length == 6561 && duplicateGraphs.all boundedProperties)
  IO.println "Closure completeness: 16 controls passed; 13122 finite graphs checked."

#print axioms GP50.closure_complete
#print axioms GP50.closure_mem_iff_reachable

