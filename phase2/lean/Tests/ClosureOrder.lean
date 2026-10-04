import GP50.ClosureOrderProofs
open GP50

private def root (id : Nat) : SupportNode := { id := id, premises := some [] }
private def dependent (id : Nat) (deps : List Nat) : SupportNode :=
  { id := id, premises := some deps }
private def blocked (id : Nat) : SupportNode := { id := id, premises := none }

-- Kernel examples exercise the theorem, not a separate executable oracle.
example (id : Nat) :
    id ∈ closure [root 0, root 1] ↔ id ∈ closure [root 1, root 0] :=
  closure_mem_iff_of_perm _ _ (List.Perm.swap ..) id

example (id : Nat) :
    id ∈ closure [root 0, dependent 1 [0], root 0] ↔
      id ∈ closure [dependent 1 [0], root 0] := by
  apply closure_mem_iff_of_node_mem_iff
  intro node
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · intro member
    rcases member with a | b | a
    · exact Or.inr a
    · exact Or.inl b
    · exact Or.inr a
  · intro member
    rcases member with b | a
    · exact Or.inr (Or.inl b)
    · exact Or.inl a

example (id : Nat) :
    id ∈ closure [dependent 0 [1], dependent 1 [0]].reverse ↔
      id ∈ closure [dependent 0 [1], dependent 1 [0]] :=
  closure_reverse_mem_iff _ id

example : 1 ∈ closure [dependent 1 [1], dependent 1 [0], root 0] := by
  apply closure_mem_of_node_subset [root 0, dependent 1 [0]]
  · intro node present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present ⊢
    rcases present with rootCase | dependentCase
    · exact Or.inr (Or.inr rootCase)
    · exact Or.inr (Or.inl dependentCase)
  · decide

private def ensure (name : String) (condition : Bool) : IO Unit := do
  if !condition then throw (IO.userError s!"FAILED: {name}")
  IO.println s!"PASS: {name}"

-- Test-only comparisons use full declarations and supported-ID sets.
private def sameDeclarations (nodes other : List SupportNode) : Bool :=
  nodes.all other.contains && other.all nodes.contains
private def sameSupport (nodes other : List SupportNode) : Bool :=
  let left := closure nodes
  let right := closure other
  left.all right.contains && right.all left.contains
private def equivalent (nodes other : List SupportNode) : Bool :=
  sameDeclarations nodes other && sameSupport nodes other

private def choices (id : Nat) : List SupportNode :=
  [blocked id, root id, dependent id [0], dependent id [1],
   dependent id [2], dependent id [0,1], dependent id [1,2], dependent id [99]]
private def graphs (ids : List Nat) : List (List SupportNode) :=
  match ids with
  | [] => [[]]
  | id :: rest => (choices id).flatMap fun node => (graphs rest).map (node :: ·)
private def orderProperties (nodes : List SupportNode) : Bool :=
  equivalent nodes nodes.reverse &&
    equivalent nodes (nodes.drop 1 ++ nodes.take 1) &&
    equivalent nodes (nodes ++ nodes.reverse ++ nodes)

def main : IO Unit := do
  ensure "empty graph" (orderProperties [])
  ensure "roots reorder without changing supported membership"
    (sameSupport [root 0, root 1] [root 1, root 0])
  ensure "list representation can reorder while membership stays equal"
    (closure [root 0, root 1] != closure [root 1, root 0])
  let chain := (List.range 256).map fun id =>
    if id == 0 then root id else dependent id [id-1]
  ensure "256-step chain and reversed chain have equal support"
    (equivalent chain chain.reverse && (closure chain.reverse).contains 255)
  ensure "cyclic graph reversal does not bootstrap support"
    (equivalent [dependent 0 [1], dependent 1 [0]]
      [dependent 1 [0], dependent 0 [1]] &&
      closure [dependent 1 [0], dependent 0 [1]] == [])
  let seeded := [dependent 0 [1], dependent 1 [0], root 0]
  ensure "seeded cycle order independence" (orderProperties seeded)
  let alternatives := [blocked 0, root 0, dependent 1 [0,99], dependent 1 [0]]
  ensure "duplicate-ID alternative declarations reorder faithfully"
    (orderProperties alternatives && (closure alternatives).contains 1)
  ensure "repeating every declaration changes the fuel bound but not support"
    (equivalent alternatives (alternatives ++ alternatives ++ alternatives))
  ensure "duplicate multiplicity can differ unequally by declaration"
    (equivalent [root 0, dependent 1 [0], blocked 0]
      [blocked 0, root 0, root 0, dependent 1 [0], dependent 1 [0]])
  ensure "blocked duplicate multiplicity cannot seed a cycle"
    (equivalent [blocked 0, dependent 1 [0], dependent 0 [1]]
      [dependent 0 [1], blocked 0, blocked 0, dependent 1 [0]] &&
      closure [dependent 0 [1], blocked 0, blocked 0, dependent 1 [0]] == [])
  ensure "same IDs with changed premises are outside equal-declaration assumption"
    (!sameDeclarations [root 0, dependent 1 [0]] [root 0, dependent 1 [99]] &&
      !sameSupport [root 0, dependent 1 [0]] [root 0, dependent 1 [99]])
  ensure "None versus some empty is not a permutation of declarations"
    (!sameDeclarations [blocked 0] [root 0] && !sameSupport [blocked 0] [root 0])
  let uniqueGraphs := graphs [0,1,2]
  ensure "512 unique-ID graphs preserve support under reversal rotation duplication"
    (uniqueGraphs.length == 512 && uniqueGraphs.all orderProperties)
  let duplicateGraphs := graphs [0,0,1]
  ensure "512 duplicate-ID graphs preserve support under the same transformations"
    (duplicateGraphs.length == 512 && duplicateGraphs.all orderProperties)
  IO.println "Closure graph order: 14 controls passed; 3072 transformations of 1024 graphs."

#print axioms GP50.closure_mem_iff_of_node_mem_iff
#print axioms GP50.closure_mem_iff_of_perm

