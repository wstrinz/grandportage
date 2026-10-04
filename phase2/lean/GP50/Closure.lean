import Std
namespace GP50
structure SupportNode where
  id : Nat
  premises : Option (List Nat)
  deriving Repr, BEq, DecidableEq
-- None is blocked; some [] is a root AFTER custody/checker validation.
def enabled (node : SupportNode) (reached : List Nat) : Bool :=
  match node.premises with
  | none => false
  | some deps => deps.all fun id => decide (id ∈ reached)
def advance (nodes : List SupportNode) (reached : List Nat) : List Nat :=
  (reached ++ (nodes.filter fun n => enabled n reached).map (·.id)).eraseDups
def rounds (nodes : List SupportNode) : Nat → List Nat
  | 0 => []
  | n+1 => advance nodes (rounds nodes n)
-- The bound is the declared support-domain size, not caller-selected fuel.
def closure (nodes : List SupportNode) : List Nat := rounds nodes nodes.length
inductive Reachable (nodes : List SupportNode) : Nat → Prop where
  | fire {node : SupportNode} {deps : List Nat}
    (member : node ∈ nodes) (requirements : node.premises = some deps)
    (supported : ∀ id ∈ deps, Reachable nodes id) : Reachable nodes node.id
end GP50
