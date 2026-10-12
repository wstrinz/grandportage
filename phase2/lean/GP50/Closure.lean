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
-- Post-G4 Track K: hash-indexed twins proved equal to the list functions they shadow. The
-- `csimp` lemmas substitute them in compiled code only; definitions and theorems are unchanged.
def eraseDupsHash.loop {α} [BEq α] [Hashable α] : List α → Std.HashSet α → List α → List α
  | [], _, bs => bs.reverse
  | a :: as, seen, bs =>
    if seen.contains a then eraseDupsHash.loop as seen bs
    else eraseDupsHash.loop as (seen.insert a) (a :: bs)
def eraseDupsHash {α} [BEq α] [Hashable α] (as : List α) : List α := eraseDupsHash.loop as ∅ []
theorem eraseDupsHash.loop_eq {α} [BEq α] [LawfulBEq α] [Hashable α] :
    ∀ (as : List α) (seen : Std.HashSet α) (bs : List α),
      (∀ x, seen.contains x = bs.any (x == ·)) →
      eraseDupsHash.loop as seen bs = List.eraseDupsBy.loop (· == ·) as bs
  | [], _, _, _ => rfl
  | a :: as, seen, bs, h => by
    simp only [eraseDupsHash.loop, List.eraseDupsBy.loop, h a]
    cases bs.any (a == ·)
    · refine eraseDupsHash.loop_eq as _ _ fun x => ?_
      simp only [Std.HashSet.contains_insert, h x, List.any_cons, BEq.comm (a := a) (b := x)]
    · exact eraseDupsHash.loop_eq as seen bs h
theorem eraseDups_eq_eraseDupsHash {α} [BEq α] [LawfulBEq α] [Hashable α] (as : List α) :
    as.eraseDups = eraseDupsHash as :=
  (eraseDupsHash.loop_eq as ∅ [] fun _ => by simp).symm
def enabledHash (node : SupportNode) (reached : Std.HashSet Nat) : Bool :=
  match node.premises with
  | none => false
  | some deps => deps.all fun id => reached.contains id
def advanceFast (nodes : List SupportNode) (reached : List Nat) : List Nat :=
  let seen := Std.HashSet.ofList reached
  eraseDupsHash (reached ++ (nodes.filter fun n => enabledHash n seen).map (·.id))
theorem enabledHash_ofList (node : SupportNode) (reached : List Nat) :
    enabledHash node (Std.HashSet.ofList reached) = enabled node reached := by
  unfold enabledHash enabled
  split <;> simp
@[csimp] theorem advance_eq_advanceFast : @advance = @advanceFast := by
  funext nodes reached
  simp only [advance, advanceFast, enabledHash_ofList, eraseDups_eq_eraseDupsHash]
def rounds (nodes : List SupportNode) : Nat → List Nat
  | 0 => []
  | n+1 => advance nodes (rounds nodes n)
-- The bound is the declared support-domain size, not caller-selected fuel.
def closure (nodes : List SupportNode) : List Nat := rounds nodes nodes.length
inductive Reachable (nodes : List SupportNode) : Nat → Prop where
  | fire {node : SupportNode} {deps : List Nat}
    (member : node ∈ nodes) (requirements : node.premises = some deps)
    (supported : ∀ id ∈ deps, Reachable nodes id) : Reachable nodes node.id
-- Post-G4 Track K: the compiled closure stops once a round adds nothing. `closure` itself is
-- unchanged; `closure_eq_closureFast` is a `csimp` lemma, so the compiler substitutes a function
-- proved equal to it, and no trust is added.
def roundsUntil (nodes : List SupportNode) : Nat → List Nat → List Nat
  | 0, reached => reached
  | fuel+1, reached =>
    let next := advance nodes reached
    if next = reached then reached else roundsUntil nodes fuel next
def closureFast (nodes : List SupportNode) : List Nat := roundsUntil nodes nodes.length []
theorem rounds_stable {nodes : List SupportNode} {k : Nat}
    (h : rounds nodes (k + 1) = rounds nodes k) : ∀ j, rounds nodes (k + j) = rounds nodes k
  | 0 => rfl
  | j+1 => by
    show advance nodes (rounds nodes (k + j)) = rounds nodes k
    rw [rounds_stable h j]
    exact h
theorem roundsUntil_rounds (nodes : List SupportNode) :
    ∀ fuel k, roundsUntil nodes fuel (rounds nodes k) = rounds nodes (k + fuel)
  | 0, _ => rfl
  | fuel+1, k => by
    simp only [roundsUntil]
    split
    · rename_i h
      exact (rounds_stable (k := k) h (fuel + 1)).symm
    · rw [show advance nodes (rounds nodes k) = rounds nodes (k + 1) from rfl,
        roundsUntil_rounds nodes fuel (k + 1)]
      congr 1
      omega
@[csimp] theorem closure_eq_closureFast : @closure = @closureFast := by
  funext nodes
  show rounds nodes nodes.length = roundsUntil nodes nodes.length (rounds nodes 0)
  rw [roundsUntil_rounds]
  simp
end GP50
