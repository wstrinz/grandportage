import GPProfile.UDG

/-!
The DECIDE goal held by the Kernel (release plan A2, [A2-GOAL-STATEMENT-DESIGN.md](../../../docs/A2-GOAL-STATEMENT-DESIGN.md)).
Statement data and the executable checks of its three rules and its one receipt. The binding gives
the meanings over `EuclideanSpace ℝ (Fin 2)`, with Q(n, m) := some `n` points have at least `m`
unit distances (`GPBinding.Real.GoalSound`):

- `goal n m true` is Q(n, m); `goal n m false` is ¬Q(n, m);
- `cover n m L` is `CoverComplete n m L`, the graphs of `L` read on `Fin n` through `UDG.Data`;
- `spine n m L` is `CoverComplete n m L → ¬Q(n, m)`.

Checks (each only a Boolean; no Python input is trusted):

- `realizeOk`: rule `realize`, from one order-free NONEMPTY claim over ℝ whose statement is exactly
  the Lean encoder's (`UDG.Data.stmt`) for a graph on `n` vertices with at least `m` canonical edges
  (`Data.edgeList`: pairs `i < j < n`, each once, so padding the edge list adds nothing);
- `spinePremisesOk`: rule `spine`, one order-free EMPTY claim over ℝ per graph of `L`, in order, each
  exactly the encoder's statement for that graph (gauged or not: the gauge loses no points);
- `decideOk`: rule `decide`, `spine n m L` and `cover n m L` with identical `n`, `m` and `L`;
- `coverAllCheck`: receipt `cover_all`, every labelled graph on `n` vertices with at least `m` edges
  is among `L`. It never holds a cover by a named premise.
-/

namespace GPProfile.Real
open GPProfile

/-- A graph on `0, …, n - 1` as an edge list, read through `UDG.Data` (`Data.edgeList`). -/
abbrev EdgeList := List (Nat × Nat)

/-- The goal family's statements (all held at `real` scope). -/
inductive GoalStmt where
  /-- Q(n, m) when `value`, else ¬Q(n, m). -/
  | goal (n m : Nat) (value : Bool)
  /-- Every `n`-point set with at least `m` unit distances contains a unit-distance copy of a graph of `L`. -/
  | cover (n m : Nat) (graphs : List EdgeList)
  /-- If `cover n m L` then ¬Q(n, m). -/
  | spine (n m : Nat) (graphs : List EdgeList)
  deriving Repr, DecidableEq

/-- Only `goal n m true` and `goal n m false` contradict (and nothing in another family). -/
def GoalStmt.contra : GoalStmt → GoalStmt → Bool
  | .goal n m v, .goal n' m' v' => n == n' && m == m' && v != v'
  | _, _ => false

/-- The sublists of `l` with at least `m` elements (pruned when too few elements remain). -/
def sublistsGE {α : Type} : Nat → List α → List (List α)
  | m, [] => if m == 0 then [[]] else []
  | m, a :: l => if l.length + 1 < m then [] else (sublistsGE (m - 1) l).map (a :: ·) ++ sublistsGE m l

/-- `n` choose `k`. -/
def binom (n k : Nat) : Nat := (List.range k).foldl (fun acc i => acc * (n - i) / (i + 1)) 1

/-- How many labelled graphs on `n` vertices have at least `m` edges. -/
def coverCount (n m : Nat) : Nat :=
  let p := (UDG.pairs n).length
  ((List.range (p + 1)).filter (m ≤ ·)).foldl (fun acc k => acc + binom p k) 0

/-- At most this many graphs are enumerated by `coverAllCheck` (the CLI's `EXHAUSTIVE_LIMIT`). -/
def coverLimit : Nat := 100000

/-- The `cover_all` receipt: every labelled graph on `n` vertices with at least `m` edges is a graph of
`L` (compared as canonical edge lists). Refused beyond `coverLimit` graphs. -/
def coverAllCheck (n m : Nat) (L : List EdgeList) : Bool :=
  coverCount n m ≤ coverLimit &&
    (sublistsGE m (UDG.pairs n)).all fun S => L.any fun l => (UDG.Data.edgeList ⟨n, l, false⟩) == S

/-- Rule `realize`'s check on its premise's statement. -/
def realizeOk (n m : Nat) (edges : EdgeList) (gauge : Bool) (s : Stmt) : Bool :=
  decide (UDG.Data.stmt ⟨n, edges, gauge⟩ .nonempty = some s) &&
    decide (m ≤ (UDG.Data.edgeList ⟨n, edges, gauge⟩).length)

/-- An exclusion of graph `l` on `n` vertices: the encoder's EMPTY statement, ungauged or gauged. -/
def exclusionOk (n : Nat) (l : EdgeList) (s : Stmt) : Bool :=
  decide (UDG.Data.stmt ⟨n, l, false⟩ .empty = some s) || decide (UDG.Data.stmt ⟨n, l, true⟩ .empty = some s)

/-- The binomial count, checked on small values. -/
example : binom 6 6 = 1 ∧ binom 6 5 = 6 ∧ binom 6 2 = 15 ∧ binom 4 5 = 0 := by decide
example : coverCount 4 6 = 1 ∧ coverCount 4 5 = 7 ∧ coverCount 2 2 = 0 := by decide

end GPProfile.Real
