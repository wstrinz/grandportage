import GPProfile.Families.Base
import GPProfile.Real.Plan

/-!
The goal family's statement surface for `gp_ledger3` (release plan A2). Reading only: these build
profile data (statements, rule data, the `cover_all` receipt); every verdict is the Kernel fold's.

- `family` `goal`: `n`, `m`, `value` (`true` for Q(n, m), `false` for its negation);
- `family` `cover` or `spine`: `n`, `m`, `graphs` (a list of edge lists `[[i, j], ...]`);
- each at `context` `real`;
- rules `realize` (`edges`, optional `gauge`), `spine` and `decide`; certificate `cover_all`.
-/

namespace GPProfile.Real.GoalSurface
open Lean GPProfile GPProfile.Families GPProfile.Real

def edgeOf (e : Json) : Except String (Nat × Nat) := do
  match (← e.getArr?).toList with
  | [a, b] => pure (← a.getNat?, ← b.getNat?)
  | _ => throw "an edge is [i, j]"

def edgesOf (j : Json) : Except String EdgeList := do (← j.getArr?).toList.mapM edgeOf

def natOf (c : Json) (k : String) : Except String Nat :=
  need ((obj? c k).bind (·.getNat?.toOption)) s!"a goal-family claim has a natural number {k}"

/-- The goal family's keys beyond the 3b claim keys. -/
def keys : List String := ["n", "m", "value", "graphs"]

/-- A goal-family statement (`goal`, `cover`, `spine`), or `none` for another family. -/
def stmtOf? (fam : String) (c : Json) : Option (Except String Stmt3) :=
  let graphs : Except String (List EdgeList) := match obj? c "graphs" with
    | some (.arr gs) => gs.toList.mapM edgesOf
    | _ => throw "a cover or spine claim has a list of graphs"
  match fam with
  | "goal" => some do
    let v ← need ((obj? c "value").bind (·.getBool?.toOption)) "a goal claim has a Boolean value"
    pure (.goal (.goal (← natOf c "n") (← natOf c "m") v))
  | "cover" => some do pure (.goal (.cover (← natOf c "n") (← natOf c "m") (← graphs)))
  | "spine" => some do pure (.goal (.spine (← natOf c "n") (← natOf c "m") (← graphs)))
  | _ => none

/-- A goal rule (`realize`, `spine`, `decide`), or `none` for another rule type. -/
def ruleOf? (rule : Json) (premises : List Nat) : Option (Except String Support3) :=
  match str? rule "type" with
  | some "realize" => some do
    let edges ← match obj? rule "edges" with
      | some j => edgesOf j
      | none => throw "realize names its graph's edges"
    let gauge := ((obj? rule "gauge").bind (·.getBool?.toOption)).getD false
    pure (.rule (.realize edges gauge) premises)
  | some "spine" => some (pure (.rule .spine premises))
  | some "decide" => some (pure (.rule .decide premises))
  | _ => none

end GPProfile.Real.GoalSurface
