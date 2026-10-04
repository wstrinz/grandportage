import GP50.Semantics
import GP50.Runtime
import HexMvPoly

/-!
Phase 2.5e layout probe. This executable uses the Kernel and Hex's Mathlib-free polynomial
library together; the package's dependency graph contains no Mathlib. It also probes whether
`MvPoly n Rat` supports the operations 3a needs (Addendum A §3.1).
-/

namespace GPProfile.Layout
open Hex

/-- Kernel use: a trivial executable profile, so the Kernel is in the import closure. -/
def ops : GP50.Semantic.ProfileOps where
  Stmt := Unit
  Scope := Unit
  same := fun _ _ => true
  same_sound := fun _ _ _ => rfl
  le := fun _ _ => true
  contra := fun _ _ => false

abbrev PZ := MvPoly 2 Int Mono.lex
abbrev PQ := MvPoly 2 Rat Mono.lex

/-- x·y − 1 over ℤ. -/
def xyMinusOneZ : PZ := MvPoly.X 0 * MvPoly.X 1 - MvPoly.C 1
/-- (1/2)·x·y − 1 over ℚ: does the rational path have the instances 3a needs? -/
def halfXyMinusOneQ : PQ := MvPoly.C (1/2 : Rat) * MvPoly.X 0 * MvPoly.X 1 - MvPoly.C 1

end GPProfile.Layout

open GPProfile.Layout Hex in
def main : IO Unit := do
  IO.println s!"kernel ProfileOps same: {ops.same () ()}"
  IO.println s!"Z: (x*y-1)(1,1) = {MvPoly.eval (fun _ => (1 : Int)) xyMinusOneZ}"
  IO.println s!"Z: (x*y-1)(2,3) = {MvPoly.eval (fun i => if i.val = 0 then (2 : Int) else 3) xyMinusOneZ}"
  IO.println s!"Q: ((1/2)xy-1)(2,1) = {MvPoly.eval (fun i => if i.val = 0 then (2 : Rat) else 1) halfXyMinusOneQ}"
  IO.println s!"Q: identity zero test (p - p == 0) = {decide (halfXyMinusOneQ - halfXyMinusOneQ = 0)}"
