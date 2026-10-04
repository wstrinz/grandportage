import Lean
import Init.Data.Rat
open Lean
namespace Spike.Poly
abbrev Polynomial := List (Nat × Rat)
def coefficient (p : Polynomial) (e : Nat) : Rat :=
  p.foldl (fun s (d,c) => if d == e then s+c else s) 0
def degreeBound (p : Polynomial) : Nat := p.foldl (fun n t => max n t.1) 0
def multiply (a b : Polynomial) : Polynomial :=
  a.flatMap (fun (i,x) => b.map fun (j,y) => (i+j,x*y))
def equal (a b : Polynomial) : Bool :=
  (List.range (max (degreeBound a) (degreeBound b) + 1)).all
    (fun e => coefficient a e == coefficient b e)
def replay (generators cofactors : List Polynomial) (target : Polynomial) : Bool :=
  generators.length == cofactors.length &&
  equal ((generators.zip cofactors).flatMap fun (g,q) => multiply g q) target
def rational (j : Json) : Except String Rat := do
  let n ← j.getObjVal? "num" >>= Json.getInt?
  let d ← j.getObjVal? "den" >>= Json.getNat?
  if d == 0 then throw "zero denominator"
  return (n : Rat) / (d : Rat)
def polynomial (j : Json) : Except String Polynomial := do
  let terms ← j.getArr?
  let values ← terms.mapM fun t => do
    let e ← t.getObjVal? "exp" >>= Json.getNat?
    let c ← rational t
    return (e,c)
  return values.toList
def candidate (j : Json) : Except String Bool := do
  let gs ← j.getObjVal? "generators" >>= Json.getArr?
  let qs ← j.getObjVal? "cofactors" >>= Json.getArr?
  let t ← j.getObjVal? "target" >>= polynomial
  let g ← gs.mapM polynomial
  let q ← qs.mapM polynomial
  return replay g.toList q.toList t
end Spike.Poly
