import Std
import Init.Data.Rat
namespace GP50.PolyStub
abbrev Polynomial := List (Nat × Rat)

-- Overlapping Spike.Poly/Singular cofactor wrappers supply candidate identities.
-- This tiny Mathlib-free native stub adds exact univariate replay with a proof
-- of all-exponent coefficient identity, not wire admission or geometric reach.
def coefficient (polynomial : Polynomial) (exponent : Nat) : Rat :=
  polynomial.foldl (fun sum term => if term.1 == exponent then sum + term.2 else sum) 0

def degreeBound (polynomial : Polynomial) : Nat :=
  polynomial.foldl (fun bound term => max bound term.1) 0

def multiply (left right : Polynomial) : Polynomial :=
  left.flatMap fun (i,x) => right.map fun (j,y) => (i+j,x*y)

def equal (left right : Polynomial) : Bool :=
  (List.range (max (degreeBound left) (degreeBound right) + 1)).all
    (fun exponent => coefficient left exponent == coefficient right exponent)

def replay (generators cofactors : List Polynomial) (target : Polynomial) : Bool :=
  generators.length == cofactors.length &&
    equal ((generators.zip cofactors).flatMap fun (generator,cofactor) =>
      multiply generator cofactor) target
end GP50.PolyStub

