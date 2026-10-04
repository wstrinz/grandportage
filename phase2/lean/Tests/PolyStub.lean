import GP50.PolyStubProofs
open GP50.PolyStub

-- The above-bound coefficient guarantee is a kernel-checked proof example.
example : coefficient [(3,1),(1,2)] 100 = 0 :=
  coefficient_zero_above_bound _ _ (by decide)

private def ensure (counter : IO.Ref Nat) (name : String) (condition : Bool) : IO Unit := do
  if !condition then throw (IO.userError s!"FAILED: {name}")
  counter.modify (· + 1)
  IO.println s!"PASS: {name}"

-- Independent test-only coefficient expression, using filtered sum rather than foldl.
private def referenceCoefficient (polynomial : Polynomial) (exponent : Nat) : Rat :=
  ((polynomial.filter fun term => term.1 == exponent).map (·.2)).sum
private def smallPolynomials : List Polynomial :=
  let terms := (List.range 4).flatMap fun exponent =>
    ([-1,0,1,(1 : Rat)/2] : List Rat).map fun value => (exponent,value)
  [] :: (terms.map (fun term => [term]) ++
    terms.flatMap (fun first => terms.map fun second => [first,second]))
private def coefficientProperties (polynomial : Polynomial) : Bool :=
  (List.range 10).all (fun exponent =>
    coefficient polynomial exponent == referenceCoefficient polynomial exponent) &&
    coefficient polynomial (degreeBound polynomial + 1) == 0 &&
    coefficient polynomial (degreeBound polynomial + 1000) == 0

def main : IO Unit := do
  let counter ← IO.mkRef 0
  let check := ensure counter
  check "empty polynomial coefficient is zero" (coefficient [] 0 == 0)
  check "empty polynomial arbitrary exponent is zero" (coefficient [] 1000000000 == 0)
  check "zero term equals empty polynomial" (equal [(0,0)] [])
  check "high-degree zero term equals empty polynomial" (equal [(1024,0)] [])
  check "duplicate terms add exactly" (coefficient [(2,1),(2,2)] 2 == 3)
  check "duplicate terms cancel exactly" (equal [(2,1),(2,-1)] [])
  check "fractional cancellation is exact"
    (equal [(0,(1 : Rat)/2),(0,(1 : Rat)/3),(0,-(5 : Rat)/6)] [])
  check "term ordering and split coefficients do not change equality"
    (equal [(0,1),(3,2)] [(3,1),(0,1),(3,1)])
  check "coefficients at different exponents remain distinct" (!equal [(0,1)] [(1,1)])
  check "degree bound covers unordered and zero terms"
    (degreeBound [(2,1),(9,0),(1,4)] == 9)
  check "coefficients vanish immediately above actual checked bound"
    (coefficient [(0,2),(3,-1)] 4 == 0)
  check "coefficients vanish far above actual checked bound"
    (coefficient [(0,2),(3,-1)] 1000000000 == 0)
  check "equal scans the exponent newly introduced by changed target"
    (!equal [(0,1)] [(0,1),(1024,1)])
  check "high-degree canceling target remains exactly equal"
    (equal [(0,1)] [(0,1),(1024,7),(1024,-7)])
  check "multiply by empty polynomial on left" (multiply [] [(1,2)] == [])
  check "multiply by empty polynomial on right" (multiply [(1,2)] [] == [])
  check "multiply adds exponents and multiplies rational coefficients"
    (equal (multiply [(2,(2 : Rat)/3)] [(5,-(9 : Rat)/4)]) [(7,-(3 : Rat)/2)])
  check "distribution includes every cross term"
    (equal (multiply [(0,1),(1,1)] [(0,1),(1,-1)]) [(0,1),(2,-1)])
  check "zero coefficients and duplicate product terms cancel"
    (equal (multiply [(0,0),(1,2),(1,-2)] [(0,3),(2,-1)]) [])
  check "empty span replays zero" (replay [] [] [])
  check "empty span cannot replay one" (!replay [] [] [(0,1)])
  check "zero generator replays zero" (replay [[]] [[(0,1)]] [])
  check "zero cofactor replays zero" (replay [[(1,1)]] [[]] [])
  check "missing cofactor refuses even for zero target" (!replay [[]] [] [])
  check "extra cofactor refuses even for zero target" (!replay [] [[]] [])
  let generators : List Polynomial := [[(1,1)],[(0,-1),(1,1)]]
  let cofactors : List Polynomial := [[(0,1),(1,1)],[(1,-1)]]
  let target : Polynomial := [(1,2)]
  check "two-generator formal span identity" (replay generators cofactors target)
  check "altered generator refuses"
    (!replay [[(2,1)],[(0,-1),(1,1)]] cofactors target)
  check "altered cofactor refuses" (!replay generators [[(0,1)],[(1,-1)]] target)
  check "altered target refuses" (!replay generators cofactors [(1,1)])
  check "unpaired generator refuses" (!replay (generators ++ [[]]) cofactors target)
  check "unpaired cofactor refuses" (!replay generators (cofactors ++ [[]]) target)
  check "generator-cofactor pair permutation preserves identity"
    (replay generators.reverse cofactors.reverse target)
  check "cofactor permutation alone changes the identity"
    (!replay generators cofactors.reverse target)
  check "fractional three-coefficient product replays exactly"
    (replay [[(0,(1 : Rat)/2),(1,(1 : Rat)/3)]] [[(0,2),(1,3)]]
      [(0,1),(1,(13 : Rat)/6),(2,1)])
  check "fractional target mutation is detected"
    (!replay [[(0,(1 : Rat)/2),(1,(1 : Rat)/3)]] [[(0,2),(1,3)]]
      [(0,1),(1,(12 : Rat)/6),(2,1)])
  check "high-degree altered cofactor cannot escape scan"
    (!replay [[(0,1)]] [[(0,1),(1024,1)]] [(0,1)])
  check "high-degree generator identity replays"
    (replay [[(1024,1)]] [[(0,(1 : Rat)/3)]] [(1024,(1 : Rat)/3)])
  let family := smallPolynomials
  check "273 sparse polynomial records match filtered coefficient sum and vanish above bounds"
    (family.length == 273 && family.all coefficientProperties)
  check "273 polynomial equality checks are insensitive to term permutation"
    (family.all fun polynomial => equal polynomial polynomial.reverse)
  check "273 polynomial products commute as exact coefficient identities"
    (family.all fun polynomial =>
      equal (multiply polynomial [(0,1),(1,-1)])
        (multiply [(0,1),(1,-1)] polynomial))
  IO.println s!"PolyStub: {← counter.get} controls passed; exact univariate span only."

#print axioms GP50.PolyStub.equal_sound
#print axioms GP50.PolyStub.replay_coefficient_sum

