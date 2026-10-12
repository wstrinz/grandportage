import GPProfile.Real.Ordered
import GPProfile.Real.Admission

/-!
Build-time checks of the ordered Positivstellensatz checker (C7, `Real/Ordered.lean`): positive
refutations, a Cloquet-style balance example, and adversarial controls. Every `#guard` runs the
real `orderedCheck`/`orderedExplain`, so a regression fails the build.
-/

namespace GPProfile.Real.OrderedTests
open GPProfile GPProfile.Real

private def p (vars : List String) (t : String) : Sparse :=
  match parse vars t with
  | .ok q => (canonical vars.length q).getD q
  | .error _ => []

private def x := ["x"]
private def xy := ["x", "y"]
private def z3 := ["a1", "b1", "a2", "b2", "a3", "b3"]

private def sys (vs : List String) (eqs : List String) (signs : List (String × Int))
    (guards : List String := []) : RealSys :=
  ⟨vs, eqs.map (p vs), guards.map (p vs), signs.map fun t => (p vs t.1, t.2)⟩

private def sq (vs : List String) (ts : List (Rat × String)) : Block :=
  .squares (ts.map fun t => (t.1, p vs t.2))

private def cert (vs : List String) (cofs : List String) (pows : List Nat) (k : Nat)
    (cone : List (List Nat × Block)) : OCert :=
  ⟨cofs.map (p vs), pows, k, cone.map fun t => ⟨t.1, t.2⟩, none⟩

private def why (r : RealSys) (c : OCert) : Option OrdFail :=
  match orderedExplain r c with
  | .ok () => none
  | .error e => some e

private def fails (r : RealSys) (c : OCert) (e : OrdFail) : Bool :=
  !orderedCheck r c && why r c == some e

/-! ## Positive refutations -/

-- x² + 1 < 0: q = −(x² + 1) > 0, and q + (x² + 1²) = 0.
private def negSq : RealSys := sys x [] [("x^2+1", -1)]
private def negSqCert : OCert := cert x [] [1] 0 [([], sq x [(1, "x"), (1, "1")])]
#guard orderedCheck negSq negSqCert && why negSq negSqCert == none
-- The same in Gram form over [1, x], G = I.
#guard orderedCheck negSq (cert x [] [1] 0 [([], .gram [[0], [1]] [[1, 0], [0, 1]])])

-- {x > 0, x < 0}: q₀ = x, q₁ = −x; q₀ + 1·q₁ = 0.
private def bothSigns : RealSys := sys x [] [("x", 1), ("x", -1)]
private def bothCert : OCert := cert x [] [1, 0] 0 [([1], sq x [(1, "1")])]
#guard orderedCheck bothSigns bothCert

-- Guards: x ≠ 0 and x² = 0: (x)^2 − 1·x² = 0.
#guard orderedCheck (sys x ["x^2"] [] ["x"]) (cert x ["-1"] [] 1 [])

-- A zero atom joins the equations: sign x = 0, sign (x − 1) = 1; q = x − 1 and
-- q + 1·1² − 1·x = 0 (x in the ideal).
private def zeroAtom : RealSys := sys x [] [("x", 0), ("x-1", 1)]
#guard orderedCheck zeroAtom (cert x ["-1"] [1] 0 [([], sq x [(1, "1")])])

-- Unit vectors in the open first quadrant with x + y = 1: x·y ∈ ideal, so the monoid x·y refutes.
private def quadrant : RealSys := sys xy ["x^2+y^2-1", "x+y-1"] [("x", 1), ("y", 1)]
private def quadrantCert : OCert := cert xy ["1/2", "-1/2*x-1/2*y-1/2"] [1, 1] 0 []
#guard orderedCheck quadrant quadrantCert

/-! ## Cloquet-style balance (`CQ-PLAN.md:176`) -/

-- Strict balance 3z₁ + z₂ + z₃ = 0 with |zᵢ| = 1 (|3| > 1 + 1), order-free:
-- 1 + 4·1² + (a2−a3)² + (b2−b3)² + 9E₁ − 2E₂ − 2E₃ + (−3a1+a2+a3)L₁ + (−3b1+b2+b3)L₂ = 0.
private def balance : RealSys :=
  sys z3 ["a1^2+b1^2-1", "a2^2+b2^2-1", "a3^2+b3^2-1", "3*a1+a2+a3", "3*b1+b2+b3"] []
private def balanceCert : OCert :=
  cert z3 ["9", "-2", "-2", "-3*a1+a2+a3", "-3*b1+b2+b3"] [] 0
    [([], sq z3 [(4, "1"), (1, "a2-a3"), (1, "b2-b3")])]
#guard orderedCheck balance balanceCert

-- The boundary case z₁ + z₂ = 2z₃ (|2| = 1 + 1) needs the order: distinct unit vectors, with
-- the sign atom a1 − a2 > 0, have no unit midpoint. q = a1 − a2:
-- q² + (b1−b2)² − 2E₁ − 2E₂ + 4E₃ + (a1+a2+2a3)L₁ + (b1+b2+2b3)L₂ = 0.
private def midpoint : RealSys :=
  sys z3 ["a1^2+b1^2-1", "a2^2+b2^2-1", "a3^2+b3^2-1", "a1+a2-2*a3", "b1+b2-2*b3"] [("a1-a2", 1)]
private def midpointCert : OCert :=
  cert z3 ["-2", "-2", "4", "a1+a2+2*a3", "b1+b2+2*b3"] [2] 0 [([], sq z3 [(1, "b1-b2")])]
#guard orderedCheck midpoint midpointCert
-- Without the sign atom the system has points (z₁ = z₂ = z₃); no certificate shape replays.
#guard fails (sys z3 ["a1^2+b1^2-1", "a2^2+b2^2-1", "a3^2+b3^2-1", "a1+a2-2*a3", "b1+b2-2*b3"] [])
  midpointCert .posCount

/-! ## Adversarial controls -/

-- Wrong cofactor (4 → 3 on E₃).
#guard fails midpoint (cert z3 ["-2", "-2", "3", "a1+a2+2*a3", "b1+b2+2*b3"] [2] 0
  [([], sq z3 [(1, "b1-b2")])]) .identity
-- Negative weight: {x > 0} has points; x + (−1)·x = 0 replays but the weight is refused.
#guard fails (sys x [] [("x", 1)]) (cert x [] [1] 0 [([0], sq x [(-1, "1")])]) .negativeWeight
-- A negative-definite Gram block is refused (no LDLᵀ).
#guard fails (sys x [] [("x", 1)]) (cert x [] [1] 0 [([0], .gram [[0]] [[-1]])]) (.block .notPSD)
-- A true system (x² + 1 > 0 everywhere) offered the certificate of x² + 1 < 0.
#guard fails (sys x [] [("x^2+1", 1)]) negSqCert .identity
-- σ = 0 mishandled: sign x = 0 (true at x = 0) refuted as if x > 0, i.e. x − 1·x = 0.
#guard fails (sys x [] [("x", 0)]) (cert x ["-1"] [1] 0 []) .posCount
-- … and with the atom read correctly as an equation, 1 − x ≠ 0.
#guard fails (sys x [] [("x", 0)]) (cert x ["-1"] [] 0 []) .identity
-- A zero atom's cofactor is required.
#guard fails zeroAtom (cert x [] [1] 0 [([], sq x [(1, "1")])]) .cofactorCount
-- Signs outside {−1, 0, 1} refuse.
#guard fails (sys x [] [("x", 2), ("x", -1)]) bothCert .badSign
-- A cone index past the strict atoms refuses.
#guard fails bothSigns (cert x [] [1, 0] 0 [([2], sq x [(1, "1")])]) .posIndex
-- Exponent budget.
#guard fails negSq (cert x [] [65] 0 []) .budget
-- Flipped strict sign: {x > 0, x > 0} has points; the certificate of {x > 0, x < 0} fails.
#guard fails (sys x [] [("x", 1), ("x", 1)]) bothCert .identity
-- Noncanonical cofactor.
#guard fails quadrant ⟨[[([0, 0], 1/2)], [([0, 0], 0)]], [1, 1], 0, [], none⟩ .notCanonical

/-! ## Selected guards (`guardSel`) -/

-- x² + y² = 0 with guards x^200, y: every guard is over budget; guard 1 alone gives y² + x² − (x² + y²).
private def circ2 : RealSys := sys xy ["x^2+y^2"] [] ["x^200", "y"]
private def circ2Cert (sel : Option (List Nat)) : OCert :=
  { cert xy ["-1"] [] 1 [([], sq xy [(1, "x")])] with guardSel := sel }
#guard fails circ2 (circ2Cert none) .budget
#guard orderedCheck circ2 (circ2Cert (some [1]))
#guard fails circ2 (circ2Cert (some [5])) .guardIndex
#guard fails circ2 (circ2Cert (some [])) .identity
-- With a strict atom: {x² + y² = 0, y > 0, guard x^200}: y·y + x² − (x² + y²) = 0, selecting no guard.
private def circ3 : RealSys := sys xy ["x^2+y^2"] [("y", 1)] ["x^200"]
#guard orderedCheck circ3 { cert xy ["-1"] [2] 0 [([], sq xy [(1, "x")])] with guardSel := some [] }
#guard fails circ3 { cert xy ["-1"] [2] 1 [([], sq xy [(1, "x")])] with guardSel := some [0] } .budget

/-! ## Admission: only `real r .empty` at `real` -/

#guard certOk3 (.real midpoint .empty) .real (.ordered midpointCert)
#guard !certOk3 (.real midpoint .empty) .semireal (.ordered midpointCert)
#guard !certOk3 (.real midpoint .nonempty) .real (.ordered midpointCert)
#guard !certOk3 (.orderFree ⟨z3, balance.eqs, [], .empty⟩) .real (.ordered balanceCert)
#guard !certOk3 (.orderFree ⟨z3, balance.eqs, [], .empty⟩) .semireal (.ordered balanceCert)
#guard !certOk3 (.real midpoint .empty) (.alg Scope.char0Only) (.ordered midpointCert)

end GPProfile.Real.OrderedTests
