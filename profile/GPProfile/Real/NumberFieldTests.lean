import GPProfile.Real.NumberFieldFrontend

/-!
Build-time tests (`#guard`) for the number-field point checker (C4, C5): the rational-root test,
points over `K = ℚ[t]/(m)` and over a finite algebra `K[Z]/(r)`, and adversarial controls.
A failing `#guard` fails the build.
-/

namespace GPProfile.Real.NumberFieldTests
open GPProfile GPProfile.Real GPProfile.Real.NF

def P (vars : List String) (s : String) : Sparse := (parse vars s).toOption.getD []
/-- A univariate text in `t` as a coefficient list. -/
def T (s : String) : List Rat := Uni.ofSparse (P ["t"] s)

#guard T "t^3-2" == [-2, 0, 0, 1]
#guard T "15*t^3+1" == [1, 0, 0, 15]

/-! ## The rational-root test -/

#guard rrtOk (RAlg.ofU (T "t^3-2"))
#guard rrtOk (RAlg.ofU (T "t^2+1"))
#guard rrtOk (RAlg.ofU (T "15*t^3+1"))
#guard rrtOk (RAlg.ofU (T "t^2+t+1"))
#guard rrtOk (RAlg.ofU (T "2*t^2-3"))
-- Reducible: a rational root 0 (GP-X350), 2, 1/2, -1/3.
#guard !rrtOk (RAlg.ofU (T "t^3-t"))
#guard !rrtOk (RAlg.ofU (T "t^2-4"))
#guard !rrtOk (RAlg.ofU (T "4*t^2-1"))
#guard !rrtOk (RAlg.ofU (T "3*t^3+t^2+3*t+1"))
-- Outside the test's reach: degree 1 and 4, rational coefficients.
#guard !rrtOk (RAlg.ofU (T "t-2"))
#guard !rrtOk (RAlg.ofU (T "t^4+1"))
#guard !rrtOk (RAlg.ofU (T "t^2+1/2"))

/-! ## Points over `K` (C4) -/

def kPoint (m : String) (vars eqs guards : List String) (coords : List String) : NFPoint :=
  ⟨T m, [], vars, eqs.map (P vars), guards.map (P vars), coords.map fun c => [T c]⟩

def ok (p : NFPoint) : Bool := nfCheck p (nfPropose p)

-- The cube root a of a³ − 2 is a nonzero point of x³ − 2 (GP-X347).
def cube : NFPoint := kPoint "t^3-2" ["x"] ["x^3-2"] ["x"] ["t"]
#guard ok cube
#guard nfExplain cube (nfPropose cube) matches .ok ()
-- 1/a = a²/2 solves 2x³ − 1 (GP-X348).
#guard ok (kPoint "t^3-2" ["x"] ["2*x^3-1"] ["x"] ["1/2*t^2"])
#guard (invK (RAlg.ofU (T "t^3-2")) (RAlg.ofU (T "t"))).map RAlg.coeffs == some (T "1/2*t^2")
-- i is a nonzero point of x² + 1 over ℚ(i) (GP-X48's closure witness), two variables.
#guard ok (kPoint "t^2+1" ["x"] ["x^2+1"] ["x"] ["t"])
#guard ok (kPoint "t^2+1" ["x", "y"] ["x^2+1", "y-x^3"] ["x+y+1", "y"] ["t", "-t"])
-- A zero coordinate (the monomial shortcut).
#guard ok (kPoint "t^3-2" ["x", "y"] ["x*y^5+y^3-2"] ["y"] ["0", "t"])

/-! ## Controls over `K` (all REFUSE) -/

-- The open guard vanishes (GP-X349).
def vanishing : NFPoint := kPoint "t^3-2" ["x"] ["x^3-2"] ["x^3-2"] ["t"]
#guard !ok vanishing
#guard nfExplain vanishing (nfPropose vanishing) matches .error _
-- A reducible defining polynomial, even where the point would replay (GP-X350, and a^3 - a with x = a).
#guard !ok (kPoint "t^3-t" ["x"] ["x^3-2"] ["x"] ["t"])
#guard !ok (kPoint "t^3-t" ["x"] ["x^3-x"] ["x+2"] ["t"])
-- Not a point: an equation does not vanish.
#guard !ok (kPoint "t^3-2" ["x"] ["x^3-3"] ["x"] ["t"])
-- A wrong inverse, a missing inverse, a reported gcd degree of 1 (GP-X320's shape).
#guard !nfCheck cube ⟨[], [[T "t"]], [0]⟩
#guard !nfCheck cube ⟨[], [], []⟩
#guard !nfCheck cube { nfPropose cube with gcdDegrees := [1] }
#guard nfExplain cube { nfPropose cube with gcdDegrees := [1] } matches .error _
-- Arity: one coordinate per variable.
#guard !nfCheck { cube with coords := [] } (nfPropose cube)

/-! ## Points over a finite algebra `K[Z]/(r)` (C5) -/

/-- `K = ℚ(i)`, `R = K[Z]/(r)` for `r` given by `K`-coefficient texts. -/
def rPoint (m : String) (r : List String) (vars eqs guards : List String) (coords : List (List String)) :
    NFPoint :=
  ⟨T m, r.map T, vars, eqs.map (P vars), guards.map (P vars), coords.map (·.map T)⟩

-- z² = i over ℚ(i): x = z satisfies x⁴ + 1 = 0, and x is a unit (z⁻¹ = −i·z).
def sqrtI : NFPoint := rPoint "t^2+1" ["-t", "0", "1"] ["x"] ["x^4+1"] ["x"] [["0", "1"]]
#guard ok sqrtI
#guard (nfPropose sqrtI).inverses == [[[], T "-t"]]
-- A non-monic modulus: 2t·Z² − 2t² has the same roots; its leading coefficient is inverted in K.
def sqrtI2 : NFPoint := rPoint "t^2+1" ["2", "0", "2*t"] ["x"] ["x^4+1"] ["x", "x+1"] [["0", "1"]]
#guard ok sqrtI2
-- Two coordinates, one in K and one in R; degree-3 field 15t³ + 1 (GP-X319's field).
def cubeTower : NFPoint :=
  rPoint "15*t^3+1" ["-t", "0", "1"] ["x", "y"] ["x^2-y", "15*y^3+1"] ["x*y", "x+1"] [["0", "1"], ["t"]]
#guard ok cubeTower

/-! ## Controls over `K[Z]/(r)` (all REFUSE) -/

-- x⁴ − 1 does not vanish at √i; x² − i does not either over (Z² + i).
#guard !ok (rPoint "t^2+1" ["-t", "0", "1"] ["x"] ["x^4-1"] [] [["0", "1"]])
#guard !ok (rPoint "t^2+1" ["t", "0", "1"] ["x", "y"] ["x^2-y"] [] [["0", "1"], ["t"]])
-- A changed modulus keeps the old certificate (GP-X336's shape): the replay refuses.
#guard !nfCheck { cubeTower with r := ["-t", "1", "1"].map T } (nfPropose cubeTower)
-- A guard that vanishes on part of R: Z² − 1 = (Z − 1)(Z + 1), guard x − 1 at x = Z.
#guard !ok (rPoint "t^2+1" ["-1", "0", "1"] ["x"] ["x^2-1"] ["x-1"] [["0", "1"]])
-- ... while x + 2 is a unit there.
#guard ok (rPoint "t^2+1" ["-1", "0", "1"] ["x"] ["x^2-1"] ["x+2"] [["0", "1"]])

/-! ## Fixture custody and decoding (C5 frontend) -/

#guard Sha256.hex "".toUTF8 == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard Sha256.hex "abc".toUTF8 == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard Sha256.hex "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8 ==
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
-- 64 and 65 bytes: the padding block boundary.
#guard Sha256.hex (String.ofList (List.replicate 64 'a')).toUTF8 ==
  "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb"

def J (t : String) : Lean.Json := (Lean.Json.parse t).toOption.getD .null
#guard (applyMutation (J "{\"a\": [1, {\"b\": 2}]}") (J "{\"op\": \"set\", \"path\": [\"a\", 1, \"b\"], \"value\": \"x\"}")).toOption ==
  some (J "{\"a\": [1, {\"b\": \"x\"}]}")
#guard (applyMutation (J "{\"c\": [1, 2, 3]}") (J "{\"op\": \"reverse\", \"path\": [\"c\"]}")).toOption ==
  some (J "{\"c\": [3, 2, 1]}")
#guard (applyMutation (J "{\"c\": [1]}") (J "{\"op\": \"set\", \"path\": [\"d\"], \"value\": 1}")).toOption == none
#guard (applyMutation (J "{\"c\": [1]}") (J "{\"op\": \"set\", \"path\": [\"c\", 3], \"value\": 1}")).toOption == none

#guard (quotientField "K = QQ[t]/(15*t**3 + 1)").toOption == some [1, 0, 0, 15]
#guard (quotientField "Q[t]/(15*t^3+1)").toOption == some [1, 0, 0, 15]
#guard (quotientField "K = QQ[t]/(15*t**3 - 1)").toOption == some [-1, 0, 0, 15]
#guard (ratOfStr "-794/1024").toOption == some (-794 / 1024)
#guard (ratOfStr "1/0").toOption == none
#guard (triplesOf (J "[\"1\", \"0\", \"0\", \"0\", \"0\", \"2/3\"]")).toOption == some [[1], [0, 0, 2/3]]

end GPProfile.Real.NumberFieldTests
