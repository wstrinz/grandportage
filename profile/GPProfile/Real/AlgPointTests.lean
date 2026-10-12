import GPProfile.Real.AlgPoint

/-!
Build-time tests (`#guard`) for the `algPoint` checker: positive cases with hand-written and
proposed Bezout certificates, and adversarial controls. A failing `#guard` fails the build.
-/

namespace GPProfile.Real.AlgPointTests
open GPProfile GPProfile.Real

def P (vars : List String) (s : String) : Sparse := (parse vars s).toOption.getD []
/-- A univariate text in `t` as a coefficient list. -/
def T (s : String) : List Rat := Uni.ofSparse (P ["t"] s)

def stmt (vars : List String) (eqs guards : List String) : Stmt :=
  ⟨vars, eqs.map (P vars), guards.map (P vars), .notInIdeal (oneP vars.length)⟩

-- The test inputs parse as intended (an unparsed text would be the zero polynomial).
#guard T "t^3+t" == [0, 1, 0, 1]
#guard T "-1/2*t" == [0, -1/2]
#guard T "1/2*t^3-9/2*t" == [0, -9/2, 0, 1/2]
#guard P ["x", "y"] "x*y-x" == [([1, 0], -1), ([1, 1], 1)] ||
  P ["x", "y"] "x*y-x" == [([1, 1], 1), ([1, 0], -1)]

/-! ## Positive cases -/

-- x² + 1 = 0, x ≠ 0: θ = i, m = t² + 1, x = t; −t·t + 1·(t² + 1) = 1.
def circle : Stmt := stmt ["x"] ["x^2+1"] ["x"]
def circleCert : AlgPointCert := ⟨T "t^2+1", [T "t"], [(T "-t", T "1")]⟩
#guard algPointCheck circle circleCert
#guard algPointExplain circle circleCert matches .ok ()

-- Two variables, no real point: x² + y² + 1 = 0, x·y − x = 0, guards x and y.
-- θ = i√2, m = t² + 2, (x, y) = (t, 1); −t/2·t + 1/2·(t² + 2) = 1 and 1·1 + 0·m = 1.
def sphere : Stmt := stmt ["x", "y"] ["x^2+y^2+1", "x*y-x"] ["x", "y"]
def sphereCert : AlgPointCert :=
  ⟨T "t^2+2", [T "t", T "1"], [(T "-1/2*t", T "1/2"), (T "1", [])]⟩
#guard algPointCheck sphere sphereCert

-- Two variables at a degree-4 point: x² = 2, y² = 3, guard x + y.
-- θ = √2 + √3, m = t⁴ − 10t² + 1, x = (t³ − 9t)/2, y = (11t − t³)/2; Bezout by search.
def sqrts : Stmt := stmt ["x", "y"] ["x^2-2", "y^2-3"] ["x+y", "x-y"]
def sqrtsCoords : List (List Rat) := [T "1/2*t^3-9/2*t", T "-1/2*t^3+11/2*t"]
#guard (algPointPropose sqrts (T "t^4-10*t^2+1") sqrtsCoords).isSome
#guard match algPointPropose sqrts (T "t^4-10*t^2+1") sqrtsCoords with
  | some c => algPointCheck sqrts c
  | none => false

-- The proposer reproduces the hand certificate's validity on the circle.
#guard (algPointPropose circle (T "t^2+1") [T "t"]).isSome

-- No guards: x³ − 2 = 0 at the real cube root (m = t³ − 2).
#guard algPointCheck (stmt ["x"] ["x^3-2"] []) ⟨T "t^3-2", [T "t"], []⟩

/-! ## Controls (all REFUSE) -/

-- An equation not divisible by m: x² − 2 at θ = i.
#guard !algPointCheck (stmt ["x"] ["x^2-2"] ["x"]) circleCert
#guard algPointExplain (stmt ["x"] ["x^2-2"] ["x"]) circleCert matches .error _

-- A wrong Bezout pair: t·t + 1·(t² + 1) ≠ 1.
#guard !algPointCheck circle ⟨T "t^2+1", [T "t"], [(T "t", T "1")]⟩
-- A Bezout pair with b off by a constant.
#guard !algPointCheck circle ⟨T "t^2+1", [T "t"], [(T "-t", T "2")]⟩

-- A guard sharing a factor with m: m = t³ + t = t(t² + 1), guard x = t. No Bezout pair
-- exists, so every candidate fails and the search finds none.
def shared : Stmt := stmt ["x"] ["x^3+x"] ["x"]
#guard !algPointCheck shared ⟨T "t^3+t", [T "t"], [(T "-t", T "1")]⟩
#guard !algPointCheck shared ⟨T "t^3+t", [T "t"], [(T "1", [])]⟩
#guard !algPointCheck shared ⟨T "t^3+t", [T "t"], [([], T "1")]⟩
#guard (algPointPropose shared (T "t^3+t") [T "t"]).isNone
#guard algPointExplain shared ⟨T "t^3+t", [T "t"], [(T "1", [])]⟩ matches
  .error "a Bezout identity a·g + b·m = 1 fails"

-- A constant m: every equation reduces to 0 and a = 0, b = 1/c always "solves" Bezout,
-- so only the degree test stands between this and a false NOT_IN_IDEAL(1).
#guard !algPointCheck (stmt ["x"] ["1"] ["x"]) ⟨T "1", [T "t"], [([], T "1")]⟩
#guard !algPointCheck (stmt ["x"] ["x^2-2"] []) ⟨T "3", [T "t"], []⟩
#guard algPointExplain (stmt ["x"] ["x^2-2"] []) ⟨T "3", [T "t"], []⟩ matches
  .error "constant defining polynomial: no root"
-- The zero polynomial as m.
#guard !algPointCheck (stmt ["x"] ["x^2-2"] []) ⟨[], [T "t"], []⟩
#guard !algPointCheck (stmt ["x"] ["x^2-2"] []) ⟨[0, 0], [T "t"], []⟩

-- The wrong kind: NONEMPTY, EMPTY, and NOT_IN_IDEAL of a non-unit target.
#guard !algPointCheck { circle with kind := .nonempty } circleCert
#guard !algPointCheck { circle with kind := .empty } circleCert
#guard !algPointCheck { circle with kind := .notInIdeal (P ["x"] "x") } circleCert
#guard !algPointCheck { circle with kind := .notInIdeal (oneP 2) } circleCert

-- Coordinate and Bezout counts must match.
#guard !algPointCheck circle ⟨T "t^2+1", [T "t", T "t"], [(T "-t", T "1")]⟩
#guard !algPointCheck circle ⟨T "t^2+1", [T "t"], []⟩
#guard !algPointCheck circle ⟨T "t^2+1", [T "t"], [(T "-t", T "1"), (T "-t", T "1")]⟩

-- Polynomial arity must match the statement.
#guard !algPointCheck ⟨["x"], [[([2, 0], 1), ([0, 0], 1)]], [[([1], 1)]],
  .notInIdeal (oneP 1)⟩ circleCert

-- A real system with no complex point either: x² + 1 = 0 and x = 0 (guard-free).
#guard !algPointCheck (stmt ["x"] ["x^2+1", "x"] []) ⟨T "t^2+1", [T "t"], []⟩

end GPProfile.Real.AlgPointTests
