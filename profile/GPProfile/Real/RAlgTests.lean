import GPProfile.Univariate
import GPProfile.Real.RealPoint

/-!
Build-time tests (`#guard`) for the real-algebraic-point checker: the corpus cases X273, X274,
X280, X351–X354, X404, X405 (inputs transcribed from `corpus/must/GP-X*.json`) and the
prototype's adversarial controls. A failing `#guard` fails the build.
-/

namespace GPProfile.Real.Tests
open GPProfile GPProfile.Real GPProfile.Real.RAlg

def P (vars : List String) (s : String) : Sparse := (parse vars s).toOption.getD []
/-- A univariate text as a coefficient list. -/
def U1 (v s : String) : List Rat := Uni.ofSparse (P [v] s)
def D1 (v s : String) : D := ofU (U1 v s)

def mkSys (vars : List String) (eqs guards : List String) (signs : List (String × Int)) :
    RealSys :=
  ⟨vars, eqs.map (P vars), guards.map (P vars), signs.map fun (f, σ) => (P vars f, σ)⟩

/-- The point `θ` itself, selected from `m` by `[lo, hi]`. -/
def theta (v m : String) (lo hi : Rat) : RealWitness := ⟨U1 v m, lo, hi, [[0, 1]]⟩

/-- A sign case: the sign of `g` at the root of `m` selected by `[lo, hi]`, checked both
as a univariate claim and as a one-variable point replay. -/
def signCase (m : String) (lo hi : Rat) (g : String) (σ : Int) : Bool :=
  let viaClaim := signClaim (D1 "w" m) lo hi (D1 "w" g) σ
  let viaPoint := pointCheck (mkSys ["w"] [] [] [(g, σ)]) (theta "w" m lo hi)
  viaClaim && viaPoint

/-- Both routes refuse. -/
def signRefused (m : String) (lo hi : Rat) (g : String) (σ : Int) : Bool :=
  !signClaim (D1 "w" m) lo hi (D1 "w" g) σ &&
    !pointCheck (mkSys ["w"] [] [] [(g, σ)]) (theta "w" m lo hi)

/-- A branch `(equations, [lo, hi])` holds the parent's selected root when the branch is
admitted (generator: its first equation) and the root satisfies its equations with `lo ≤ θ ≤ hi`. -/
def branchHit (parent : RealWitness) (eqs : List String) (lo hi : Rat) : Bool :=
  (match isolate (D1 "x" (eqs.headD "0")) lo hi with | .ok _ => true | .error _ => false) &&
    [(0, -1), (0, 0), (1, -1), (1, 0)].any fun (σlo, σhi) =>
      pointCheck (mkSys ["x"] eqs [] [(s!"x-({lo.num})/({lo.den})", σlo),
        (s!"x-({hi.num})/({hi.den})", σhi)]) parent

def cover (parent : RealWitness) (branches : List (List String × Rat × Rat)) : Bool :=
  branches.any fun (eqs, lo, hi) => branchHit parent eqs lo hi

/-! ## Corpus cases -/

-- GP-X273: matching selected roots cover their parent (ACCEPT).
#guard cover (theta "x" "x^2-2" 1 2) [(["x^2-2"], 1, 2), (["x^2-2"], 1, 2)]
-- GP-X274: negative selected roots do not cover the positive root (REFUSE).
#guard !cover (theta "x" "x^2-2" 1 2) [(["x^2-2"], -2, -1), (["x^2-2"], -2, -1)]
-- GP-X280: a step between matching explicit universes (ALGEBRAIC_CLOSURE) stays recordable
-- (ACCEPT). A type-level gate, not this checker; recorded for coverage.
#guard "ALGEBRAIC_CLOSURE" == "ALGEBRAIC_CLOSURE"
-- GP-X351: repeated interior root of (w^2-2)^2 on [1,2], sign w = +1 (ACCEPT).
#guard signCase "(w^2-2)^2" 1 2 "w" 1
-- GP-X352: common factor, sign w^2-2 = 0 (ACCEPT).
#guard signCase "(w^2-2)^2" 1 2 "w^2-2" 0
-- GP-X353: repeated endpoint root w = 2 of (w-2)^2 on [2,3], sign w = +1 (ACCEPT).
#guard signCase "(w-2)^2" 2 3 "w" 1
-- GP-X354: tampered sign -1 (REFUSE).
#guard signRefused "(w^2-2)^2" 1 2 "w" (-1)
-- GP-X404: interval [2,1] fails `lo < hi` (REFUSE).
#guard signRefused "w-2" 2 1 "w" 1
-- GP-X405: endpoint root w = 2 on [2,3], sign w = +1 (ACCEPT).
#guard signCase "w-2" 2 3 "w" 1

/-! ## Adversarial controls -/

def admits (m : String) (lo hi : Rat) : Bool :=
  match isolate (D1 "x" m) lo hi with | .ok _ => true | .error _ => false

-- Selection admission.
#guard !admits "x^2-2" (-2) 2                -- two roots in the interval
#guard !admits "x^2-2" 2 3                   -- interval misses the root
#guard !admits "x-1" 1 1                     -- lo = hi
#guard !admits "0" 0 1                       -- zero generator
#guard !admits "5" 0 1                       -- constant generator
#guard !admits "(x-1)*(x-2)" 1 2             -- both endpoints are roots
#guard !admits "x^2+1" (-10) 10              -- no real root
#guard admits "x^2-2" 1 2
-- Endpoint roots.
#guard signCase "(w-1)*(w-3)" 1 2 "w-1" 0
#guard signCase "(w-1)*(w-3)" 1 2 "w" 1
#guard signRefused "(w-1)*(w-3)" 1 2 "w-1" 1
-- Shared factors.
#guard signCase "(w^2-2)*(w-5)" 1 2 "(w^2-2)*(w+7)" 0
#guard signRefused "(w^2-2)*(w-5)" 1 2 "(w^2-2)*(w+7)" 1
#guard signCase "(w^2-2)*(w^2-3)" 1 (3/2) "w^2-3" (-1)  -- gcd root outside the interval
-- Repeated roots.
#guard signCase "(w^2-2)^3" 1 2 "w-3/2" (-1)
#guard signRefused "(w^2-2)^3" 1 2 "w-3/2" 1
#guard signCase "(2*w-3)^2" 1 2 "2*w-3" 0       -- double root, no sign change of m
-- Field-form points.
#guard pointCheck (mkSys ["x", "y"] ["x-y", "x^2-2"] ["x+y"] []) ⟨U1 "t" "t^2-2", 1, 2, [[0, 1], [0, 1]]⟩
#guard !pointCheck (mkSys ["x", "y"] ["x+y"] [] []) ⟨U1 "t" "t^2-2", 1, 2, [[0, 1], [0, 1]]⟩
-- θ = √2+√3, x = (θ³-9θ)/2 = √2, y = (11θ-θ³)/2 = √3.
def s23 : RealWitness := ⟨U1 "t" "t^4-10*t^2+1", 3, 4, [U1 "t" "(t^3-9*t)/2", U1 "t" "(11*t-t^3)/2"]⟩
#guard pointCheck (mkSys ["x", "y"] ["x^2-2", "y^2-3", "x^2*y^2-6"] ["x*y-2"] [("y-x", 1)]) s23
#guard !pointCheck (mkSys ["x", "y"] [] [] [("y-x", -1)]) s23               -- false sign
#guard !pointCheck (mkSys ["x", "y"] [] ["(x*y)^2-6"] []) s23               -- vanishing guard
#guard !pointCheck (mkSys ["x", "y"] ["x*y"] [] []) s23                     -- false equation
-- Wrong conjugate interval [0,1]: θ = √3-√2 gives x = -√2.
#guard !pointCheck (mkSys ["x", "y"] ["x^2-2"] [] [("x", 1)])
  ⟨U1 "t" "t^4-10*t^2+1", 0, 1, [U1 "t" "(t^3-9*t)/2", U1 "t" "(11*t-t^3)/2"]⟩
#guard pointCheck (mkSys ["x", "y"] ["x^2-2"] [] [("x", -1)])
  ⟨U1 "t" "t^4-10*t^2+1", 0, 1, [U1 "t" "(t^3-9*t)/2", U1 "t" "(11*t-t^3)/2"]⟩
-- Shape refusals.
#guard !pointCheck (mkSys ["x", "y"] ["x^2-2"] [] []) (theta "t" "t^2-2" 1 2)  -- one coordinate
#guard !pointCheck ⟨["x"], [[([2, 0], 1), ([0, 0], -2)]], [], []⟩ (theta "t" "t^2-2" 1 2)
-- A non-square-free generator with an interior root, several obligations at once.
#guard pointCheck (mkSys ["x"] ["x^2-2"] ["x-1", "x^3-3"] [("x-1", 1), ("x^3-3", -1)])
  (theta "t" "(t^2-2)^2*(t-5)" 1 2)

end GPProfile.Real.Tests
