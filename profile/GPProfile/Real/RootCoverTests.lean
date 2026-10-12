import GPProfile.Real.RootCover

/-!
Build-time tests (`#guard`) for the selected-root cover and rational-root checkers
(`Real/RootCover.lean`): the corpus shapes of GP-X273, GP-X274 and GP-X56, and adversarial
controls. A failing `#guard` fails the build.
-/

namespace GPProfile.Real.RootCoverTests
open GPProfile GPProfile.Real GPProfile.Real.RAlg

def P (s : String) : Sparse := (parse ["x"] s).toOption.getD []

/-- The parent selecting the root of `m` in `(lo, hi)`, as the frontend encodes it. -/
def sel (m lo hi : String) : RealSys := ⟨["x"], [P m], [], [(P s!"x-({lo})", 1), (P s!"x-({hi})", -1)]⟩

def br (eqs : List String) (lo hi : String) : RBranch :=
  { eqs := eqs.map P, guards := [], signs := [(P s!"x-({lo})", 1), (P s!"x-({hi})", -1)] }

def cert (m : String) (lo hi : Rat) : RootCoverCert := ⟨lo, hi, ⟨coeffs (toD (P m)), lo, hi, [[0, 1]]⟩⟩

def cover (m lo hi : String) (l h : Rat) (bs : List RBranch) : Bool :=
  rootCoverCheck (sel m lo hi) bs (cert m l h)

/-! ## Selected-root covers -/

-- GP-X273: matching branches cover the parent.
#guard cover "x^2-2" "1" "2" 1 2 [br ["x^2-2"] "1" "2", br ["x^2-2"] "1" "2"]
-- GP-X274: branches selecting the negative root do not.
#guard !cover "x^2-2" "1" "2" 1 2 [br ["x^2-2"] "-2" "-1", br ["x^2-2"] "-2" "-1"]
-- A narrower branch interval holding the root covers; one missing it does not.
#guard cover "x^2-2" "1" "2" 1 2 [br ["x^2-2"] "7/5" "3/2"]
#guard !cover "x^2-2" "1" "2" 1 2 [br ["x^2-2"] "3/2" "2"]
-- A branch with sign atoms only (no equation) covers through uniqueness.
#guard cover "x^2-2" "1" "2" 1 2 [br [] "7/5" "3/2"]
-- One good branch among bad ones suffices.
#guard cover "x^2-2" "1" "2" 1 2 [br ["x^2-2"] "-2" "-1", br ["x^2-2"] "1" "2"]
-- Adversarial: the parent interval (-2, 2) holds two roots; Descartes refuses, so a branch holding
-- only the positive root is not a cover.
#guard !cover "x^2-2" "-2" "2" (-2) 2 [br ["x^2-2"] "1" "2"]
#guard !atMostOneRoot (toD (P "x^2-2")) (-2) 2
#guard atMostOneRoot (toD (P "x^2-2")) 1 2
-- Adversarial: the certificate's interval must be the parent's atoms.
#guard !cover "x^2-2" "1" "2" 0 2 [br ["x^2-2"] "1" "2"]
#guard !cover "x^2-2" "1" "2" 1 3 [br ["x^2-2"] "1" "2"]
-- No branches: no cover.
#guard !cover "x^2-2" "1" "2" 1 2 []

/-! ## Rational-root certificates -/

#guard noRationalRoot (toD (P "x^2-2"))
#guard noRationalRoot (toD (P "2*x^2-1"))
#guard noRationalRoot (toD (P "x^3-x-1"))
#guard !noRationalRoot (toD (P "x^2-4"))
#guard !noRationalRoot (toD (P "4*x^2-1"))
#guard !noRationalRoot (toD (P "6*x^2-5*x+1"))
#guard !noRationalRoot (toD (P "x^2-x"))
-- Rational coefficients are not scaled: refused (conservative).
#guard !noRationalRoot (toD (P "x^2-1/2"))
#guard ratRootCheck ⟨["x"], [P "x^2-2"], [], .empty⟩
#guard !ratRootCheck ⟨["x"], [P "x^2-2"], [], .nonempty⟩
#guard !ratRootCheck ⟨["x"], [P "x^2-4"], [], .empty⟩
#guard !ratRootCheck ⟨["x", "y"], [(parse ["x", "y"] "x^2-2").toOption.getD []], [], .empty⟩

end GPProfile.Real.RootCoverTests
