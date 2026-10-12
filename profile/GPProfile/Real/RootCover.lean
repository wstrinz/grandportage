import GPProfile.Real.Profile
import GPProfile.Real.NumberField

/-!
Two univariate checkers for the 3b stop-and-ask calls (DECISIONS.md, 2026-10-09).

**Selected-root covers (GP-X273, GP-X274).** A `realCover r bs` claim whose parent `r` selects the
root of an equation `m` in the open interval `(lo, hi)` (sign atoms `x - lo > 0`, `x - hi < 0`).
The trusted same-root check is Descartes' bound: when the Möbius transform of `m` on `(lo, hi)`
has at most one sign variation, `m` has at most one root there (binding: `atMostOneRoot_sound`,
from Mathlib's `Polynomial.roots_countP_pos_le_signVariations`). A point replay (`pointCheck`) of
the parent joined with one branch then exhibits a root of `m` in `(lo, hi)` satisfying the branch;
by uniqueness every parent point is that root, so the branch covers the parent.

**Rational-root certificates (GP-X56).** A univariate equation with integer coefficients
`a₀, …, aₙ` (`a₀ ≠ 0`) has no rational root when every candidate `±p/q`, `p ∣ a₀`, `q ∣ aₙ`,
evaluates nonzero: a rational root would be among the candidates (rational root theorem).
-/

namespace GPProfile.Real
open Hex RAlg

/-- A univariate sparse polynomial as a dense one: `p(X)`. -/
def toD (p : Sparse) : D := fieldEval 1 [RAlg.X] 0 p

/-- `c` when the dense `p` is `x - c`. -/
def linRoot (p : D) : Option Rat := if p.size == 2 && p.coeff 1 == 1 then some (-p.coeff 0) else none

/-! ## Descartes: at most one root -/

/-- The coefficients are `≥ 0` below `k` and `≤ 0` from `k` on (`pos`), or the reverse. -/
def switchAt (T : D) (k : Nat) (pos : Bool) : Bool :=
  (List.range T.size).all fun i =>
    if (decide (i < k)) == pos then 0 ≤ T.coeff i else T.coeff i ≤ 0

/-- At most one sign variation (zeros ignored) in a nonzero coefficient sequence. -/
def oneSwitch (T : D) : Bool :=
  (List.range T.size).any (fun i => T.coeff i != 0) &&
    (List.range (T.size + 1)).any fun k => switchAt T k true || switchAt T k false

/-- Trusted: `m` has at most one root in `(lo, hi)` (Descartes' bound on the Möbius transform). -/
def atMostOneRoot (m : D) (lo hi : Rat) : Bool := lo < hi && oneSwitch (mobius m lo hi)

/-! ## Selected-root covers -/

/-- The parent's selection interval and a point witness for the joined systems (untrusted). -/
structure RootCoverCert where
  lo : Rat
  hi : Rat
  point : RealWitness

/-- A parent joined with one branch: the branch's conditions added to the parent's. -/
def RealSys.join (r : RealSys) (b : RBranch) : RealSys :=
  ⟨r.vars, r.eqs ++ b.eqs, r.guards ++ b.guards, r.signs ++ b.signs⟩

/-- The sign atom `x - c` with sign `σ` is among the parent's. -/
def hasAtom (r : RealSys) (c : Rat) (σ : Int) : Bool :=
  r.signs.any fun a => a.2 == σ && sparseArity 1 a.1 && linRoot (toD a.1) == some c

/-- Trusted cover check: the parent selects a root of some equation in `(lo, hi)` with at most one
root there, and the parent joined with some branch has a replayed real point. -/
def rootCoverCheck (r : RealSys) (bs : List RBranch) (c : RootCoverCert) : Bool :=
  r.vars.length == 1 && hasAtom r c.lo 1 && hasAtom r c.hi (-1) &&
    r.eqs.any (fun m => sparseArity 1 m && atMostOneRoot (toD m) c.lo c.hi) &&
    bs.any fun b => pointCheck (r.join b) c.point

/-- Why a cover is refused (diagnostics only; agrees with `rootCoverCheck`). -/
def rootCoverExplain (r : RealSys) (bs : List RBranch) (c : RootCoverCert) : String :=
  if !(r.vars.length == 1 && hasAtom r c.lo 1 && hasAtom r c.hi (-1)) then
    "the parent is not a selected root in an open interval"
  else if !r.eqs.any (fun m => sparseArity 1 m && atMostOneRoot (toD m) c.lo c.hi) then
    "Descartes' bound does not isolate the parent's root"
  else if !bs.any (fun b => pointCheck (r.join b) c.point) then
    "no branch holds the parent's selected root"
  else "selected-root cover accepted"

/-! ## Rational-root certificates -/

/-- Trusted: the integer polynomial `M` has no rational root (the rational root test, as in
`NF.rrtOk` but in any degree): `M(0) ≠ 0` and no `±a/b` with `a ∣ M(0)`, `b ∣ lc M` is a root. -/
def noRationalRoot (M : D) : Bool :=
  (List.range M.size).all (fun i => (M.coeff i).den == 1) &&
    M.coeff 0 != 0 && (M.coeff 0).num.natAbs ≤ NF.rrtBound && M.leadingCoeff.num.natAbs ≤ NF.rrtBound &&
    (NF.divisorsN (M.coeff 0).num.natAbs).all fun a => (NF.divisorsN M.leadingCoeff.num.natAbs).all fun b =>
      M.eval ((a : Rat) / (b : Rat)) != 0 && M.eval (-((a : Rat) / (b : Rat))) != 0

/-- An order-free EMPTY claim over ℚ: one variable, and some equation without a rational root. -/
def ratRootCheck (s : Stmt) : Bool :=
  s.kind == .empty && s.vars.length == 1 && s.eqs.any fun m => sparseArity 1 m && noRationalRoot (toD m)

end GPProfile.Real
