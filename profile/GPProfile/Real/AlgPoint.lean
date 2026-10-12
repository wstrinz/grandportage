import GPProfile.Algebra
import GPProfile.Univariate
import GPProfile.Real.RealPoint

/-!
The `algPoint` receipt (3b, `docs/3B-PROFILE-DESIGN.md`): an algebraic point with Bezout
certificates, for a 3a statement `NOT_IN_IDEAL(1)` at characteristic 0 (u(22)'s complex
relaxation).

The witness is a nonconstant rational polynomial `m(t)` and coordinates `q₁(t), …, qₙ(t)`.
Every equation `e` must satisfy `e(q(t)) ≡ 0 (mod m)`, and every guard `g` carries a pair
`(a, b)` with `a · ĝ + b · m = 1` exactly in `ℚ[t]`, where `ĝ = g(q(t)) mod m` (`fieldEval`
reduces modulo `m` as it composes). At any root `θ` of `m` in an algebraically closed field of
characteristic 0 the point `q(θ)` lies on the locus: the equations vanish and `a(θ)·g(q(θ)) = 1`.
The binding proves that this gives `NOT_IN_IDEAL(1)` in every field of characteristic 0.

Only `algPointCheck` is trusted. `algPointPropose` searches for the Bezout pairs with the
untrusted extended Euclidean algorithm of `GPProfile.Uni`; its output is replayed.
-/

namespace GPProfile.Real
open Hex RAlg

/-- An algebraic-point witness: the defining polynomial `m`, one coordinate polynomial per
variable and one Bezout pair `(a, b)` per guard. Polynomials are coefficient lists, lowest
degree first. -/
structure AlgPointCert where
  m : List Rat
  coords : List (List Rat)
  bezout : List (List Rat × List Rat)
  deriving Repr

/-- `a · ĝ + b · m = 1`, exactly. -/
def bezoutOk (m ĝ : D) (ab : List Rat × List Rat) : Bool :=
  (ofU ab.1 * ĝ + ofU ab.2 * m - 1).isZero

/-- Trusted replay. The statement asks NOT_IN_IDEAL(1); `m` is nonconstant; there is one
coordinate per variable; every polynomial has the statement's arity; every equation reduces
to 0 modulo `m`; every guard has an exact Bezout identity with `m`. -/
def algPointCheck (s : Stmt) (c : AlgPointCert) : Bool :=
  let n := s.vars.length
  let m := ofU c.m
  let cs := c.coords.map ofU
  s.kind == .notInIdeal (oneP n) && 2 ≤ m.size && c.coords.length == n &&
    s.eqs.all (sparseArity n) && s.guards.all (sparseArity n) &&
    s.eqs.all (fun e => (fieldEval n cs m e).isZero) &&
    s.guards.length == c.bezout.length &&
    (s.guards.zip c.bezout).all fun (g, ab) => bezoutOk m (fieldEval n cs m g) ab

/-- Why a certificate is refused, for diagnostics (agrees with `algPointCheck`). -/
def algPointExplain (s : Stmt) (c : AlgPointCert) : Except String Unit := do
  let n := s.vars.length
  let m := ofU c.m
  let cs := c.coords.map ofU
  unless s.kind == .notInIdeal (oneP n) do throw "algPoint proves NOT_IN_IDEAL(1) only"
  unless 2 ≤ m.size do throw "constant defining polynomial: no root"
  unless c.coords.length == n do throw "arity mismatch: one coordinate per variable"
  unless s.eqs.all (sparseArity n) && s.guards.all (sparseArity n) do
    throw "polynomial arity mismatch"
  unless s.eqs.all (fun e => (fieldEval n cs m e).isZero) do
    throw "an equation does not vanish modulo m"
  unless s.guards.length == c.bezout.length do throw "one Bezout pair per guard required"
  unless (s.guards.zip c.bezout).all fun (g, ab) => bezoutOk m (fieldEval n cs m g) ab do
    throw "a Bezout identity a·g + b·m = 1 fails"
  unless algPointCheck s c do throw "algPoint replay failed"

/-! ## Certificate search (untrusted) -/

/-- A Bezout pair for `ĝ` and `m` from the extended Euclidean algorithm, when their gcd is a
nonzero constant. -/
def bezoutFor (m ĝ : List Rat) : Option (List Rat × List Rat) :=
  let (d, a, b) := Uni.xgcd ĝ m
  match Uni.trim d with
  | [c] => if c == 0 then none else some (Uni.scale c⁻¹ a, Uni.scale c⁻¹ b)
  | _ => none

/-- Propose the Bezout pairs for a witness `(m, coords)`; the result still has to pass
`algPointCheck`. -/
def algPointPropose (s : Stmt) (m : List Rat) (coords : List (List Rat)) :
    Option AlgPointCert := do
  let n := s.vars.length
  let cs := coords.map ofU
  let bz ← s.guards.mapM fun g => bezoutFor m (coeffs (fieldEval n cs (ofU m) g))
  let c : AlgPointCert := ⟨m, coords, bz⟩
  if algPointCheck s c then some c else none

end GPProfile.Real
