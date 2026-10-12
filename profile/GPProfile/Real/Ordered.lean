import GPProfile.Real.SOS
import GPProfile.Real.RealPoint

/-!
C7: ordered exclusions over ℝ. An EMPTY claim of a real system with sign atoms (`real r .empty`
at `real` scope) is certified by a Positivstellensatz refutation (Krivine–Stengle form).

The system `r` has equations `eᵢ = 0`, guards `gⱼ ≠ 0` and sign atoms `sign pₖ = σₖ` with
`σₖ ∈ {−1, 0, 1}` (any other sign refuses). Atoms with `σ = 0` join the equations; an atom with
`σ = ±1` gives the strict positive `qₖ = σₖ·pₖ > 0`. A certificate gives one cofactor per
equation (the system's equations, then its zero atoms, in order), one exponent `aₖ` per strict
atom, a guard exponent `k` and cone terms `(S, s)` (`S` a list of strict-atom indices, `s` an SOS
block), and replay checks the exact identity in `ℚ[x]`

    ∏ₖ qₖ^aₖ · (∏ⱼ gⱼ)^(2k)  +  Σ_(S, s) s · ∏_{k ∈ S} qₖ  +  Σᵢ cᵢ·eᵢ  =  0.

As in `SOS`, a certificate may select the guards of the monoid term by index (`guardSel`, repeats
allowed): `∏ⱼ gⱼ` is then the product of the selected guards, each a guard of the system and so
nonzero at a real point. Without a selection every guard is used.

Soundness (`GPBinding.Real.OrderedSound`): at a real point of `r`, the first term is a product of
positive numbers and a nonzero even power, so positive; every cone term is a nonnegatively
weighted sum of squares times positives, so nonnegative; the ideal term vanishes. A positive
number is not zero. As in `SOS`, a Gram block is decomposed by exact LDLᵀ into explicit weighted
squares, and the identity is replayed on those squares; the decomposition is never trusted.

The order is read in ℝ (a field isomorphic to it): this is not a semireal claim, since a
semireal field has no fixed ordering (3B context note, revision 2026-10-09, item 1).
-/

namespace GPProfile.Real
open GPProfile Hex

/-- A cone term `s · ∏_{k ∈ S} qₖ`: indices into the strict atoms (repeats allowed) and an SOS
block. -/
structure ConeTerm where
  posIdx : List Nat
  block : Block
  deriving Repr, DecidableEq

/-- A Positivstellensatz refutation of a real system with sign atoms. -/
structure OCert where
  /-- One cofactor per equation, then one per zero sign atom, in order. -/
  cofactors : List Sparse
  /-- One exponent per strict sign atom (`σ = ±1`), in order. -/
  posPow : List Nat
  /-- `k` in `(∏ guards)^(2k)`. -/
  guardPow : Nat
  cone : List ConeTerm
  /-- The guards the monoid term multiplies, by index (repeats allowed); `none` is every guard. -/
  guardSel : Option (List Nat) := none
  deriving Repr, DecidableEq

inductive OrdFail where
  | notCanonical | badSign | cofactorCount | posCount | posIndex | arity | budget
  | block (e : SOSFail) | negativeWeight | identity | guardIndex
  deriving Repr, DecidableEq

/-- The polynomials of the zero sign atoms: equations. -/
def zeroAtoms (r : RealSys) : List Sparse := (r.signs.filter (·.2 == 0)).map (·.1)

/-- The strict sign atoms (`σ ≠ 0`). -/
def strictAtoms (r : RealSys) : List (Sparse × Int) := r.signs.filter (·.2 != 0)

/-- The strict positive `σ·p` of a sign atom. -/
def posHex (n : Nat) (a : Sparse × Int) : Option (P n Rat) :=
  (toHexQ n a.1).map (MvPoly.C ((a.2 : Int) : Rat) * ·)

/-- The SOS polynomial `Σ w·p²` of explicit weighted squares. -/
def sqSum {n : Nat} (sq : List (Rat × P n Rat)) : P n Rat :=
  (sq.map fun t => MvPoly.C t.1 * (t.2 * t.2)).sum

/-- A replayed cone term. An index out of range reads `0` (the precheck refuses it anyway). -/
def coneHex {n : Nat} (Q : List (P n Rat)) (t : List (Rat × P n Rat) × List Nat) : P n Rat :=
  sqSum t.1 * (t.2.map fun i => Q.getD i 0).prod

/-- The replayed polynomial `∏ qₖ^aₖ·(∏ g)^(2k) + Σ s·∏ q + Σ cᵢ·eᵢ`. -/
def oAssemble {n : Nat} (E G Q C : List (P n Rat)) (pows : List Nat) (k : Nat)
    (T : List (List (Rat × P n Rat) × List Nat)) : P n Rat :=
  ((Q.zip pows).map fun t => t.1 ^ t.2).prod * guardTerm G k + (T.map (coneHex Q)).sum +
    (List.zipWith (· * ·) C E).sum

/-- Degree of the monoid term, for the budget (`sg`: the guards it multiplies). -/
def monoidDegree (r : RealSys) (c : OCert) (sg : List Sparse) : Nat :=
  ((strictAtoms r).zip c.posPow).foldl (fun d t => d + t.2 * t.1.1.degree) 0 +
    2 * c.guardPow * degreeSum sg

/-- Every polynomial of the system and the certificate's cofactors are canonical in arity `n`. -/
def oCanonical (r : RealSys) (c : OCert) : Bool :=
  let n := r.vars.length
  let ok := fun (q : Sparse) => canonical n q == some q
  r.eqs.all ok && r.guards.all ok && r.signs.all (ok ·.1) && c.cofactors.all ok

/-- A cone term, blocks expanded to explicit squares. -/
def ConeTerm.expand (n : Nat) (t : ConeTerm) : Except OrdFail (List (Rat × P n Rat) × List Nat) :=
  match t.block.expand n with
  | .ok sq => .ok (sq, t.posIdx)
  | .error e => .error (.block e)

/-- The replayed polynomial of a certificate, or the reason it is refused before the identity. -/
def orderedResidual (r : RealSys) (c : OCert) : Except OrdFail (P r.vars.length Rat) :=
  let n := r.vars.length
  let m := (strictAtoms r).length
  if !oCanonical r c then .error .notCanonical
  else if !r.signs.all (fun a => a.2 == -1 || a.2 == 0 || a.2 == 1) then .error .badSign
  else if c.cofactors.length != r.eqs.length + (zeroAtoms r).length then .error .cofactorCount
  else if c.posPow.length != m then .error .posCount
  else if !c.cone.all (·.posIdx.all (· < m)) then .error .posIndex
  else match selectGuards r.guards c.guardSel with
  | none => .error .guardIndex
  | some sg =>
  if c.guardPow > maxExponent || c.posPow.any (· > maxExponent) ||
      c.cone.any (·.posIdx.length > maxExponent) || monoidDegree r c sg > maxRhsDegree then .error .budget
  else match c.cone.mapM (ConeTerm.expand n) with
    | .error e => .error e
    | .ok T =>
      if !T.all (fun t => t.1.all fun u => decide (0 ≤ u.1)) then .error .negativeWeight
      else match (r.eqs ++ zeroAtoms r).mapM (toHexQ n), sg.mapM (toHexQ n),
          (strictAtoms r).mapM (posHex n), c.cofactors.mapM (toHexQ n) with
        | some E, some G, some Q, some C => .ok (oAssemble E G Q C c.posPow c.guardPow T)
        | _, _, _, _ => .error .arity

/-- Why a certificate is accepted (`.ok ()`) or refused (diagnostics). -/
def orderedExplain (r : RealSys) (c : OCert) : Except OrdFail Unit :=
  match orderedResidual r c with
  | .ok R => if R == 0 then .ok () else .error .identity
  | .error e => .error e

/-- EMPTY over ℝ: an exactly replaying ordered Positivstellensatz refutation. -/
def orderedCheck (r : RealSys) (c : OCert) : Bool :=
  match orderedResidual r c with
  | .ok R => R == 0
  | .error _ => false

end GPProfile.Real
