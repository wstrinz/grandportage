import GPProfile.Algebra

/-!
The 3b EMPTY checker by Positivstellensatz/SOS refutation (post-G2 §5; 3B context note, revision
2026-10-09: semireal scope, order-free systems only).

A 3a statement of kind EMPTY is a system `eᵢ = 0`, `g ≠ 0` (g over the guards). A certificate gives
cofactors `qᵢ`, a guard exponent `k` and SOS blocks, and replay checks the exact identity

    (∏ guards)^(2k) + Σ_blocks σ + Σᵢ qᵢ·eᵢ = 0      in ℚ[x],

with every block a sum of nonnegatively weighted squares. A Gram block `(m, G)` is turned into
weighted squares `Σₖ dₖ (Σⱼ Lⱼₖ mⱼ)²` by exact LDLᵀ, and the identity is replayed on those explicit
squares, so `G` is an untrusted hint and soundness never depends on the decomposition. The constant
term is fixed at exactly `(∏ guards)^(2k)`: an identity that only holds up to a positive scalar
must be normalised by the prover. At a point of the system in a field `K` the identity gives
`(gᵏ)² + σ(x) = 0` with `gᵏ ≠ 0`, so `−1` is a sum of squares in `K`; the binding package
(`GPBinding.Real.SOSSound`) proves that impossible for every semireal `K`.

**Selected guards** (`guardSel`, as 3a's `idealSel`): a certificate may name guard indices,
repeats allowed (a repeated index is an exponent), and then `∏ guards` above is the product of the
selected guards only. Every selected guard is a guard of the system, so it is nonzero on the
locus, and so is any product of them. Without a selection every guard is used, exactly as before.

Scope (which contexts may receive this reach) is not decided here: `sosCheck` says only that the
system is empty over every semireal field.
-/

namespace GPProfile.Real
open GPProfile Hex

/-! ## Exact LDLᵀ (untrusted: its output is replayed, never trusted) -/

namespace SOS

/-- A dense square rational matrix, row-major. -/
structure Mat where
  n : Nat
  data : Array Rat

def Mat.get (A : Mat) (i j : Nat) : Rat := A.data.getD (i * A.n + j) 0

def Mat.ofRows (rows : List (List Rat)) : Option Mat :=
  let n := rows.length
  if rows.all (·.length == n) then some ⟨n, rows.flatten.toArray⟩ else none

def Mat.symmetric (A : Mat) : Bool :=
  A.data.size == A.n * A.n &&
    (List.range A.n).all fun i => (List.range i).all fun j => A.get i j == A.get j i

/-- The LDLᵀ factors: pivots `d` and the unit lower-triangular `L` (dense, row-major). -/
structure LDL where
  d : Array Rat
  L : Mat

/-- Exact LDLᵀ without pivoting, or `none` when the matrix is not symmetric positive
semidefinite. A negative pivot refuses; a zero pivot requires its remaining row and column to be
zero. Every Schur complement of a PSD matrix is PSD, and a PSD matrix with a zero diagonal entry
has a zero row there, so this accepts exactly the PSD matrices. -/
def ldl (G : Mat) : Option LDL := Id.run do
  if !G.symmetric then return none
  let n := G.n
  let mut A := G.data
  let mut L : Array Rat := (Array.range (n * n)).map fun t => if t / n == t % n then 1 else 0
  let mut d : Array Rat := #[]
  for k in [0:n] do
    let p := A.getD (k * n + k) 0
    if p < 0 then return none
    if p == 0 then
      for j in [k+1:n] do
        if A.getD (k * n + j) 0 != 0 || A.getD (j * n + k) 0 != 0 then return none
      d := d.push 0
    else
      d := d.push p
      for i in [k+1:n] do
        let lik := A.getD (i * n + k) 0 / p
        L := L.set! (i * n + k) lik
        if lik != 0 then
          for j in [k+1:n] do
            A := A.set! (i * n + j) (A.getD (i * n + j) 0 - lik * A.getD (k * n + j) 0)
  return some ⟨d, ⟨n, L⟩⟩

/-- `(dₖ, ℓₖ)` with `ℓₖ = Σⱼ L[j][k] · x^{mⱼ}` for each column `k` with a nonzero pivot. -/
def LDL.squares {n : Nat} (f : LDL) (ms : Array (Mono n)) : List (Rat × P n Rat) :=
  (List.range f.L.n).filterMap fun k =>
    let dk := f.d.getD k 0
    if dk == 0 then none
    else some (dk, MvPoly.ofTerms ((List.range f.L.n).filterMap fun j =>
      let c := f.L.get j k
      if c == 0 then none else (ms[j]?).map fun m => (m, c)))

end SOS

/-! ## Certificates -/

inductive Block where
  /-- `Σ wᵢ · pᵢ²` with every `wᵢ ≥ 0` and every `pᵢ` canonical. -/
  | squares (ws : List (Rat × Sparse))
  /-- `mᵀ G m` over a monomial vector `m`; `G` must be symmetric PSD (decided by exact LDLᵀ). -/
  | gram (monos : List (List Nat)) (G : List (List Rat))
  deriving Repr, DecidableEq

/-- A Positivstellensatz refutation of an EMPTY system. -/
structure PCert where
  /-- One cofactor per equation. -/
  cofactors : List Sparse
  /-- `k` in the guard term `(∏ guards)^(2k)`; `k = 0` gives the constant 1. -/
  guardPow : Nat
  blocks : List Block
  /-- The guards the guard term multiplies, by index (repeats allowed); `none` is every guard. -/
  guardSel : Option (List Nat) := none
  deriving Repr, DecidableEq

/-- Gram blocks beyond this many monomials are refused rather than decomposed. -/
def maxGram : Nat := 256

inductive SOSFail where
  | kind | notCanonical | cofactorCount | arity | budget
  | negativeWeight | notSymmetric | notPSD | identity | guardIndex
  deriving Repr, DecidableEq

/-- The guards a guard term multiplies: every guard, or the selected ones by index (a repeated
index is an exponent); `none` when an index is out of range. Each is a guard of the system. -/
def selectGuards (gs : List Sparse) : Option (List Nat) → Option (List Sparse)
  | none => some gs
  | some idx => idx.mapM (gs[·]?)

def degreeSum (gs : List Sparse) : Nat := gs.foldl (fun d g => d + g.degree) 0

/-- A block as explicit weighted squares, or the reason it is refused. -/
def Block.expand (n : Nat) : Block → Except SOSFail (List (Rat × P n Rat))
  | .squares ws =>
    if !ws.all (fun t => canonical n t.2 == some t.2) then .error .notCanonical
    else match ws.mapM (fun t => (toHexQ n t.2).map (t.1, ·)) with
      | some l => .ok l
      | none => .error .arity
  | .gram monos G =>
    if monos.length > maxGram then .error .budget
    else match monos.mapM (mono? n) with
      | none => .error .arity
      | some ms =>
        match SOS.Mat.ofRows G with
        | none => .error .notSymmetric
        | some M =>
          if M.n != monos.length || !M.symmetric then .error .notSymmetric
          else match SOS.ldl M with
            | none => .error .notPSD
            | some f => .ok (f.squares ms.toArray)

/-- The guard term `(∏ guards)^(2k)`. For `k = 0` it is `1`, and the product is never formed (with many
guards it is large). -/
def guardTerm {n : Nat} (guards : List (P n Rat)) (k : Nat) : P n Rat :=
  if k = 0 then 1 else guards.prod ^ (2 * k)

/-- The replayed polynomial `(∏ guards)^(2k) + Σ w·p² + Σ qᵢ·eᵢ`. -/
def assemble {n : Nat} (guards : List (P n Rat)) (k : Nat) (sq : List (Rat × P n Rat))
    (qs eqs : List (P n Rat)) : P n Rat :=
  guardTerm guards k + (sq.map fun t => MvPoly.C t.1 * (t.2 * t.2)).sum +
    (List.zipWith (· * ·) qs eqs).sum

def guardDegree (s : Stmt) : Nat := degreeSum s.guards

/-- The replayed polynomial of a certificate, or the reason it is refused before the identity. -/
def sosResidual (s : Stmt) (c : PCert) : Except SOSFail (P s.vars.length Rat) :=
  let n := s.vars.length
  if s.kind != .empty then .error .kind
  else if !s.canonical || !c.cofactors.all (fun q => canonical n q == some q) then .error .notCanonical
  else if c.cofactors.length != s.eqs.length then .error .cofactorCount
  else match selectGuards s.guards c.guardSel with
  | none => .error .guardIndex
  | some sg =>
  if c.guardPow > maxExponent || 2 * c.guardPow * degreeSum sg > maxRhsDegree then .error .budget
  else match c.blocks.mapM (Block.expand n) with
    | .error e => .error e
    | .ok sqs =>
      if !sqs.flatten.all (fun t => decide (0 ≤ t.1)) then .error .negativeWeight
      else match s.eqs.mapM (toHexQ n), sg.mapM (toHexQ n), c.cofactors.mapM (toHexQ n) with
        | some eqs, some guards, some qs => .ok (assemble guards c.guardPow sqs.flatten qs eqs)
        | _, _, _ => .error .arity

/-- Why a certificate is accepted (`.ok ()`) or refused (diagnostics). -/
def sosExplain (s : Stmt) (c : PCert) : Except SOSFail Unit :=
  match sosResidual s c with
  | .ok r => if r == 0 then .ok () else .error .identity
  | .error e => .error e

/-- EMPTY over every semireal field: an order-free EMPTY statement and an exactly replaying
Positivstellensatz certificate. -/
def sosCheck (s : Stmt) (c : PCert) : Bool :=
  match sosResidual s c with
  | .ok r => r == 0
  | .error _ => false

end GPProfile.Real
