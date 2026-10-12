import GPProfile.Algebra

/-!
The rank-3 matroid encoder in Lean (post-G3a §4.3; Will 2026-10-05: discharge ENCODING-FRAME).
It mirrors `tools/encode-matroid.py`: the same frame, variable names and triple order, with each
determinant computed by Hex arithmetic. The CLI checks that every matroid claim's system equals
this encoder's output, and `GPBinding.Matroid.frame_iff` proves that the framed system has a
`K`-point exactly when the matroid is realizable over `K`.
-/

namespace GPProfile.Matroid
open Hex

/-- A simple rank-3 matroid as the encoder reads it: `n` elements and its lines, as index lists. -/
structure Data where
  n : Nat
  lines : List (List Nat)
  deriving Repr, DecidableEq

/-- The triples `a < b < c`, in lexicographic order. -/
def triples (n : Nat) : List (Nat × Nat × Nat) :=
  (List.range n).flatMap fun a => (List.range n).flatMap fun b =>
    ((List.range n).filter fun c => a < b && b < c).map fun c => (a, b, c)

def Data.nonbasis (M : Data) (t : Nat × Nat × Nat) : Bool :=
  M.lines.any fun l => l.contains t.1 && l.contains t.2.1 && l.contains t.2.2

/-- Three distinct elements on no common line. `nonbasis` is symmetric, so no sorting is needed. -/
def Data.isBasis (M : Data) (a b c : Nat) : Bool :=
  a != b && a != c && b != c && !M.nonbasis (a, b, c)

/-- The frame: the first basis, then the first later element in general position with it. -/
def Data.frame (M : Data) : Option (List Nat) := do
  let (a, b, c) ← (triples M.n).find? fun t => !M.nonbasis t
  let d := (List.range M.n).find? fun j =>
    [a, b, c].all (· != j) && M.isBasis a b j && M.isBasis a c j && M.isBasis b c j
  pure ([a, b, c] ++ d.toList)

/-- A column entry: a constant or a variable. -/
inductive Entry where
  | const (k : Int)
  | var (i : Nat)
  deriving Repr, DecidableEq

/-- The columns: frame elements fixed to e₁, e₂, e₃ and (1, 1, 1); the others three variables each. -/
def Data.columns (M : Data) (frame : List Nat) : Nat → Entry × Entry × Entry := fun j =>
  match frame.idxOf? j with
  | some 0 => (.const 1, .const 0, .const 0)
  | some 1 => (.const 0, .const 1, .const 0)
  | some 2 => (.const 0, .const 0, .const 1)
  | some _ => (.const 1, .const 1, .const 1)
  | none =>
    let k := ((List.range M.n).filter fun i => !frame.contains i).idxOf j
    (.var (3 * k), .var (3 * k + 1), .var (3 * k + 2))

def Data.vars (M : Data) (frame : List Nat) : List String :=
  ((List.range M.n).filter fun i => !frame.contains i).flatMap fun j =>
    ["x", "y", "z"].map fun c => s!"{c}{j + 1}"

def entryP (n : Nat) : Entry → P n Rat
  | .const k => MvPoly.C (k : Rat)
  | .var i => if h : i < n then MvPoly.X ⟨i, h⟩ else 0

/-- The determinant of three columns, in the encoder's expansion. -/
def det3P (n : Nat) (u v w : Entry × Entry × Entry) : P n Rat :=
  let (a, b, c) := (entryP n u.1, entryP n u.2.1, entryP n u.2.2)
  let (d, e, f) := (entryP n v.1, entryP n v.2.1, entryP n v.2.2)
  let (g, h, i) := (entryP n w.1, entryP n w.2.1, entryP n w.2.2)
  a * (e * i - h * f) - d * (b * i - h * c) + g * (b * f - e * c)

def isConst {n : Nat} (p : P n Rat) : Bool := p.termsList.all fun (m, _) => m.toList.all (· == 0)

/-- A constant that is ±1: nonzero in every field. -/
def isUnitConst {n : Nat} (p : P n Rat) : Bool := p == MvPoly.C 1 || p == MvPoly.C (-1)

/-- The determinant of a triple's columns. -/
def Data.det (M : Data) (frame : List Nat) (n : Nat) (t : Nat × Nat × Nat) : P n Rat :=
  let col := M.columns frame
  det3P n (col t.1) (col t.2.1) (col t.2.2)

/-- The framed encoding exists: no non-basis determinant is a nonzero constant, no basis
determinant vanishes, constant basis determinants are ±1, and every determinant reads back
exactly through its sparse form. -/
def Data.frameOK (M : Data) (frame : List Nat) (n : Nat) : Bool :=
  (triples M.n).all fun t =>
    let d := M.det frame n t
    toHexQ n (ofHex d) == some d && (ofHex d).all (fun x => x.2.den == 1) &&
      if M.nonbasis t then d == 0 || !isConst d
      else d != 0 && (!isConst d || isUnitConst d)

/-- The framed system's equations (non-bases) and guards (bases), in triple order, or `none` when
the matroid has no framed encoding. -/
def Data.system (M : Data) : Option (List String × List Sparse × List Sparse) := do
  let frame ← M.frame
  let vars := M.vars frame
  let n := vars.length
  if !M.frameOK frame n then none else
  let eqs := ((triples M.n).filter fun t => M.nonbasis t && M.det frame n t != 0).map
    fun t => ofHex (M.det frame n t)
  let guards := ((triples M.n).filter fun t => !M.nonbasis t && !isConst (M.det frame n t)).map
    fun t => ofHex (M.det frame n t)
  pure (vars, eqs, guards)

/-- The encoder's statement of a given kind. -/
def Data.stmt (M : Data) (kind : Kind) : Option Stmt :=
  (M.system).map fun (vars, eqs, guards) => ⟨vars, eqs, guards, kind⟩

end GPProfile.Matroid
