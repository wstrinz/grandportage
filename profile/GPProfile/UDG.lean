import GPProfile.Algebra

/-!
The unit-distance graph encoder in Lean (HW61 G-4, for G-1 and G-2). It mirrors
`tools/encode-udg.py`: the same variable names and order, equation order and guard order, with
every polynomial computed by Hex arithmetic. `GPBinding.UDG.udg_frame_iff` proves that the system
has a real point exactly when the graph has an injective unit-distance embedding into the plane.

- Variables `x1, y1, x2, y2, …`: vertex `i` (0-based) owns variables `2i` and `2i + 1`.
- Equations: the gauge, if requested, then `(xᵢ - xⱼ)² + (yᵢ - yⱼ)² - 1` per edge `i < j`, in
  lexicographic order. Non-edges carry no equation (extra unit distances are allowed).
- Guards: `(xᵢ - xⱼ)² + (yᵢ - yⱼ)²` for every pair `i < j`, in lexicographic order.
- Gauge (off by default): for the first edge `a < b`, the equations `x_a`, `y_a`, `x_b - 1`,
  `y_b`. It loses no points (`GPBinding.UDG.udg_gauge_iff`).
-/

namespace GPProfile.UDG
open Hex

/-- A graph as the encoder reads it: `n` vertices `0, …, n - 1` and an edge list. Pairs out of
range or with equal ends name no edge. -/
structure Data where
  n : Nat
  edges : List (Nat × Nat)
  gauge : Bool := false
  deriving Repr, DecidableEq

/-- The pairs `i < j < n`, in lexicographic order. -/
def pairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i => ((List.range n).filter fun j => i < j).map fun j => (i, j)

/-- `i` and `j` are joined by a listed edge, in either orientation. -/
def Data.adj (D : Data) (i j : Nat) : Bool :=
  D.edges.any fun e => (e.1 == i && e.2 == j) || (e.1 == j && e.2 == i)

/-- The edges `i < j`, in lexicographic order. -/
def Data.edgeList (D : Data) : List (Nat × Nat) := (pairs D.n).filter fun p => D.adj p.1 p.2

def Data.vars (D : Data) : List String :=
  (List.range D.n).flatMap fun i => [s!"x{i + 1}", s!"y{i + 1}"]

def varP (m k : Nat) : P m Rat := if h : k < m then MvPoly.X ⟨k, h⟩ else 0

/-- The squared distance of vertices `i` and `j`. -/
def sqDist (m i j : Nat) : P m Rat :=
  (varP m (2 * i) - varP m (2 * j)) * (varP m (2 * i) - varP m (2 * j)) +
    (varP m (2 * i + 1) - varP m (2 * j + 1)) * (varP m (2 * i + 1) - varP m (2 * j + 1))

/-- The gauged edge: the first edge, when the gauge is requested. -/
def Data.gaugeEdge (D : Data) : Option (Nat × Nat) := if D.gauge then D.edgeList.head? else none

/-- The gauge equations pinning the gauged edge `a < b` at `(0, 0)` and `(1, 0)`. -/
def Data.gaugeEqs (D : Data) (m : Nat) : List (P m Rat) :=
  match D.gaugeEdge with
  | some (a, b) => [varP m (2 * a), varP m (2 * a + 1), varP m (2 * b) - 1, varP m (2 * b + 1)]
  | none => []

def Data.eqPolys (D : Data) (m : Nat) : List (P m Rat) :=
  D.gaugeEqs m ++ D.edgeList.map fun e => sqDist m e.1 e.2 - 1

def Data.guardPolys (D : Data) (m : Nat) : List (P m Rat) :=
  (pairs D.n).map fun e => sqDist m e.1 e.2

/-- Every polynomial reads back exactly through its sparse form, with integer coefficients. -/
def readBack {m : Nat} (d : P m Rat) : Bool :=
  toHexQ m (ofHex d) == some d && (ofHex d).all (fun t => t.2.den == 1)

/-- The system: variables, equations and guards (`none` only if a read-back check fails). -/
def Data.system (D : Data) : Option (List String × List Sparse × List Sparse) :=
  let vars := D.vars
  let m := vars.length
  if (D.eqPolys m ++ D.guardPolys m).all readBack then
    some (vars, (D.eqPolys m).map ofHex, (D.guardPolys m).map ofHex)
  else none

/-- The encoder's statement of a given kind. -/
def Data.stmt (D : Data) (kind : Kind) : Option Stmt :=
  D.system.map fun (vars, eqs, guards) => ⟨vars, eqs, guards, kind⟩

end GPProfile.UDG
