import GPProfile.Real.Ordered
import GPProfile.Real.OrderedPar

/-!
G-6: refutation case trees (HW61-REVISITED-PACKET §5), in the shape of Siddique–Mian's
non-embeddability trees (arXiv 2607.26413), imitated, not imported. A `caseTree` certificate
proves a real system EMPTY over ℝ.

**Internal nodes** split the current branch system on a polynomial `p`:
- `zero p t f`: `p = 0` (added to the equations) or `p ≠ 0` (added to the guards);
- `sign p n z q`: the sign trichotomy (sign atoms `(p, -1)`, `(p, 0)`, `(p, 1)`).
Every point of the branch lies in one of the children, over ℝ, so missing branches are not
representable: each node carries all of its children.

**Derivation nodes** (L1b) have one child: `unit d t` derives the unit-distance equation
`|p_u − p_v|² − 1` and checks `t` with it added to the branch's equations. Weighted rhombus
relations (cited exactly as in L1a) must sum to `(p_u − p_v) − s·(p_a − p_b)` in both coordinates,
with `s = ±1` and `(a, b)` an edge: its unit equation is cited from the branch's equations. Then
`p_u − p_v = ±(p_a − p_b)` at every real point of the branch, so `|p_u − p_v|² = |p_a − p_b|² = 1`.
Steps chain: a later rhombus may cite a derived equation.

**Leaves** refute their branch system:
- `collision` (L1a): rhombus relations force two points to coincide against a distinctness guard;
- `ordered`: an ordered Positivstellensatz refutation (`orderedCheck`, C7) of the branch, with
  every guard of the branch or selected ones (`guardSel`). With no cone and no strict atoms it is
  an ideal certificate: `(∏ guards)^(2k)` lies in the ideal of the equations, so 1 lies in the
  ideal of the equations and the guard inverses.

**L1a.** The certificate's `points` table names each vertex's coordinate variables `(x, y)`. A
rhombus `(a, b, c, d)` is a 4-cycle; it *cites* its four edge equations `|p_a − p_b|² − 1`,
`|p_b − p_c|² − 1`, `|p_c − p_d|² − 1`, `|p_d − p_a|² − 1` by index in the branch's equations,
and its two diagonal distinctness guards `|p_a − p_c|²` and `|p_b − p_d|²` by index in the
branch's guards. The checker compares each cited polynomial exactly with the one it builds.
Injectivity is therefore explicit and never assumed: a rhombus whose diagonal pair has no guard
in the system (or in a case hypothesis on the path) is refused. Under those six facts the
binding proves `p_a − p_b + p_c − p_d = 0` in both coordinates (`rhombus_relation`, P1 in GP's
coordinate form; a trusted rule, not a per-instance certificate). A collision leaf then gives
rational weights `λₖ` with `Σ λₖ·(x_a − x_b + x_c − x_d) = x_u − x_v` and the same in `y`,
checked as exact identities in `ℚ[x]`, and cites the guard `|p_u − p_v|²`, which the relations
force to vanish.

Soundness: `GPBinding.Real.CaseTree.caseTreeCheck_sound`.
-/

namespace GPProfile.Real
open GPProfile Hex

/-- A rhombus instance: the 4-cycle `a b c d` (indices into the point table), the indices of its
edge equations `ab`, `bc`, `cd`, `da` in the branch's equations, and of its diagonal guards `ac`,
`bd` in the branch's guards. -/
structure Rhombus where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  eab : Nat
  ebc : Nat
  ecd : Nat
  eda : Nat
  gac : Nat
  gbd : Nat
  deriving Repr, DecidableEq

/-- An L1a collision: weighted rhombus relations summing to `p_u − p_v`, and the cited guard
`|p_u − p_v|²` they contradict. -/
structure Collision where
  rhombi : List (Rat × Rhombus)
  u : Nat
  v : Nat
  guard : Nat
  deriving Repr, DecidableEq

/-- An L1b step: weighted rhombus relations summing to `(p_u − p_v) − sign·(p_a − p_b)`, and the
cited edge equation of `(a, b)`; it derives `|p_u − p_v|² − 1 = 0`. -/
structure UnitStep where
  rhombi : List (Rat × Rhombus)
  u : Nat
  v : Nat
  a : Nat
  b : Nat
  /-- `1`: `p_u − p_v = p_a − p_b`; `-1`: `p_u − p_v = p_b − p_a`. Anything else refuses. -/
  sign : Int
  /-- The index of `|p_a − p_b|² − 1` in the branch's equations. -/
  edge : Nat
  deriving Repr, DecidableEq

inductive CaseTree where
  | collision (c : Collision)
  /-- L1b: derive `|p_u − p_v|² − 1 = 0`, then refute the branch with it added. -/
  | unit (d : UnitStep) (t : CaseTree)
  | ordered (c : OCert)
  /-- `p = 0` (first child) or `p ≠ 0` (second). -/
  | zero (p : Sparse) (onZero onNonzero : CaseTree)
  /-- `p < 0`, `p = 0`, `p > 0`. -/
  | sign (p : Sparse) (neg zero pos : CaseTree)
  deriving Repr

structure CaseTreeCert where
  /-- Vertex `i`'s coordinate variables, as indices into the system's variables. -/
  points : List (Nat × Nat)
  tree : CaseTree
  deriving Repr

/-! ## The polynomials L1a builds -/

/-- Variable `i` in arity `n` (`0` when out of range: the checker refuses those tables, and the
binding's meaning is total). -/
def varP (n i : Nat) : P n Rat := if h : i < n then MvPoly.X ⟨i, h⟩ else 0

def ptX (n : Nat) (pts : List (Nat × Nat)) (i : Nat) : P n Rat := varP n (pts.getD i (0, 0)).1
def ptY (n : Nat) (pts : List (Nat × Nat)) (i : Nat) : P n Rat := varP n (pts.getD i (0, 0)).2

/-- `|p_i − p_j|²`. -/
def sqDist (n : Nat) (pts : List (Nat × Nat)) (i j : Nat) : P n Rat :=
  (ptX n pts i - ptX n pts j) * (ptX n pts i - ptX n pts j) +
    (ptY n pts i - ptY n pts j) * (ptY n pts i - ptY n pts j)

/-- The unit-edge equation `|p_i − p_j|² − 1`. -/
def edgeP (n : Nat) (pts : List (Nat × Nat)) (i j : Nat) : P n Rat := sqDist n pts i j - MvPoly.C 1

/-- The rhombus relation's two coordinates: `x_a − x_b + x_c − x_d` and the same in `y`. -/
def relX (n : Nat) (pts : List (Nat × Nat)) (h : Rhombus) : P n Rat :=
  ptX n pts h.a - ptX n pts h.b + ptX n pts h.c - ptX n pts h.d
def relY (n : Nat) (pts : List (Nat × Nat)) (h : Rhombus) : P n Rat :=
  ptY n pts h.a - ptY n pts h.b + ptY n pts h.c - ptY n pts h.d

/-- The polynomial at index `k` of a list is `Q`, exactly. -/
def cites (n : Nat) (ps : List Sparse) (k : Nat) (Q : P n Rat) : Bool :=
  match ps[k]? with
  | some p => toHexQ n p == some Q
  | none => false

/-! ## The checker -/

/-- A rhombus instance cites its four edge equations and both diagonal guards. -/
def rhombusOk (n : Nat) (pts : List (Nat × Nat)) (r : RealSys) (h : Rhombus) : Bool :=
  cites n r.eqs h.eab (edgeP n pts h.a h.b) && cites n r.eqs h.ebc (edgeP n pts h.b h.c) &&
    cites n r.eqs h.ecd (edgeP n pts h.c h.d) && cites n r.eqs h.eda (edgeP n pts h.d h.a) &&
    cites n r.guards h.gac (sqDist n pts h.a h.c) && cites n r.guards h.gbd (sqDist n pts h.b h.d)

/-- `Σ λₖ · relₖ`. -/
def combo (n : Nat) (rel : Rhombus → P n Rat) (ts : List (Rat × Rhombus)) : P n Rat :=
  (ts.map fun t => MvPoly.C t.1 * rel t.2).sum

/-- L1a: every rhombus cites its facts, the weighted relations sum to `p_u − p_v` in both
coordinates, and `|p_u − p_v|²` is a cited guard. -/
def collisionOk (n : Nat) (pts : List (Nat × Nat)) (r : RealSys) (c : Collision) : Bool :=
  c.rhombi.all (rhombusOk n pts r ·.2) &&
    combo n (relX n pts) c.rhombi == ptX n pts c.u - ptX n pts c.v &&
    combo n (relY n pts) c.rhombi == ptY n pts c.u - ptY n pts c.v &&
    cites n r.guards c.guard (sqDist n pts c.u c.v)

/-- `(p_u − p_v) − s·(p_a − p_b)` in one coordinate (`pt` is `ptX` or `ptY`). -/
def unitRel {n : Nat} (pt : Nat → P n Rat) (d : UnitStep) : P n Rat :=
  pt d.u - pt d.v - MvPoly.C ((d.sign : Int) : Rat) * (pt d.a - pt d.b)

/-- The equation an L1b step derives, `|p_u − p_v|² − 1`, as a sparse polynomial. -/
def unitEq (n : Nat) (pts : List (Nat × Nat)) (d : UnitStep) : Sparse := ofHex (edgeP n pts d.u d.v)

/-- L1b: every rhombus cites its facts, the sign is `±1`, the weighted relations sum to
`(p_u − p_v) − s·(p_a − p_b)` in both coordinates, `(a, b)` is a cited edge, and the derived
equation reads back exactly. -/
def unitOk (n : Nat) (pts : List (Nat × Nat)) (r : RealSys) (d : UnitStep) : Bool :=
  d.rhombi.all (rhombusOk n pts r ·.2) && (d.sign == 1 || d.sign == -1) &&
    combo n (relX n pts) d.rhombi == unitRel (ptX n pts) d &&
    combo n (relY n pts) d.rhombi == unitRel (ptY n pts) d &&
    cites n r.eqs d.edge (edgeP n pts d.a d.b) &&
    toHexQ n (unitEq n pts d) == some (edgeP n pts d.u d.v)

/-- The branch systems of a split. -/
def RealSys.addEq (r : RealSys) (p : Sparse) : RealSys := { r with eqs := r.eqs ++ [p] }
def RealSys.addGuard (r : RealSys) (p : Sparse) : RealSys := { r with guards := r.guards ++ [p] }
def RealSys.addSign (r : RealSys) (p : Sparse) (σ : Int) : RealSys := { r with signs := r.signs ++ [(p, σ)] }

/-- Every leaf refutes its branch system. -/
def caseTreeGo (pts : List (Nat × Nat)) : RealSys → CaseTree → Bool
  | r, .collision c => collisionOk r.vars.length pts r c
  | r, .unit d t => unitOk r.vars.length pts r d && caseTreeGo pts (r.addEq (unitEq r.vars.length pts d)) t
  | r, .ordered c => orderedCheck r c
  | r, .zero p t f => caseTreeGo pts (r.addEq p) t && caseTreeGo pts (r.addGuard p) f
  | r, .sign p n z q =>
    caseTreeGo pts (r.addSign p (-1)) n && caseTreeGo pts (r.addSign p 0) z &&
      caseTreeGo pts (r.addSign p 1) q

/-- The point table names variables of the system. -/
def pointsOk (r : RealSys) (pts : List (Nat × Nat)) : Bool :=
  pts.all fun t => t.1 < r.vars.length && t.2 < r.vars.length

/-- EMPTY over ℝ: an exactly replaying case tree. -/
def caseTreeCheck (r : RealSys) (c : CaseTreeCert) : Bool :=
  pointsOk r c.points && caseTreeGo c.points r c.tree

/-! ## Diagnostics (agree with the checker; reporting only) -/

def rhombusExplain (n : Nat) (pts : List (Nat × Nat)) (r : RealSys) (h : Rhombus) : Option String :=
  let cyc := s!"rhombus ({h.a},{h.b},{h.c},{h.d})"
  if !(cites n r.eqs h.eab (edgeP n pts h.a h.b) && cites n r.eqs h.ebc (edgeP n pts h.b h.c) &&
      cites n r.eqs h.ecd (edgeP n pts h.c h.d) && cites n r.eqs h.eda (edgeP n pts h.d h.a)) then
    some s!"{cyc}: a cited edge equation is not the unit-distance equation of that edge"
  else if !cites n r.guards h.gac (sqDist n pts h.a h.c) then
    some s!"{cyc}: no distinctness guard cited for the diagonal ({h.a},{h.c})"
  else if !cites n r.guards h.gbd (sqDist n pts h.b h.d) then
    some s!"{cyc}: no distinctness guard cited for the diagonal ({h.b},{h.d})"
  else none

def caseTreeExplainGo (pts : List (Nat × Nat)) : RealSys → CaseTree → Except String Unit
  | r, .collision c => do
    let n := r.vars.length
    for t in c.rhombi do
      if let some e := rhombusExplain n pts r t.2 then throw e
    unless combo n (relX n pts) c.rhombi == ptX n pts c.u - ptX n pts c.v &&
        combo n (relY n pts) c.rhombi == ptY n pts c.u - ptY n pts c.v do
      throw s!"collision: the weighted rhombus relations do not sum to p{c.u} - p{c.v}"
    unless cites n r.guards c.guard (sqDist n pts c.u c.v) do
      throw s!"collision: no distinctness guard cited for ({c.u},{c.v})"
  | r, .unit d t => do
    let n := r.vars.length
    for x in d.rhombi do
      if let some e := rhombusExplain n pts r x.2 then throw e
    unless d.sign == 1 || d.sign == -1 do throw s!"unit ({d.u},{d.v}): the sign is {d.sign}, not 1 or -1"
    let (c, e) := if d.sign == 1 then (d.a, d.b) else (d.b, d.a)
    unless combo n (relX n pts) d.rhombi == unitRel (ptX n pts) d &&
        combo n (relY n pts) d.rhombi == unitRel (ptY n pts) d do
      throw s!"unit ({d.u},{d.v}): the weighted rhombus relations do not sum to (p{d.u} - p{d.v}) - (p{c} - p{e})"
    unless cites n r.eqs d.edge (edgeP n pts d.a d.b) do
      throw s!"unit ({d.u},{d.v}): ({d.a},{d.b}) is not an edge of the branch (no unit equation cited for it)"
    unless toHexQ n (unitEq n pts d) == some (edgeP n pts d.u d.v) do
      throw s!"unit ({d.u},{d.v}): the derived equation does not read back"
    caseTreeExplainGo pts (r.addEq (unitEq n pts d)) t
  | r, .ordered c =>
    match orderedExplain r c with
    | .ok () => pure ()
    | .error e => throw s!"ordered leaf refused ({reprStr e})"
  | r, .zero p t f => do
    caseTreeExplainGo pts (r.addEq p) t
    caseTreeExplainGo pts (r.addGuard p) f
  | r, .sign p n z q => do
    caseTreeExplainGo pts (r.addSign p (-1)) n
    caseTreeExplainGo pts (r.addSign p 0) z
    caseTreeExplainGo pts (r.addSign p 1) q

def caseTreeExplain (r : RealSys) (c : CaseTreeCert) : Except String Unit := do
  unless pointsOk r c.points do throw "the point table names a variable outside the system"
  caseTreeExplainGo c.points r c.tree
  unless caseTreeCheck r c do throw "case tree replay failed"

/-! ## Citation search (untrusted: its output is replayed by `caseTreeCheck`) -/

/-- The first index whose polynomial is `Q`, else an index past the end (which the checker refuses). -/
def findCite (n : Nat) (ps : List Sparse) (Q : P n Rat) : Nat :=
  ((ps.zipIdx.find? fun t => toHexQ n t.1 == some Q).map (·.2)).getD ps.length

/-- Fill a rhombus's citations from the branch system. -/
def Rhombus.cite (n : Nat) (pts : List (Nat × Nat)) (r : RealSys) (h : Rhombus) : Rhombus :=
  { h with eab := findCite n r.eqs (edgeP n pts h.a h.b), ebc := findCite n r.eqs (edgeP n pts h.b h.c),
           ecd := findCite n r.eqs (edgeP n pts h.c h.d), eda := findCite n r.eqs (edgeP n pts h.d h.a),
           gac := findCite n r.guards (sqDist n pts h.a h.c), gbd := findCite n r.guards (sqDist n pts h.b h.d) }

def citeGo (pts : List (Nat × Nat)) : RealSys → CaseTree → CaseTree
  | r, .collision c =>
    let n := r.vars.length
    .collision { c with rhombi := c.rhombi.map fun t => (t.1, t.2.cite n pts r),
                        guard := findCite n r.guards (sqDist n pts c.u c.v) }
  | r, .unit d t =>
    let n := r.vars.length
    .unit { d with rhombi := d.rhombi.map fun x => (x.1, x.2.cite n pts r),
                   edge := findCite n r.eqs (edgeP n pts d.a d.b) }
      (citeGo pts (r.addEq (unitEq n pts d)) t)
  | _, .ordered c => .ordered c
  | r, .zero p t f => .zero p (citeGo pts (r.addEq p) t) (citeGo pts (r.addGuard p) f)
  | r, .sign p n z q =>
    .sign p (citeGo pts (r.addSign p (-1)) n) (citeGo pts (r.addSign p 0) z) (citeGo pts (r.addSign p 1) q)

/-- Fill every citation a certificate leaves out. -/
def caseTreeCite (r : RealSys) (c : CaseTreeCert) : CaseTreeCert := { c with tree := citeGo c.points r c.tree }

end GPProfile.Real
