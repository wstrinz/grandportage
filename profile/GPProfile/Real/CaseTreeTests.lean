import GPProfile.Real.CaseTree
import GPProfile.Real.Admission

/-!
Build-time checks (`#guard`) of the refutation case-tree checker (G-6, `Real/CaseTree.lean`): an
L1a collision on K₂,₃ (two unit circles meet in at most two points), splits, and the adversarial
controls: a rhombus without a diagonal guard, a wrong citation, a leaf wrong by one coefficient,
a wrong branch under a split, and a ℂ-scope (`alg`) or semireal claim, which never receives a tree.
L1b: Globus–Parshall's GP5 needs one derived unit edge before its L1a collision; its controls are a
missing diagonal guard, a via pair that is not an edge, a wrong sign and an off-by-one weight.
Every `#guard` runs the real `caseTreeCheck` / `certOk3`.
-/

namespace GPProfile.Real.CaseTreeTests
open GPProfile GPProfile.Real

private def p (vars : List String) (t : String) : Sparse :=
  match parse vars t with
  | .ok q => (canonical vars.length q).getD q
  | .error _ => []

/-- Five points `p0 … p4` as variables `x0 y0 … x4 y4`. -/
private def v5 : List String := (List.range 5).flatMap fun i => [s!"x{i}", s!"y{i}"]
private def pts5 : List (Nat × Nat) := (List.range 5).map fun i => (2 * i, 2 * i + 1)

private def d2 (i j : Nat) : String := s!"(x{i}-x{j})^2+(y{i}-y{j})^2"

private def pairs5 : List (Nat × Nat) :=
  (List.range 5).flatMap fun i => (List.range 5).filterMap fun j => if i < j then some (i, j) else none

/-- K₂,₃ with parts {0, 1} and {2, 3, 4}: unit edges, and a distinctness guard on every pair but
those in `drop`. -/
private def k23 (drop : List (Nat × Nat) := []) : RealSys :=
  ⟨v5, [(0, 2), (1, 2), (0, 3), (1, 3), (0, 4), (1, 4)].map (fun e => p v5 (d2 e.1 e.2 ++ "-1")),
    (pairs5.filter (!drop.contains ·)).map (fun e => p v5 (d2 e.1 e.2)), []⟩

/-- A rhombus with citations to be filled by the (untrusted) search. -/
private def R (a b c d : Nat) : Rhombus := ⟨a, b, c, d, 0, 0, 0, 0, 0, 0⟩

/-- (p0 − p2 + p1 − p3) − (p0 − p2 + p1 − p4) = p4 − p3: the guard on {3, 4} is contradicted. -/
private def l1a (w : Rat := -1) : CaseTree := .collision ⟨[(1, R 0 2 1 3), (w, R 0 2 1 4)], 4, 3, 0⟩

private def cert (r : RealSys) (t : CaseTree) : CaseTreeCert := caseTreeCite r ⟨pts5, t⟩

private def why (r : RealSys) (c : CaseTreeCert) : String :=
  match caseTreeExplain r c with
  | .ok () => "accepted"
  | .error e => e

/-! ## Accepted -/

#guard caseTreeCheck (k23) (cert (k23) (l1a))
#guard why (k23) (cert (k23) (l1a)) == "accepted"
-- Only four guards are needed: the diagonals {0,1}, {2,3}, {2,4} and the collided pair {3,4}.
private def needed : List (Nat × Nat) := [(0, 1), (2, 3), (2, 4), (3, 4)]
private def k23min : RealSys := k23 (pairs5.filter (!needed.contains ·))
#guard caseTreeCheck k23min (cert k23min (l1a))
-- The same leaf under a sign split (on x0 − x1): every branch must close, and each does.
private def splitTree (w : Rat := -1) : CaseTree := .sign (p v5 "x0-x1") (l1a) (l1a) (l1a w)
#guard caseTreeCheck (k23) (cert (k23) (splitTree))

/-! ## Controls (each refused) -/

-- (1) A rhombus whose diagonal pair {2, 3} has no guard: injectivity is not assumed.
#guard !caseTreeCheck (k23 [(2, 3)]) (cert (k23 [(2, 3)]) (l1a))
#guard why (k23 [(2, 3)]) (cert (k23 [(2, 3)]) (l1a)) ==
  "rhombus (0,2,1,3): no distinctness guard cited for the diagonal (2,3)"
-- The other diagonal, {0, 1}, likewise.
#guard !caseTreeCheck (k23 [(0, 1)]) (cert (k23 [(0, 1)]) (l1a))
-- Citing some other guard for the diagonal (index 1 is the guard on {0, 2}, an edge) is refused.
private def miscited : CaseTreeCert :=
  let c := cert (k23) (l1a)
  match c.tree with
  | .collision k => { c with tree := .collision { k with rhombi := k.rhombi.map fun t =>
      (t.1, { t.2 with gbd := 1 }) } }
  | t => { c with tree := t }
#guard !caseTreeCheck (k23) miscited
-- A cited edge equation that is not that edge's equation.
private def badEdge : CaseTreeCert :=
  let c := cert (k23) (l1a)
  match c.tree with
  | .collision k => { c with tree := .collision { k with rhombi := k.rhombi.map fun t =>
      (t.1, { t.2 with eab := 5 }) } }
  | t => { c with tree := t }
#guard !caseTreeCheck (k23) badEdge
-- (2) A missing branch is unrepresentable (every split carries all its children); the nearest
-- executable control is a split with one wrong branch, which refuses the whole tree.
#guard !caseTreeCheck (k23) (cert (k23) (splitTree (-2)))
-- (3) A leaf wrong by one coefficient.
#guard !caseTreeCheck (k23) (cert (k23) (l1a (-2)))
#guard why (k23) (cert (k23) (l1a (-2))) == "collision: the weighted rhombus relations do not sum to p4 - p3"
-- No guard on the collided pair {3, 4}.
#guard !caseTreeCheck (k23 [(3, 4)]) (cert (k23 [(3, 4)]) (l1a))
-- A point table naming a variable outside the system.
#guard !caseTreeCheck (k23) { cert (k23) (l1a) with points := pts5 ++ [(10, 11)] }

/-! ## Scope (4): over ℝ only -/

private def s23 : Stmt := ⟨v5, (k23).eqs, (k23).guards, .empty⟩
private def c23 : Cert3 := .caseTree (cert (k23) (l1a))
#guard certOk3 (.orderFree s23) .real c23
#guard certOk3 (.real (k23) .empty) .real c23
-- A ℂ-scope (characteristic 0) claim never receives a case tree, nor does a semireal one.
#guard !certOk3 (.alg s23) (.alg Scope.char0Only) c23
#guard !certOk3 (.orderFree s23) .semireal c23
#guard !certOk3 (.real (k23) .empty) .semireal c23
-- A case tree proves EMPTY, never NONEMPTY.
#guard !certOk3 (.orderFree { s23 with kind := .nonempty }) .real c23
#guard !certOk3 (.real (k23) .nonempty) .real c23
-- And nothing narrows from a characteristic scope into ℝ.
#guard Scope3.le (.alg Scope.char0Only) .real = false

/-! ## Splits with ordered leaves -/

-- x² + 1 = 0, split on x: x = 0 gives 1 = (x² + 1) − x·x; x ≠ 0 gives 1 + x² − (x² + 1) = 0.
private def xs : List String := ["x"]
private def sq1 : RealSys := ⟨xs, [p xs "x^2+1"], [], []⟩
private def zeroTree : CaseTree :=
  .zero (p xs "x") (.ordered ⟨[p xs "-1", p xs "x"], [], 0, [], none⟩)
    (.ordered ⟨[p xs "-1"], [], 0, [⟨[], .squares [(1, p xs "x")]⟩], none⟩)
#guard caseTreeCheck sq1 ⟨[], zeroTree⟩
-- The zero branch's leaf must use the branch equation x = 0: without its cofactor it is refused.
#guard !caseTreeCheck sq1 ⟨[], .zero (p xs "x") (.ordered ⟨[p xs "-1"], [], 0, [], none⟩)
    (.ordered ⟨[p xs "-1"], [], 0, [⟨[], .squares [(1, p xs "x")]⟩], none⟩)⟩

/-! ## L1b: derived unit edges (GP5) -/

-- GP5 (7 vertices, 11 edges). The rhombi 0-1-5-6 and 1-3-4-5 sum to (p0 − p3) + (p4 − p6), so
-- p0 − p3 = −(p4 − p6) and the edge 46 forces |p0 − p3| = 1. Then K₄ on {0, 1, 2, 3} collides 0
-- and 1: ½(0-1-2-3) + ½(0-1-3-2) = p0 − p1.
private def v7 : List String := (List.range 7).flatMap fun i => [s!"x{i}", s!"y{i}"]
private def pts7 : List (Nat × Nat) := (List.range 7).map fun i => (2 * i, 2 * i + 1)
private def pairs7 : List (Nat × Nat) :=
  (List.range 7).flatMap fun i => (List.range 7).filterMap fun j => if i < j then some (i, j) else none
private def gp5Edges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 6), (1, 2), (1, 3), (1, 5), (2, 3), (3, 4), (4, 5), (4, 6), (5, 6)]
private def gp5 (drop : List (Nat × Nat) := []) (dropEdge : List (Nat × Nat) := []) : RealSys :=
  ⟨v7, (gp5Edges.filter (!dropEdge.contains ·)).map (fun e => p v7 (d2 e.1 e.2 ++ "-1")),
    (pairs7.filter (!drop.contains ·)).map (fun e => p v7 (d2 e.1 e.2)), []⟩

private def k4 : CaseTree := .collision ⟨[(1/2, R 0 1 2 3), (1/2, R 0 1 3 2)], 0, 1, 0⟩
private def step (w : Rat := 1) (sign : Int := -1) (a : Nat := 4) (b : Nat := 6) : UnitStep :=
  ⟨[(1, R 0 1 5 6), (w, R 1 3 4 5)], 0, 3, a, b, sign, 0⟩
private def l1b (d : UnitStep := step) : CaseTree := .unit d k4
private def cert7 (r : RealSys) (t : CaseTree) : CaseTreeCert := caseTreeCite r ⟨pts7, t⟩
private def why7 (r : RealSys) (t : CaseTree) : String :=
  match caseTreeExplain r (cert7 r t) with
  | .ok () => "accepted"
  | .error e => e

#guard caseTreeCheck (gp5) (cert7 (gp5) (l1b))
#guard why7 (gp5) (l1b) == "accepted"
-- The collision alone is refused: the edge 03 is not in the system until the step derives it.
#guard !caseTreeCheck (gp5) (cert7 (gp5) k4)
-- The step's edge is cited by the collision's rhombi: the derived equation is the last one.
#guard certOk3 (.orderFree ⟨v7, (gp5).eqs, (gp5).guards, .empty⟩) .real (.caseTree (cert7 (gp5) (l1b)))

-- Controls, each refused. (1) A missing diagonal guard: {0, 5} is a diagonal of 0-1-5-6.
#guard !caseTreeCheck (gp5 [(0, 5)]) (cert7 (gp5 [(0, 5)]) (l1b))
#guard why7 (gp5 [(0, 5)]) (l1b) == "rhombus (0,1,5,6): no distinctness guard cited for the diagonal (0,5)"
-- (2) The via pair is not an edge: drop the edge 46 (no rhombus uses it, so only the step fails).
#guard !caseTreeCheck (gp5 [] [(4, 6)]) (cert7 (gp5 [] [(4, 6)]) (l1b))
#guard why7 (gp5 [] [(4, 6)]) (l1b) ==
  "unit (0,3): (4,6) is not an edge of the branch (no unit equation cited for it)"
-- A via pair that is an edge but the wrong one (02 instead of 46) is refused by the identity.
#guard !caseTreeCheck (gp5) (cert7 (gp5) (l1b (step 1 (-1) 0 2)))
-- (3) A wrong sign.
#guard !caseTreeCheck (gp5) (cert7 (gp5) (l1b (step 1 1)))
#guard why7 (gp5) (l1b (step 1 1)) ==
  "unit (0,3): the weighted rhombus relations do not sum to (p0 - p3) - (p4 - p6)"
-- A sign other than ±1.
#guard !caseTreeCheck (gp5) (cert7 (gp5) (l1b (step 1 2)))
-- (4) An off-by-one coefficient.
#guard !caseTreeCheck (gp5) (cert7 (gp5) (l1b (step 2)))
#guard why7 (gp5) (l1b (step 2)) ==
  "unit (0,3): the weighted rhombus relations do not sum to (p0 - p3) - (p6 - p4)"
-- A miscited via edge (index 0 is the edge 01) is refused even when the identity holds.
#guard !caseTreeCheck (gp5)
  (match cert7 (gp5) (l1b) with
   | ⟨pt, .unit d t⟩ => ⟨pt, .unit { d with edge := 0 } t⟩
   | c => c)

end GPProfile.Real.CaseTreeTests
