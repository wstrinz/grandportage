import GPProfile.Real.SOS

/-!
Build-time checks of the SOS/Positivstellensatz EMPTY checker: the corpus cases it can see at the
checker level and adversarial controls. Every `#guard` runs the real `sosCheck`/`sosExplain`, so a
regression fails the build.

Not checked here (the 3b skeleton's job): the field-context scope (A10-C and X345 offer a correct
certificate at ℂ, outside semireal reach) and binding of certificate generators to the model (X02,
X311: a receipt produced for one system and offered for another).
-/

namespace GPProfile.Real.SOSTests
open GPProfile GPProfile.Real

private def p (vars : List String) (t : String) : Sparse :=
  match parse vars t with
  | .ok q => (canonical vars.length q).getD q
  | .error _ => []

private def x := ["x"]
private def xy := ["x", "y"]

private def empty (vs : List String) (eqs : List String) (guards : List String := []) : Stmt :=
  ⟨vs, eqs.map (p vs), guards.map (p vs), .empty⟩

private def sq (vs : List String) (ts : List (Rat × String)) : Block :=
  .squares (ts.map fun t => (t.1, p vs t.2))

/-- The refusal reason, or `none` when accepted. -/
private def why (s : Stmt) (c : PCert) : Option SOSFail :=
  match sosExplain s c with
  | .ok () => none
  | .error e => some e

private def fails (s : Stmt) (c : PCert) (e : SOSFail) : Bool :=
  !sosCheck s c && why s c == some e

/-! ## Corpus cases (checker level) -/

-- GP-A10-Q, GP-A10-R, GP-X308: 1 + x² − (x² + 1) = 0.
private def a10 : Stmt := empty x ["x^2+1"]
private def a10Cert : PCert := ⟨[p x "-1"], 0, [sq x [(1, "x")]], none⟩
#guard sosCheck a10 a10Cert
#guard why a10 a10Cert == none
-- GP-X309: the noncanonical record `x*x+1` parses to the same statement.
#guard empty x ["x*x+1"] == a10 && sosCheck (empty x ["x*x+1"]) a10Cert
-- GP-X01, GP-X310: false cofactor `1`: 1 + x² + (x² + 1) ≠ 0.
#guard fails a10 ⟨[p x "1"], 0, [sq x [(1, "x")]], none⟩ .identity
-- GP-X311 at the checker level: evidence for x² + 1 replayed on the model x² + 2 leaves −1.
#guard fails (empty x ["x^2+2"]) a10Cert .identity
-- GP-X02 at the checker level: the same certificate replayed on its own generators x² + 2 fails.
-- (Replayed on the model x² + 1 it holds; refusing the detached receipt is the binding's job.)
#guard fails (empty x ["x^2+2"]) ⟨[p x "-1"], 0, [sq x [(1, "x")]], none⟩ .identity

/-! ## Gram blocks -/

-- A10 in Gram form over [x], G = [[1]].
#guard sosCheck a10 ⟨[p x "-1"], 0, [.gram [[1]] [[1]]], none⟩
-- 1×1 negative pivot: x² − 1 = 0 has real points; G = [[−1]] makes the identity hold.
#guard fails (empty x ["x^2-1"]) ⟨[p x "1"], 0, [.gram [[1]] [[-1]]], none⟩ .notPSD
-- 2×2 negative second pivot: G = [[1,2],[2,1]] over [1,x]; x² + 4x + 2 has real roots.
#guard fails (empty x ["x^2+4*x+2"]) ⟨[p x "-1"], 0, [.gram [[0], [1]] [[1, 2], [2, 1]]], none⟩ .notPSD
-- Zero pivot with a nonzero off-diagonal: G = [[0,1],[1,1]] over [1,x]; (x + 1)² has the point −1.
#guard fails (empty x ["x^2+2*x+1"]) ⟨[p x "-1"], 0, [.gram [[0], [1]] [[0, 1], [1, 1]]], none⟩ .notPSD
-- Zero pivot with a zero row is PSD: σ = (x + y)² + y² over [1,x,y].
private def xyCirc : Stmt := empty xy ["x^2+2*x*y+2*y^2+1"]
#guard sosCheck xyCirc ⟨[p xy "-1"], 0, [.gram [[0,0],[1,0],[0,1]] [[0,0,0],[0,1,1],[0,1,2]]], none⟩
#guard fails xyCirc ⟨[p xy "-1"], 0, [.gram [[0,0],[1,0],[0,1]] [[0,0,0],[0,1,2],[0,0,2]]], none⟩ .notSymmetric
#guard fails xyCirc ⟨[p xy "-1"], 0, [.gram [[0,0],[1,0]] [[0,0,0],[0,1,1],[0,1,2]]], none⟩ .notSymmetric
#guard fails xyCirc ⟨[p xy "-1"], 0, [.gram [[0,0],[1,0],[0,1]] [[0,0,0],[0,1,1]]], none⟩ .notSymmetric
#guard fails a10 ⟨[p x "-1"], 0, [.gram [[1, 0]] [[1]]], none⟩ .arity
-- A perturbed but still PSD Gram matrix replays to a nonzero residual.
#guard fails xyCirc ⟨[p xy "-1"], 0, [.gram [[0,0],[1,0],[0,1]] [[0,0,0],[0,2,1],[0,1,2]]], none⟩ .identity
-- Over budget: more than `maxGram` monomials are refused before decomposition.
#guard fails a10 ⟨[p x "-1"], 0, [.gram ((List.range 257).map fun i => [i]) []], none⟩ .budget
-- Gram and explicit squares mix: x² + y² + 1 with σ = x² (Gram) + y² (square).
#guard sosCheck (empty xy ["x^2+y^2+1"]) ⟨[p xy "-1"], 0, [.gram [[1,0]] [[1]], sq xy [(1, "y")]], none⟩

/-! ## The constant must normalise to exactly 1, and weights are nonnegative -/

-- Off by a constant: 1 + ½x² − ½(x² + 1) = ½.
#guard fails a10 ⟨[p x "-1/2"], 0, [sq x [(1/2, "x")]], none⟩ .identity
-- Unnormalised −2 = x² − (x² + 2): the prover must scale.
#guard fails (empty x ["x^2+2"]) ⟨[p x "-1"], 0, [sq x [(1, "x")]], none⟩ .identity
#guard sosCheck (empty x ["x^2+2"]) ⟨[p x "-1/2"], 0, [sq x [(1/2, "x")]], none⟩
-- Negative weight: 1 − x² + (x² − 1) = 0 holds, but x² − 1 has real roots.
#guard fails (empty x ["x^2-1"]) ⟨[p x "1"], 0, [sq x [(-1, "x")]], none⟩ .negativeWeight
-- A zero weight is a (useless) square.
#guard sosCheck a10 ⟨[p x "-1"], 0, [sq x [(1, "x"), (0, "x+1")]], none⟩

/-! ## Shape controls -/

#guard fails a10 ⟨[p x "-1", p x "0"], 0, [sq x [(1, "x")]], none⟩ .cofactorCount
#guard fails a10 ⟨[], 0, [sq x [(1, "x")]], none⟩ .cofactorCount
#guard fails a10 ⟨[[([0], 0)]], 0, [sq x [(1, "x")]], none⟩ .notCanonical
#guard fails a10 ⟨[p x "-1"], 0, [.squares [(1, [([1, 0], 1)])]], none⟩ .notCanonical
#guard fails a10 ⟨[[([0, 0], -1)]], 0, [sq x [(1, "x")]], none⟩ .notCanonical
#guard fails { a10 with kind := .nonempty } a10Cert .kind
#guard fails { a10 with kind := .inIdeal (p x "1") } a10Cert .kind
#guard fails ⟨x, [[([2], 1), ([0], 1), ([0], 0)]], [], .empty⟩ a10Cert .notCanonical

/-! ## Guard powers: (∏ guards)^(2k) -/

-- x² + y² = 0, x ≠ 0 is empty over semireal fields: x² + y² − (x² + y²) = 0 with k = 1.
private def circ0 : Stmt := empty xy ["x^2+y^2"] ["x"]
#guard sosCheck circ0 ⟨[p xy "-1"], 1, [sq xy [(1, "y")]], none⟩
#guard fails circ0 ⟨[p xy "-1"], 0, [sq xy [(1, "y")]], none⟩ .identity
#guard fails circ0 ⟨[p xy "-1"], 65, [sq xy [(1, "y")]], none⟩ .budget
-- Two guards: x² + y² = 0, x ≠ 0, y ≠ 0; (xy)² = x²·y², and x²y² = y²(x² + y²) − y⁴.
#guard sosCheck (empty xy ["x^2+y^2"] ["x", "y"]) ⟨[p xy "-y^2"], 1, [sq xy [(1, "y^2")]], none⟩
-- Degree budget: 2k·deg(∏ guards) must stay within `maxRhsDegree`.
#guard fails (empty xy ["x^2+y^2"] ["x^100"]) ⟨[p xy "-1"], 2, [sq xy [(1, "y")]], none⟩ .budget

/-! ## Selected guards (`guardSel`): only the named guards enter the guard term -/

-- x² + y² = 0, x^200 ≠ 0, y ≠ 0. With every guard, the guard term (x^200·y)² is over budget; with
-- only guard 1 (y): y² + x² − (x² + y²) = 0.
private def circ2 : Stmt := empty xy ["x^2+y^2"] ["x^200", "y"]
#guard fails circ2 ⟨[p xy "-1"], 1, [sq xy [(1, "x")]], none⟩ .budget
#guard sosCheck circ2 ⟨[p xy "-1"], 1, [sq xy [(1, "x")]], some [1]⟩
-- A repeated index is an exponent: (y·y)² + (xy)² − y²(x² + y²) = 0.
#guard sosCheck circ2 ⟨[p xy "-y^2"], 1, [sq xy [(1, "x*y")]], some [1, 1]⟩
-- Controls: an index past the guards refuses; so does a selection the identity does not fit.
#guard fails circ2 ⟨[p xy "-1"], 1, [sq xy [(1, "x")]], some [2]⟩ .guardIndex
#guard fails circ2 ⟨[p xy "-1"], 1, [sq xy [(1, "x")]], some [1, 1]⟩ .identity
#guard fails circ0 ⟨[p xy "-1"], 1, [sq xy [(1, "y")]], some []⟩ .identity
-- The default (`none`) is every guard, exactly as before.
#guard sosCheck circ0 ⟨[p xy "-1"], 1, [sq xy [(1, "y")]], some [0]⟩ == sosCheck circ0 ⟨[p xy "-1"], 1, [sq xy [(1, "y")]], none⟩

end GPProfile.Real.SOSTests
