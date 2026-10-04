import GPProfile.Rules

/-!
Executable checks of the K3 IN_IDEAL rows (G3a review §3), evaluated at build time. Each instance
runs the real `ruleReach`, so its obligations are replayed by the certificate checkers.
-/

namespace GPProfile.RuleChecks
open GPProfile

private def p (vars : List String) (t : String) : Sparse :=
  match parse vars t with
  | .ok q => (canonical vars.length q).getD q
  | .error _ => []

private def xy := ["x", "y"]

/-! ### R2: an identity survives restriction to a chart

The loose system `{x²y − x = 0, x ≠ 0}` and the hyperbola `{xy = 1}` have the same locus but
different presentations. Before the sound condition, R2 refused because the guards differ. -/

private def looseC : Stmt := ⟨xy, [p xy "x^2*y - x"], [p xy "x"], .inIdeal (p xy "y - x*y^2")⟩
private def tightC : Stmt := ⟨xy, [p xy "x*y - 1"], [], .inIdeal (p xy "y - x*y^2")⟩

-- x²y − x = x·(xy − 1); and x is a unit on the hyperbola: 1 = −(xy − 1) + y·x.
private def chart : RuleData :=
  .inclusion [.ideal .rat [p xy "x"] 1 0] [.ideal .rat [p xy "-1", p xy "y"] 0 0]

#guard ruleReach tightC [looseC] chart == some Scope.all

-- Without the guard obligation the loose guard is not known to be a unit: refused.
#guard ruleReach tightC [looseC] (.inclusion [.ideal .rat [p xy "x"] 1 0] []) == none

-- A wrong guard certificate fails replay: refused.
#guard ruleReach tightC [looseC] (.inclusion [.ideal .rat [p xy "x"] 1 0]
  [.ideal .rat [p xy "1", p xy "y"] 0 0]) == none

/-! ### R3: IN_IDEAL along a polynomial map

`φ : t ↦ −t` maps `{t² = 1}` into `{x² = 1, x ≠ 2}`; IN_IDEAL(x³ − x) on the target gives
IN_IDEAL(−t³ + t) on the source. The guard certificate divides by 3, so the computed reach
excludes characteristic 3, where `x = 2` and `x = −1` coincide and the guard vanishes. -/

private def target : Stmt := ⟨["x"], [p ["x"] "x^2 - 1"], [p ["x"] "x - 2"], .inIdeal (p ["x"] "x^3 - x")⟩
private def phi : List Sparse := [p ["t"] "-t"]
private def source : Stmt :=
  ⟨["t"], [p ["t"] "t^2 - 1"], [], .inIdeal ((compose 1 phi 1 (p ["x"] "x^3 - x")).getD [])⟩

-- (−t)² − 1 = 1·(t² − 1); 1 = (t² − 1)/3 + (t − 2)(−t − 2)/3.
private def along : RuleData :=
  .map phi [.ideal .rat [p ["t"] "1"] 1 0] [.ideal .rat [p ["t"] "1/3", p ["t"] "1/3*t - 2/3"] 0 0]

#guard ruleReach source [target] along == some (Scope.outside [3])

-- The conclusion must be the composed target: IN_IDEAL(t³ − t) with the wrong sign is refused.
#guard ruleReach { source with kind := .inIdeal (p ["t"] "t^3 - t") } [target] along == none

/-! ### Geometric nonemptiness (G3a review §2, §6)

The `proper` base checker: `a² − 3` takes different values at 0 and 1 in every characteristic, so
`(a² − 3)` is proper everywhere. `a² − a` is sampled at 0 and 2, which agree mod 2: the reach is
conservative there (`a² − a` is non-constant over F₂ too), and sound. A constant is refused. -/

private def univ (m : String) : Stmt := ⟨["a"], [p ["a"] m], [], .notInIdeal (oneP 1)⟩

#guard reach (univ "a^2 - 3") (.proper .rat [0] [1]) == some Scope.all
#guard reach (univ "a^2 - a") (.proper .rat [0] [2]) == some (Scope.outside [2])
#guard reach (univ "5") (.proper .rat [0] [1]) == none

-- The bridge: a point with x ≠ 0 on {x² = 1} gives NOT_IN_IDEAL(x); a point gives NOT_IN_IDEAL(1).
private def circle (g : List Sparse) (k : Kind) : Stmt := ⟨["x"], [p ["x"] "x^2 - 1"], g, k⟩
#guard ruleReach (circle [] (.notInIdeal (p ["x"] "x"))) [circle [p ["x"] "x"] .nonempty] .witness == some Scope.all
#guard ruleReach (circle [] (.notInIdeal (oneP 1))) [circle [] .nonempty] .witness == some Scope.all
-- The witness system must carry `h` as a guard.
#guard ruleReach (circle [] (.notInIdeal (p ["x"] "x"))) [circle [] .nonempty] .witness == none

-- R2 moves NOT_IN_IDEAL(1) tight → loose: the origin lies on {xy = 0}; xy = y·x on {x = y = 0}.
#guard ruleReach ⟨xy, [p xy "x*y"], [], .notInIdeal (oneP 2)⟩
  [⟨xy, [p xy "x", p xy "y"], [], .notInIdeal (oneP 2)⟩]
  (.inclusion [.ideal .rat [p xy "y", []] 1 0] []) == some Scope.all
-- …but not loose → tight.
#guard ruleReach ⟨xy, [p xy "x", p xy "y"], [], .notInIdeal (oneP 2)⟩
  [⟨xy, [p xy "x*y"], [], .notInIdeal (oneP 2)⟩]
  (.inclusion [.ideal .rat [p xy "y", []] 1 0] []) == none

/-! ### COVER split trees and generalized R4 (G3a review §2)

`{x² = x}` is covered by `{x = 0}` and `{x = 1}`, but lies in neither branch alone: depth 0 fails
and a depth-1 tree splitting on `x` succeeds. -/

private def px (t : String) : Sparse := p ["x"] t
private def bothBranches : List (List Sparse × List Sparse) := [([px "x"], []), ([px "x - 1"], [])]
private def idem (k : Kind) (eqs : List Sparse := []) : Stmt := ⟨["x"], [px "x^2 - x"] ++ eqs, [], k⟩

-- {x² = x, x = 0} ⊆ {x = 0}: x = 0·(x² − x) + 1·x.  {x² = x, x ≠ 0} ⊆ {x = 1}: (x − 1)·x = x² − x.
private def tree : SplitTree := .split (px "x")
  (.leaf 0 [⟨.rat, [[], px "1"], 1, 0⟩] [])
  (.leaf 1 [⟨.rat, [px "1"], 1, 1⟩] [])

#guard reach (idem (.cover bothBranches)) (.cover tree) == some Scope.all
#guard reach (idem (.cover bothBranches)) (.cover (.leaf 0 [⟨.rat, [px "1"], 1, 0⟩] [])) == none

-- R4 by cover: VANISHES_ON(x³ − x) on each branch subsystem gives it on {x² = x}.
private def h3 : Kind := .vanishesOn (px "x^3 - x")
#guard ruleReach ⟨["x"], [px "x^2 - x"], [], h3⟩
  [idem (.cover bothBranches), idem h3 [px "x"], idem h3 [px "x - 1"]] .byCover == some Scope.all
-- Every branch needs its premise.
#guard ruleReach ⟨["x"], [px "x^2 - x"], [], h3⟩
  [idem (.cover bothBranches), idem h3 [px "x"]] .byCover == none

end GPProfile.RuleChecks
