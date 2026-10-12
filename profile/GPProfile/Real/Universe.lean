import GPProfile.Families.Base
import GPProfile.Real.Plan

/-!
Point-universe and image controls for the 3b corpus (M1 group R7). Every claim here is a 3a
statement in the `alg` family at characteristic 0, and every step is a lifted 3a rule, so these
families add no admission path and no soundness obligation: the Kernel fold with `admission3`
decides, through 3a's checkers and direction tables.

Point universes, as 3a reads them at characteristic 0:
- `BASE` is NONEMPTY: a point in every field of characteristic 0, that is a rational point;
- `ALGEBRAIC_CLOSURE` is NOT_IN_IDEAL(1): a point in every algebraically closed one.

A typed coordinate-ring relation between two universes of one system is the identity relation on
that system, offered as 3a's R3 map along the identity. R3's direction table carries each kind to
itself only, so a step that changes the universe has no row and is never held, whatever the relation
is called (GP-X275–X279), while matching universes fold (GP-X280). The universe change itself is
3a's bridge rule (NONEMPTY gives NOT_IN_IDEAL(1)), which is not a coordinate-ring relation.
-/

namespace GPProfile.Real
open Lean GP50 GPProfile GPProfile.Families

/-- The identity substitution on `n` variables. -/
def identityPhi (n : Nat) : List Sparse :=
  (List.range n).map fun i => [((List.range n).map fun j => if i == j then 1 else 0, (1 : Rat))]

/-- `eqᵢ ∈ (eqs)` with cofactor 1 at position `i`: R3's obligations along the identity. -/
def selfCerts (n : Nat) (eqs : List Sparse) : List Cert :=
  (List.range eqs.length).map fun i => .ideal .rat (eqs.mapIdx fun j _ => if i == j then oneP n else []) 1 0

/-- Geometric nonemptiness of a single non-constant equation: a `properCoeff` receipt at its first
non-constant monomial. Anything else is offered no receipt. -/
def properSupport (s : Stmt) : Support3 :=
  match s.eqs, s.guards with
  | [e], [] =>
    match e.find? fun (mono, c) => c != 0 && mono.any (· != 0) with
    | some (mono, _) => .receipt (.alg (.properCoeff .rat mono))
    | none => .none
  | _, _ => .none

/-- The 3a kind of a named point universe. -/
def universeKind3 (n : Nat) : Option String → Except String Kind
  | some "BASE" => pure .nonempty
  | some "ALGEBRAIC_CLOSURE" => pure (.notInIdeal (oneP n))
  | _ => throw "no point universe on one side of the step"

def algAt0 (key : Nat) (s : Stmt) (support : Support3) (extra : List String := []) : Item3 :=
  { key, stmt := .alg s, scope := .alg Scope.char0Only, extra, support }

/-! ## Typed steps between point universes (GP-X275–X280) -/

/-- `variables`, `equations`, `source_universe`, `target_universe`, `relation`, `question`
(`record_step`) and `debt_reason` (null: a typed step, not a recorded debt). The source universe's
claim carries the receipt it can honestly have; the step files the target's claim by R3 along the
identity, and recording the step means the Kernel admits it. -/
def universeStepFamily (inputs : Json) : Except String Plan3 := do
  unless str? inputs "question" == some "record_step" do throw "only record_step questions are decoded"
  unless (obj? inputs "debt_reason").all (· == .null) do throw "a debt record is not a typed step"
  let rel ← need (str? inputs "relation") "no relation"
  let vars ← strs inputs "variables"
  let n := vars.length
  let eqs ← (← strs inputs "equations").mapM (canonP vars)
  let su := str? inputs "source_universe"
  let tu := str? inputs "target_universe"
  let src : Stmt := ⟨vars, eqs, [], ← universeKind3 n su⟩
  let tgt : Stmt := ⟨vars, eqs, [], ← universeKind3 n tu⟩
  -- A rational point is never searched for; geometric nonemptiness has a `properCoeff` receipt.
  let srcSupport := if src.kind == .nonempty then .none else properSupport src
  let items := [algAt0 1 src srcSupport ["side:source", s!"universe:{su.getD ""}"],
    algAt0 2 tgt (.rule (.lift (.map (identityPhi n) (selfCerts n eqs) [])) [1])
      ["side:target", s!"universe:{tu.getD ""}", s!"relation:{rel}"]]
  pure { items, requested := [2] }

/-! ## Cover refutation in a point universe (GP-X368, GP-X369) -/

/-- A declared cover of the parent by the empty branch family (encoded natively as branches whose
equations are nonzero constants). A point of the parent outside every branch is a point of the
parent, so noncoverage in a universe is the parent's claim in that universe. The geometric test is
not assumed: the parent's NOT_IN_IDEAL(1) is checked by a `properCoeff` receipt. In the
algebraic-closure universe that refutes the cover; in the BASE universe the geometric result is
offered for the rational claim by R3 along the identity, which has no row. -/
def coverUniverseFamily (inputs : Json) : Except String Plan3 := do
  unless str? inputs "coefficient_domain" == some "Q" do throw "only covers over Q are decoded"
  let vars ← strs inputs "variables"
  let n := vars.length
  let eqs ← (← strs inputs "parent_equations").mapM (canonP vars)
  unless (← strs inputs "semantic_branches").isEmpty do throw "only the empty branch family is decoded"
  let native ← match obj? inputs "native_empty_union_encoding" with
    | some (.arr bs) => bs.toList.mapM strList
    | _ => throw "no native encoding"
  for b in native do
    for t in b do
      match ← parse vars t with
      | [(mono, c)] => unless c != 0 && mono.all (· == 0) do throw "a native branch is not empty"
      | _ => throw "a native branch is not empty"
  let u := str? inputs "point_universe"
  let kind ← universeKind3 n u
  let geometric : Stmt := ⟨vars, eqs, [], .notInIdeal (oneP n)⟩
  let test := algAt0 1 geometric (properSupport geometric) ["geometric_test"]
  if kind == .nonempty then
    pure { items := [test, algAt0 2 { geometric with kind } (.rule (.lift (.map (identityPhi n) (selfCerts n eqs) [])) [1])
      [s!"universe:{u.getD ""}"]], requested := [2] }
  else pure { items := [test], requested := [1] }

/-! ## Image versus closure (GP-A07a, GP-A07b) -/

/-- `equations`, `projection`, `reading` and `point`. The source is the locus of the equations over
ℚ (characteristic 0, geometric points); the closure ambient is the space of the projected variables.

- `existential`: the image is nonempty iff the source is (the projection is total). The source's
  NOT_IN_IDEAL(1) is checked by a `properCoeff` receipt and carried forward to the closure ambient
  by R3 along the projection.
- `specific witness`: the selected closure point (a `properCoeff` receipt on its coordinate
  equations) is offered for the fiber over it, by R3 along the projection. R3 carries points from
  the source of the map to its target only, and the projection's source is the fiber: lifting
  needs a section, so the step has no row (Chevalley: a closure point need not be in the image). -/
def imageFamily (inputs : Json) : Except String Plan3 := do
  let eqT ← strs inputs "equations"
  let proj ← strs inputs "projection"
  let vars := (eqT.flatMap identifiers).eraseDups
  unless proj.all vars.contains && proj.eraseDups.length == proj.length do throw "projection is not onto source variables"
  let n := vars.length
  let eqs ← eqT.mapM (canonP vars)
  let phi ← proj.mapM (canonP vars)
  let src : Stmt := ⟨vars, eqs, [], .notInIdeal (oneP n)⟩
  match str? inputs "reading" with
  | some "existential" =>
    unless (obj? inputs "point").all (· == .null) do throw "an existential reading carries no point"
    let closure : Stmt := ⟨proj, [], [], .notInIdeal (oneP proj.length)⟩
    pure { items := [algAt0 1 src (properSupport src) ["image:source"],
      algAt0 2 closure (.rule (.lift (.map phi [] [])) [1]) ["image:closure"]], requested := [1, 2] }
  | some "specific witness" =>
    let pt ← need (obj? inputs "point") "no point"
    let coordEqs ← proj.mapM fun v => do canonP proj s!"{v}-({← text (← need (obj? pt v) s!"point lacks {v}")})"
    let fiberEqs ← proj.mapM fun v => do canonP vars s!"{v}-({← text (← need (obj? pt v) s!"point lacks {v}")})"
    let point : Stmt := ⟨proj, coordEqs, [], .notInIdeal (oneP proj.length)⟩
    let fiber : Stmt := ⟨vars, eqs ++ fiberEqs, [], .notInIdeal (oneP n)⟩
    let noCerts : List Cert := fiber.eqs.map fun _ => .ideal .rat [] 0 0
    let lift : Support3 := .rule (.lift (.map phi noCerts [])) [1]
    pure { items := [algAt0 1 point (properSupport point) ["image:closure_point"],
      algAt0 2 fiber lift ["image:fiber"]], requested := [2] }
  | _ => throw "unknown reading"

/-! ## Diagnostics -/

/-- Why a lifted 3a rule refuses when the direction table has no row for its statements
(reporting only; the verdict is the fold's). -/
def liftNoRow (p : Plan3) (i : Item3) (d : RuleData) (ps : List Nat) : Option String :=
  let algOf (s : Stmt3) : Option Stmt := match s with | .alg s => some s | _ => none
  match algOf i.stmt, ps.mapM fun k => (p.items.find? (·.key == k)).bind fun j => algOf j.stmt with
  | some c, some prem =>
    if (ruleReach c prem d).isNone then
      some "rule refused: no direction-table row carries the premise's kind to the conclusion's along this relation"
    else none
  | _, _ => none

end GPProfile.Real
