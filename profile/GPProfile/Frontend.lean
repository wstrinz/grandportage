import Lean.Data.Json
import GPProfile.Algebra

/-!
The shared case-to-profile frontend (post-G2 §1.8). It constructs only profile inputs:
the statement AST, the requested scope, and raw certificate data. It never constructs
events, warrants, admission results or success flags. A case whose inputs fit none of the
shapes below is reported as an expressiveness loss, never as a pass.

Shapes, read from a case's `inputs`:
* `generators` + `cofactors` (+ `target`, default `1`; + `guards`, `exponent`):
  C1 EMPTY when the target is 1, otherwise C3 IN_IDEAL(target) with m = 1.
* `generators` + `point` (+ `guards`): C2 NONEMPTY.
* `identity` (`lhs=rhs`) + optional `source_ideal`/`cofactor`: C3 IN_IDEAL(lhs − rhs).
`characteristic`/`target_characteristic` gives both the requested scope and the replay
field (0 → ℚ, p → F_p). Variables come from `variables`, else from first appearance.
-/

namespace GPProfile
open Lean

structure Inputs where
  stmt : Stmt
  scope : Scope
  cert : Cert
  deriving Repr

def strings (json : Json) : Except String (List String) := do
  (← json.getArr?).toList.mapM Json.getStr?

def field? (json : Json) (key : String) : Option Json := (json.getObjVal? key).toOption

/-- A named coefficient field or context: the rationals and the complex numbers are char 0. -/
def fieldChar? (name : String) : Option Nat :=
  if ["Q", "QQ", "C", "CC", "R", "RR"].contains name then some 0 else none

/-- The field a case names. R/RR and C/CC are read as "every characteristic-0 field", which only
strengthens the claim (G3a review §4); the corpus run tags rows that pass that way. -/
def namedField? (inputs : Json) : Option String :=
  ["target_context", "coefficient_field", "coefficient_domain", "field"].findSome? fun k =>
    (field? inputs k).bind fun v => v.getStr?.toOption

def characteristic (inputs : Json) (params : List (String × Nat)) : Except String Nat := do
  let named := ["target_context", "coefficient_field", "coefficient_domain", "field"].findSome? fun k =>
    (field? inputs k).bind fun v => (v.getStr?.toOption).bind fieldChar?
  let raw ← match field? inputs "characteristic", field? inputs "target_characteristic", named with
    | some v, _, _ | none, some v, _ => pure v
    | none, none, some c => pure (toJson c)
    | none, none, none => pure (toJson (0 : Nat))
  match raw.getNat?, raw.getStr? with
  | .ok n, _ => pure n
  | _, .ok s => match params.lookup s with
    | some n => pure n
    | none => throw s!"unbound characteristic parameter {s}"
  | _, _ => throw "characteristic must be a natural or a parameter name"

def splitIdentity (text : String) : Except String String :=
  match text.splitOn "=" with
  | [lhs, rhs] => pure s!"({lhs})-({rhs})"
  | _ => throw "identity must have exactly one '='"

def frontend (case : Json) (params : List (String × Nat)) : Except String Inputs := do
  let inputs ← case.getObjVal? "inputs"
  let p ← characteristic inputs params
  let field : Field := if p == 0 then .rat else .prime p
  let scope : Scope := if p == 0 then .char0Only else .only p
  let opt (key : String) : Except String (List String) :=
    match field? inputs key with | some v => strings v | none => pure []
  let generators ← opt "generators"
  let guards ← opt "guards"
  let identity? := (field? inputs "identity").bind (·.getStr?.toOption)
  let identity ← match identity? with | some t => some <$> splitIdentity t | none => pure none
  let sourceIdeal ← opt "source_ideal"
  let cofactors ← match field? inputs "cofactors", field? inputs "cofactor" with
    | some v, _ => strings v
    | none, some v => (fun s => [s]) <$> v.getStr?
    | none, none => pure []
  let target := (field? inputs "target").bind (·.getStr?.toOption) |>.getD "1"
  let texts := generators ++ guards ++ sourceIdeal ++ cofactors ++ identity.toList ++ [target]
  let vars ← match field? inputs "variables" with
    | some v => strings v
    | none => pure ((texts.flatMap identifiers).eraseDups.filter fun v => (params.lookup v).isNone)
  let parse' (t : String) := parse vars t params
  let guardsP ← guards.mapM parse'
  let one := [(List.replicate vars.length 0, (1 : Rat))]
  if let some pointJson := field? inputs "point" then
    let values ← vars.mapM fun v => do
      let raw ← (pointJson.getObjVal? v).mapError (fun _ => s!"point lacks {v}")
      match (parse [] (← raw.getStr?) params) with
      | .ok [] => pure (0 : Rat)
      | .ok [([], c)] => pure c
      | _ => throw s!"point coordinate {v} is not a rational constant"
    return ⟨⟨vars, ← generators.mapM parse', guardsP, .nonempty⟩, scope, .point field values⟩
  if let some h := identity then
    let eqs := if sourceIdeal.isEmpty then [h] else sourceIdeal
    let qs := if cofactors.isEmpty then ["1"] else cofactors
    return ⟨⟨vars, ← eqs.mapM parse', guardsP, .inIdeal (← parse' h)⟩, scope,
      .ideal field (← qs.mapM parse') 1 0⟩
  if (field? inputs "generators").isSome && (field? inputs "cofactors").isSome then
    let t ← parse' target
    let k := ((field? inputs "exponent").bind (·.getNat?.toOption)).getD 0
    let kind := if t == one then Kind.empty else .inIdeal t
    let m := if t == one then 0 else 1
    return ⟨⟨vars, ← generators.mapM parse', guardsP, kind⟩, scope,
      .ideal field (← cofactors.mapM parse') m k⟩
  throw "inputs fit no 3a frontend shape"

end GPProfile
