import GPProfile.Frontend
import GPProfile.Plan
import GPProfile.Univariate

/-! Family adapters: JSON helpers, polynomial parsing and the input-key checks every family shares. -/

namespace GPProfile.Families
open Lean GPProfile

/-! ## JSON helpers -/

def obj? (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption
def has (j : Json) (k : String) : Bool := (obj? j k).isSome
def str? (j : Json) (k : String) : Option String := (obj? j k).bind (·.getStr?.toOption)
def strList (j : Json) : Except String (List String) := do (← j.getArr?).toList.mapM Json.getStr?
def strs (j : Json) (k : String) : Except String (List String) :=
  match obj? j k with | some v => strList v | none => pure []
def nats (j : Json) (k : String) : Except String (List Nat) :=
  match obj? j k with | some v => do (← v.getArr?).toList.mapM Json.getNat? | none => pure []
def text (j : Json) : Except String String :=
  match j with
  | .str s => pure s
  | .num n => pure (toString n)
  | _ => throw "expected a polynomial string or number"

/-- The requested scope and replay field from the case's characteristic fields. -/
def scopeField (inputs : Json) : Except String (Scope × Field) := do
  let p ← characteristic inputs []
  pure (if p == 0 then (.char0Only, .rat) else (.only p, .prime p))

def P (vars : List String) (t : String) : Except String Sparse := parse vars t

/-- A parsed polynomial in canonical form: `parse` output already is (`canonP_eq`). -/
def canonP (vars : List String) (t : String) : Except String Sparse := P vars t

theorem canonP_eq (vars : List String) (t : String) :
    canonP vars t = (do let p ← P vars t; pure ((canonical vars.length p).getD p)) := by
  unfold canonP
  cases h : P vars t with
  | error e => rfl
  | ok s => simp only [bind, Except.bind, pure, Except.pure, canonical_parse h, Option.getD_some]

def one (n : Nat) : Sparse := oneP n

def mkItem (key : Nat) (stmt : Stmt) (scope : Scope) (support : Support) (extra : List String := []) : Item :=
  { key, stmt, scope, extra, support }

def single (stmt : Stmt) (scope : Scope) (support : Support) : Plan :=
  { items := [{ key := 1, stmt, scope, support }], requested := [1] }

def splitEq (t : String) : Except String (String × String) :=
  match t.splitOn "=" with
  | [l, r] => pure (l, r)
  | [l] => pure (l, "0")
  | _ => throw "identity must have at most one '='"

/-- `p * q` in canonical sparse form. -/
def mulS (n : Nat) (p q : Sparse) : Option Sparse := do
  let a ← toHexQ n p
  let b ← toHexQ n q
  pure (ofHex (a * b))

def subS (n : Nat) (p q : Sparse) : Option Sparse := do
  let a ← toHexQ n p
  let b ← toHexQ n q
  pure (ofHex (a - b))

def powS (n : Nat) (p : Sparse) (k : Nat) : Option Sparse := do
  let a ← toHexQ n p
  pure (ofHex (a ^ k))

def need {α : Type} (o : Option α) (msg : String) : Except String α :=
  match o with | some a => pure a | none => throw msg

/-- A total map on `vars`, as source polynomials in the given order. -/
def totalMap (images : Json) (domain codomain : List String) : Except String (List Sparse) :=
  domain.mapM fun v => match obj? images v with
    | some t => do P codomain (← text t)
    | none => throw s!"incomplete map: no image for {v}"

/-- A family applies only when every input key is one it reads (or ignores as provenance) and
the fixed fields it requires have the stated values. Anything else is an expressiveness loss:
the frontend never guesses past a key it does not understand. -/
def onlyKeys (inputs : Json) (allowed : List String) : Bool :=
  match inputs with
  -- `meta` is the explicit ignored namespace for provenance notes (G3a review §4).
  | .obj kvs => kvs.toList.all fun (k, _) => k == "meta" || allowed.contains k
  | _ => false

/-- A nested model object: only these keys, and a rational field when one is named. -/
def modelOk (j : Json) : Bool :=
  onlyKeys j ["field", "variables", "equations", "nonzero"] &&
    (str? j "field").all fun f => (fieldChar? f).isSome && f != "R" && f != "RR"

def nestedOk (inputs : Json) (key : String) (allowed : List String) : Bool :=
  (obj? inputs key).all fun j => onlyKeys j allowed

def questionIs (inputs : Json) (qs : List String) : Bool :=
  match str? inputs "question" with
  | some q => qs.contains q
  | none => true

/-- A scalar factor is a constant or a declared unit. -/
def scalarOk (inputs : Json) (scalar : Option String) : Except String Bool := do
  let some sc := scalar | return true
  let units ← strs inputs "declared_units"
  let ids := identifiers sc
  pure (ids.all units.contains)

def legacyKeys : List String :=
  ["variables", "generators", "cofactors", "target", "characteristic", "target_characteristic",
    "guards", "exponent", "point", "reduced_point", "identity", "source_ideal", "cofactor",
    "source_context", "target_context"]

end GPProfile.Families
