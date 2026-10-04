import Lean
open Lean

namespace Spike
-- Finite toy only: natural-number equalities, named context sets, opaque SHA-256 labels.
structure Claim where
  id : String
  lhs : Nat
  rhs : Nat
  scope : Array String
  model : String
  modelHash : String
  checkerHash : String
  deriving Repr
structure Receipt where
  claim : Claim
  reach : Array String
  deriving Repr
inductive Event where
  | source (key digest : String)
  | declare (claim : Claim)
  | receipt (r : Receipt)
  | narrow (id parent : String) (scope : Array String)
  deriving Repr
structure State where
  sources : Array (String × String) := #[]
  claims : Array Claim := #[]
  receipts : Array Receipt := #[]
  narrows : Array (String × String × Array String) := #[]
  deriving Repr

def text (j : Json) (k : String) : Except String String := j.getObjVal? k >>= Json.getStr?
def nat (j : Json) (k : String) : Except String Nat := j.getObjVal? k >>= Json.getNat?
def strings (j : Json) (k : String) : Except String (Array String) := do
  let a ← j.getObjVal? k >>= Json.getArr?
  a.mapM Json.getStr?
def decodeClaim (j : Json) : Except String Claim := do
  let id ← text j "id"
  let lhs ← nat j "lhs"
  let rhs ← nat j "rhs"
  let sc ← strings j "scope"
  let model ← text j "model"
  let mh ← text j "model_hash"
  let ch ← text j "checker_hash"
  return ⟨id, lhs, rhs, sc, model, mh, ch⟩
def decode (j : Json) : Except String Event := do
  match ← text j "event" with
  | "source" => return .source (← text j "key") (← text j "hash")
  | "declare" => return .declare (← decodeClaim j)
  | "receipt" => return .receipt { claim := ← decodeClaim j, reach := ← strings j "reach" }
  | "narrow" => return .narrow (← text j "id") (← text j "parent") (← strings j "scope")
  | _ => throw "unknown event"
def subset (a b : Array String) : Bool := a.all b.contains
def fresh (s : State) (c : Claim) : Bool :=
  s.sources.any (fun (k,h) => k == c.model && h == c.modelHash) &&
  s.sources.any (fun (k,h) => k == "checker" && h == c.checkerHash)
def sameClaim (a b : Claim) : Bool :=
  a.id == b.id && a.lhs == b.lhs && a.rhs == b.rhs && a.scope == b.scope &&
  a.model == b.model && a.modelHash == b.modelHash && a.checkerHash == b.checkerHash
def checked (s : State) (c : Claim) : Bool :=
  fresh s c && c.lhs == c.rhs &&
  s.receipts.any (fun r => sameClaim c r.claim && subset c.scope r.reach)
def usedId (s : State) (id : String) : Bool :=
  s.claims.any (fun c => c.id == id) || s.narrows.any (fun (i,_,_) => i == id)
def step (s : State) (e : Event) : Except String State :=
  match e with
  | .source k h => return { s with sources := (s.sources.filter (fun p => p.1 != k)).push (k,h) }
  | .declare c => if usedId s c.id then throw "duplicate claim id" else
      return { s with claims := s.claims.push c }
  | .receipt r => return { s with receipts := s.receipts.push r }
  | .narrow i p sc => if usedId s i then throw "duplicate claim id" else
      return { s with narrows := s.narrows.push (i,p,sc) }
def resolve (s : State) : Nat → String → Option (Bool × Array String)
  | 0, _ => none
  | n+1, id =>
    match s.claims.find? (fun c => c.id == id) with
    | some c => some (checked s c, c.scope)
    | none => match s.narrows.find? (fun (i,_,_) => i == id) with
      | none => none
      | some (_,parent,sc) => do
        let (held,reach) ← resolve s n parent
        return (held && subset sc reach, sc)
def held (s : State) (id : String) : Bool :=
  ((resolve s (s.claims.size + s.narrows.size + 1) id).map Prod.fst).getD false
def summary (s : State) : Json :=
  Json.arr <| (s.claims.map fun c => Json.mkObj [("id", toJson c.id), ("held", toJson (held s c.id))]) ++
    (s.narrows.map fun (i,_,_) => Json.mkObj [("id", toJson i), ("held", toJson (held s i))])
def foldLines (lines : Array String) : Except String State := do
  lines.foldlM (fun s line => do
    let j ← Json.parse line
    let e ← decode j
    step s e) {}

-- The admitted toy checker proves only equality of two naturals.
theorem checked_equality (s : State) (c : Claim) (h : checked s c = true) : c.lhs = c.rhs := by
  simp only [checked, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.2
#print axioms checked_equality
end Spike
