import GPCensus.Profile
import Lean.Data.Json

/-!
The census runner: JSON in, Kernel verdicts out. It only constructs profile inputs (statements,
scopes, certificates); every verdict comes from the fold under `GPCensus.admission`.

Formulas are JSON with named variables, converted to de Bruijn indices:
`true`, `{"adj": ["x","y"]}`, `{"eq": ["x","y"]}`, `{"color": ["x", c]}`, `{"not": φ}`,
`{"and": [φ, …]}`, `{"or": [φ, …]}`, `{"exists": "x", "body": φ}`, `{"forall": "x", "body": φ}`,
`{"atLeast": m, "var": "x", "body": φ}`.

Extension covers (HW61 G-5): a NONE claim may give `"extension": {"base_g6", "k", "patterns"}` in
place of a predicate; its predicate is `Extension.extPred` of that base, degree and pattern list
(each pattern `{"n", "edges", "non_edges"}`). An `extcover` certificate repeats the three and names
a hits file, one line `S;p;map` per neighbourhood in generator order (`;;` for none).

usage: gp_census cnf <claim.json> <n>             print the DIMACS CNF GP refutes for NONE at n
       gp_census combos <n> <k>                   print the extension generator's neighbourhoods
       gp_census listcnf <claim.json> <listing.json>  the CNF a `listed` certificate refutes
       gp_census run <ledger.json>                print each claim's status after the fold
-/

namespace GPCensus.Run
open Lean GP50 GPCensus

def str? (j : Json) (k : String) : Option String := (j.getObjValAs? String k).toOption
def nat? (j : Json) (k : String) : Option Nat := (j.getObjValAs? Nat k).toOption

def need {α : Type} (o : Option α) (msg : String) : Except String α :=
  match o with
  | some a => pure a
  | none => throw msg

def varIdx (bound : List String) (x : Json) : Except String Nat := do
  let name ← x.getStr?
  need (bound.idxOf? name) s!"unbound variable {name}"

partial def formula (bound : List String) (j : Json) : Except String Formula := do
  if j == Json.bool true then return .tt
  if j == Json.bool false then return .not .tt
  let pair (k : String) : Except String (Nat × Nat) := do
    match (← j.getObjVal? k).getArr? with
    | .ok #[x, y] => pure (← varIdx bound x, ← varIdx bound y)
    | _ => throw s!"{k} takes two variables"
  match j.getObjVal? "adj", j.getObjVal? "eq", j.getObjVal? "color" with
  | .ok _, _, _ => let (i, k) ← pair "adj"; return .adj i k
  | _, .ok _, _ => let (i, k) ← pair "eq"; return .eq i k
  | _, _, .ok (.arr #[x, c]) => return .color (← varIdx bound x) (← c.getNat?)
  | _, _, _ => pure ()
  if let .ok (.arr #[g, x, y]) := j.getObjVal? "act" then
    return .act (← g.getNat?) (← varIdx bound x) (← varIdx bound y)
  if let .ok φ := j.getObjVal? "not" then return .not (← formula bound φ)
  let list (k : String) (unit : Formula) (op : Formula → Formula → Formula) : Except String (Option Formula) := do
    match j.getObjVal? k with
    | .ok (.arr fs) =>
      let gs ← fs.toList.mapM (formula bound)
      pure (some (match gs.reverse with
        | [] => unit
        | g :: rest => rest.foldl (fun acc h => op h acc) g))
    | _ => pure none
  if let some f ← list "and" .tt .and then return f
  if let some f ← list "or" (.not .tt) .or then return f
  let body (x : String) : Except String Formula := do formula (x :: bound) (← j.getObjVal? "body")
  if let some x := str? j "exists" then return .ex (← body x)
  if let some x := str? j "forall" then return .all (← body x)
  if let some m := nat? j "atLeast" then
    return .atLeast m (← body (← need (str? j "var") "atLeast needs a var"))
  throw s!"not a formula: {j.compress}"

def witness (j : Json) : Except String Witness := do
  let edges ← (← (← j.getObjVal? "edges").getArr?).toList.mapM fun e => do
    match e.getArr? with
    | .ok #[a, b] => pure (← a.getNat?, ← b.getNat?)
    | _ => throw "an edge is a pair"
  let colors ← match j.getObjVal? "colors" with
    | .ok (.arr cs) => cs.toList.mapM Json.getNat?
    | _ => pure []
  pure ⟨edges, colors⟩

def kind (j : Json) : Except String Kind := do
  match ← need (str? j "kind") "no kind" with
  | "EXISTS" => pure .exists_
  | "NONE" => pure .none_
  | "EXHAUSTIVE" => pure (.exhaustive (← (← (← j.getObjVal? "list").getArr?).toList.mapM witness))
  | "COUNT" =>
    let m ← need (nat? j "count") "COUNT needs a count"
    match j.getObjVal? "assuming_complete" with
    | .ok (.arr ws) => pure (.countGiven (← ws.toList.mapM witness) m)
    | _ => pure (.count m)
  | "V4_COUNT" =>
    let pts ← need (nat? j "points") "V4_COUNT needs points"
    let a0 ← (← (← j.getObjVal? "action").getArr?).toList.mapM fun g => do (← g.getArr?).toList.mapM Json.getNat?
    let m ← need (nat? j "count") "V4_COUNT needs a count"
    match j.getObjVal? "assuming_complete" with
    | .ok (.arr ws) => pure (.v4CountGiven pts a0 (← ws.toList.mapM witness) m)
    | _ => pure (.v4Count pts a0 m)
  | k => throw s!"unknown kind {k}"

/-- A graph6 string (n < 63) as its vertex count and edge list. -/
def graph6 (s : String) : Except String (Nat × List (Nat × Nat)) := do
  let ds := s.toList.map fun c => c.toNat - 63
  let n ← match ds with
    | n :: _ => if n < 63 then pure n else throw "graph6: n >= 63 is not supported"
    | [] => throw "graph6: empty"
  let bits := (ds.drop 1).flatMap fun x => (List.range 6).map fun i => (x >>> (5 - i)) % 2 == 1
  let pairs := (List.range n).flatMap fun j => (List.range j).map fun i => (i, j)
  unless bits.length ≥ pairs.length && ds.all (· < 64) do throw "graph6: malformed"
  pure (n, (pairs.zip bits).filterMap fun (e, b) => if b then some e else none)

def pairs (j : Json) : Except String (List (Nat × Nat)) := do
  (← j.getArr?).toList.mapM fun e => do
    match e.getArr? with
    | .ok #[a, b] => pure (← a.getNat?, ← b.getNat?)
    | _ => throw "an edge is a pair"

def pattern (j : Json) : Except String Extension.Pattern := do
  pure ⟨← need (nat? j "n") "a pattern names its n", ← pairs (← j.getObjVal? "edges"),
    ← match j.getObjVal? "non_edges" with
      | .ok ne => pairs ne
      | .error _ => pure []⟩

/-- Base (as `n` and edges), degree and patterns of an extension spec. -/
def extSpec (j : Json) : Except String (Nat × List (Nat × Nat) × Nat × List Extension.Pattern) := do
  let (n, E) ← graph6 (← need (str? j "base_g6") "an extension names its base_g6")
  pure (n, E, ← need (nat? j "k") "an extension names its k",
    ← (← (← j.getObjVal? "patterns").getArr?).toList.mapM pattern)

def stmt (j : Json) : Except String Stmt := do
  if let .ok e := j.getObjVal? "extension" then
    let (n, E, k, pats) ← extSpec e
    return ⟨(nat? j "colors").getD 1, Extension.extPred n (Extension.table n E) k pats, ← kind j⟩
  pure ⟨(nat? j "colors").getD 1, ← formula [] (← j.getObjVal? "predicate"), ← kind j⟩

def natList (s : String) : Except String (List Nat) :=
  if s.isEmpty then pure [] else
  (s.splitOn ",").mapM fun t => match t.toNat? with
    | some v => pure v
    | none => throw s!"not a natural: {t}"

/-- One hits line `S;p;map`; an empty `p` (no hit) becomes an out-of-range pattern index. -/
def hitLine (l : String) : Except String Extension.Hit := do
  match l.splitOn ";" with
  | [S, p, m] =>
    let pat ← if p.isEmpty then pure (2 ^ 32) else need p.toNat? s!"bad pattern index {p}"
    pure ⟨← natList S, pat, ← natList m⟩
  | _ => throw s!"bad hits line: {l}"

def cube (j : Json) : Except String LRATCatcher.Cube :=
  do (← j.getArr?).toList.mapM fun l => do
    let i : Int ← l.getInt?
    pure (i.natAbs - 1, decide (0 < i))

/-- A representative: its witness and its action (three image lists over all vertices). -/
def rep (j : Json) : Except String (Witness × List (List Nat)) := do
  pure (← witness (← j.getObjVal? "witness"),
    ← (← (← j.getObjVal? "action").getArr?).toList.mapM fun g => do (← g.getArr?).toList.mapM Json.getNat?)

def cert (j : Json) : Except String Cert := do
  let n ← need (nat? j "n") "a certificate names its n"
  match ← need (str? j "type") "no certificate type" with
  | "witness" => pure (.witness n (← witness (← j.getObjVal? "witness")))
  | "catalog" => pure (.catalog n)
  | "lrat" => pure (.lrat n (← need (str? j "proof") "no proof"))
  | "listed" =>
    pure (.listed n (← (← (← j.getObjVal? "list").getArr?).toList.mapM witness)
      (← (← (← j.getObjVal? "labels").getArr?).toList.mapM fun l => do
        (← l.getArr?).toList.mapM Json.getNat?)
      ((str? j "proof").getD ""))
  | "cover" =>
    pure (.cover n (← (← (← j.getObjVal? "cubes").getArr?).toList.mapM cube)
      (← (← (← j.getObjVal? "leaves").getArr?).toList.mapM Json.getStr?)
      (← need (str? j "cover_proof") "no cover proof") ((j.getObjValAs? Bool "relative").toOption.getD false))
  | "v4listed" =>
    pure (.v4listed n (← (← (← j.getObjVal? "models").getArr?).toList.mapM witness)
      (← (← (← j.getObjVal? "reps").getArr?).toList.mapM rep)
      (← (← (← j.getObjVal? "labels").getArr?).toList.mapM fun l => do (← l.getArr?).toList.mapM Json.getNat?)
      ((str? j "proof").getD ""))
  | "v4catalog" => pure (.v4catalog n (← (← (← j.getObjVal? "reps").getArr?).toList.mapM rep))
  | "extcover" =>
    let (b, E, k, pats) ← extSpec j
    unless n == b + 1 do throw "an extcover certificate's n is its base size plus one"
    let text ← need (str? j "hits_text") "an extcover certificate needs its hits"
    let lines := (text.splitOn "\n").filter (!·.isEmpty)
    pure (.extCover b k E pats (← lines.mapM hitLine))
  | t => throw s!"unknown certificate type {t}"

/-- A statement's binding: its exact canonical form and scope. -/
def bindingOf (s : Stmt) (scope : Scope) : Binding :=
  { statementHash := reprStr s, scopeHash := reprStr scope, modelHash := "gp-census/v1",
    inputHashes := [], authority := "census", authorityVersion := 1, kernelVersion := 1 }

structure Item where
  key : Nat
  stmt : Stmt
  scope : Scope
  cert : Option Cert

def item (j : Json) : Except String Item := do
  let scope ← (← (← j.getObjVal? "scope").getArr?).toList.mapM Json.getNat?
  let cert ← match j.getObjVal? "certificate" with
    | .ok c => some <$> cert c
    | .error _ => pure none
  pure ⟨← need (nat? j "key") "claim without key", ← stmt j, scope, cert⟩

def runLedger (j : Json) : Except String Json := do
  let items ← (← (← j.getObjVal? "claims").getArr?).toList.mapM item
  let clauses : List Clause := items.map fun i => ⟨i.key, 1, bindingOf i.stmt i.scope, i.stmt, i.scope⟩
  let receipts : List Receipt := items.filterMap fun i =>
    i.cert.map fun c => ⟨s!"receipt-{i.key}", i.key, 1, bindingOf i.stmt i.scope, c⟩
  let events : List Event := items.flatMap fun i =>
    [Event.declareClaim i.key, .current ⟨i.key, 1, bindingOf i.stmt i.scope⟩] ++
      (if i.cert.isSome then [.warrant ⟨i.key, i.key, 1, bindingOf i.stmt i.scope, .receipt s!"receipt-{i.key}"⟩]
       else [])
  match fold (admission clauses receipts) events with
  | .error e => throw s!"fold refused the log: {e}"
  | .ok state =>
    pure (Json.mkObj [("schema", "gp-census-run/v1"), ("claims", toJson (items.map fun i =>
      let checked := i.cert.map fun c => check i.stmt i.scope c
      Json.mkObj [("key", toJson i.key), ("held", toJson (held state i.key)),
        ("reach", toJson ((i.cert.bind (reach i.stmt ·)).map (·))), ("check", toJson checked)]))])

end GPCensus.Run

/-- Read each `extcover` certificate's `hits_file` into `hits_text`. -/
def inlineHits (j : Lean.Json) : IO Lean.Json := do
  let some claims := (j.getObjVal? "claims" >>= (·.getArr?)).toOption | return j
  let claims ← claims.mapM fun c => do
    match c.getObjVal? "certificate" with
    | .ok cert =>
      match (cert.getObjValAs? String "hits_file").toOption with
      | some path => return c.setObjVal! "certificate" (cert.setObjVal! "hits_text" (← IO.FS.readFile path))
      | none => return c
    | .error _ => return c
  return j.setObjVal! "claims" (Lean.Json.arr claims)

open GPCensus GPCensus.Run in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["combos", nStr, kStr] =>
    let (some n, some k) := (nStr.toNat?, kStr.toNat?) | IO.eprintln "n and k must be naturals"; return 2
    for S in Extension.combos n k do IO.println (",".intercalate (S.map toString))
    return 0
  | ["cnf", path, nStr] =>
    let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
    let s ← IO.ofExcept (stmt j)
    let some n := nStr.toNat? | IO.eprintln "n must be a natural"; return 2
    let f := cnf n s.colors s.pred
    if !LRATCatcher.dimacsRoundTrip f then IO.eprintln "DIMACS round trip failed"; return 1
    IO.print f.dimacs
    return 0
  | ["listcnf", path, listing] =>
    let s ← IO.ofExcept (stmt (← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))))
    match ← IO.ofExcept (cert (← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile listing)))) with
    | .listed n list labels _ =>
      match list.mapM (decode n s.colors), labels.mapM (labelOf n) with
      | some Bs, some ls =>
        IO.print (listCnf n s.colors s.pred ls Bs).dimacs
        return 0
      | _, _ => IO.eprintln "a listed object or a relabelling does not decode"; return 1
    | _ => IO.eprintln "listcnf takes a listed certificate"; return 2
  | ["v4listcnf", path, listing] =>
    let s ← IO.ofExcept (stmt (← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))))
    match s.kind, ← IO.ofExcept (cert (← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile listing)))) with
    | .v4Count pts a0 _, .v4listed n models _ labels _ =>
      match models.mapM (decode n s.colors), labels.mapM (labelOf n) with
      | some Bs, some ls =>
        IO.print (v4ListCnf n s.colors pts a0 s.pred ls Bs).dimacs
        return 0
      | _, _ => IO.eprintln "a model or a relabelling does not decode"; return 1
    | _, _ => IO.eprintln "v4listcnf takes a V4_COUNT claim and a v4listed certificate"; return 2
  | ["run", path] =>
    let j ← inlineHits (← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path)))
    match runLedger j with
    | .ok out => IO.println out.compress; return 0
    | .error e => IO.eprintln e; return 1
  | _ => IO.eprintln "usage: gp_census (cnf <claim.json> <n> | run <ledger.json>)"; return 2
