import GP50.Queries
import GPProfile.Frontend
import GPProfile.Canonical

/-!
The §3.6 receipt reach slice. Per case: the shared frontend builds profile inputs; the
untrusted proposer files the requested claim and its receipt warrant through the commit
guard; the Kernel fold decides. The proposer then files the widest claim each held receipt's
reach allows (§1.9), and the earned surface shows it. Authority comes only from the fold.
-/

namespace GPProfile.Slice
open Lean GP50

/-! ## Proposer (untrusted) -/

def bindingFor (stmt : Stmt) (scope : Scope) (field : Field) : Binding :=
  { statementHash := stmtCanon stmt, scopeHash := scopeCanon scope, modelHash := "gp-profile-3a/v1"
    inputHashes := [reprStr field], authority := "3a-reach-slice", authorityVersion := 1,
    kernelVersion := 1 }

structure Ledger where
  clauses : List Clause
  receipts : List Receipt
  events : List Event

def Ledger.admission (l : Ledger) : Admission := GPProfile.admission l.clauses l.receipts

/-- File a claim with one receipt warrant. The commit guard lands the append only if the
resulting log still folds (post-G2 §1.5). -/
def Ledger.file (l : Ledger) (key : Nat) (stmt : Stmt) (scope : Scope) (cert : Cert) :
    Except String Ledger := do
  let b := bindingFor stmt scope cert.field
  let name := s!"receipt-{key}"
  let next : Ledger := {
    clauses := l.clauses ++ [⟨key, 1, b, stmt, scope⟩]
    receipts := l.receipts ++ [⟨name, key, 1, b, cert⟩]
    events := l.events ++ [.declareClaim key, .current ⟨key, 1, b⟩,
      .warrant ⟨key, key, 1, b, .receipt name⟩] }
  match fold next.admission next.events with
  | .ok _ => pure next
  | .error e => throw s!"commit guard refused append: {e}"

def _root_.GPProfile.Cert.withField : Cert → Field → Cert
  | .ideal _ qs m k, f => .ideal f qs m k
  | .point _ vs, f => .point f vs
  | .proper _ a b, f => .proper f a b
  | c, _ => c

/-- The widest strictly wider reach among re-replays of a held receipt's certificate. -/
def widen (stmt : Stmt) (scope : Scope) (cert : Cert) : Option (Scope × Cert) :=
  let candidates := [cert, cert.withField .rat].eraseDups.filterMap fun c =>
    (reach stmt c).map (·, c)
  let wider := candidates.filter fun (r, _) => scope.le r && !r.le scope
  (wider.find? fun (r, _) => wider.all fun (r', _) => r'.le r).orElse fun _ => wider.head?

/-! ## Presentation -/

def sparseJson (vars : List String) (p : Sparse) : Json :=
  if p.isEmpty then "0" else
  Json.str <| " + ".intercalate <| p.map fun (e, c) =>
    let mono := ((vars.zip e).filter (·.2 != 0)).map fun (v, k) => if k == 1 then v else s!"{v}^{k}"
    let coeff := if c.den == 1 then toString c.num else s!"({c.num}/{c.den})"
    if mono.isEmpty then coeff else s!"{coeff}*{"*".intercalate mono}"

def kindJson (vars : List String) : Kind → Json
  | .empty => "EMPTY" | .nonempty => "NONEMPTY"
  | .inIdeal h => Json.mkObj [("IN_IDEAL", sparseJson vars h)]
  | .vanishesOn h => Json.mkObj [("VANISHES_ON", sparseJson vars h)]
  | .notInIdeal h => Json.mkObj [("NOT_IN_IDEAL", sparseJson vars h)]
  | .cover bs => Json.mkObj [("COVER", toJson bs.length)]

def stmtJson (s : Stmt) : Json := Json.mkObj [
  ("vars", toJson s.vars), ("eqs", toJson (s.eqs.map (sparseJson s.vars))),
  ("guards", toJson (s.guards.map (sparseJson s.vars))), ("kind", kindJson s.vars s.kind),
  ("s_stmt", toJson s.primes)]

def scopeJson (s : Scope) : Json := Json.mkObj [("char0", toJson s.char0),
  match s.primes with
  | .finite ps => ("primes", toJson ps)
  | .cofinite e => ("all_primes_except", toJson e)]

def fieldJson : Field → Json
  | .rat => "Q" | .prime p => s!"F_{p}"

def checkJson : Check → Json
  | .accepted r => Json.mkObj [("result", "ACCEPTED"), ("reach", scopeJson r)]
  | .notCanonical => Json.mkObj [("result", "NOT_CANONICAL")]
  | .illFormed s => Json.mkObj [("result", "ILL_FORMED"), ("s_stmt", toJson s)]
  | .replayFailed => Json.mkObj [("result", "REPLAY_FAILED")]
  | .outsideReach r => Json.mkObj [("result", "OUTSIDE_REACH"), ("reach", scopeJson r)]

/-! ## One case -/

def runCase (label : String) (case : Json) (params : List (String × Nat)) : Json :=
  let expected := (do (← (← case.getObjVal? "expected").getObjVal? "verdict").getStr?).toOption
  let base : List (String × Json) := [("id", toJson label), ("expected", toJson expected)]
  match frontend case params with
  | .error e => Json.mkObj (base ++ [("observed", Json.str "EXPRESSIVENESS_LOSS"), ("frontend_error", toJson e)])
  | .ok i =>
    let result : Except String Json := do
      let ledger ← ({ clauses := [], receipts := [], events := [] } : Ledger).file 1 i.stmt i.scope i.cert
      let state ← fold ledger.admission ledger.events
      let accepted := held state 1
      let (ledger, widened) ← if accepted then
          match widen i.stmt i.scope i.cert with
          | some (r, c) => do pure ((← ledger.file 2 i.stmt r c), some (r, c))
          | none => pure (ledger, none)
        else pure (ledger, none)
      let final ← fold ledger.admission ledger.events
      return Json.mkObj (base ++ ([
        ("observed", Json.str (if accepted then "ACCEPT" else "REFUSE")),
        ("statement", stmtJson i.stmt), ("requested_scope", scopeJson i.scope),
        ("field", fieldJson i.cert.field), ("check", checkJson (check i.stmt i.scope i.cert)),
        ("widened", match widened with
          | some (r, c) => Json.mkObj [("scope", scopeJson r), ("field", fieldJson c.field),
              ("held", toJson (held final 2))]
          | none => Json.null),
        ("held_claims", toJson final.claims),
        ("earned", toJson ((Queries.earned final [1] [] []).map (·.claim)))] : List (String × Json)))
    match result with
    | .ok j => j
    | .error e => Json.mkObj (base ++ [("observed", Json.str "MALFORMED"), ("error", toJson e)])

/-! ## Manifest -/

def params (entry : Json) : List (String × Nat) :=
  match entry.getObjVal? "parameters" with
  | .ok (.obj kvs) => kvs.toList.filterMap fun (k, v) => (v.getNat?.toOption).map (k, ·)
  | _ => []

def run (root : System.FilePath) (manifest : Json) : IO Json := do
  let entries ← IO.ofExcept ((← IO.ofExcept (manifest.getObjVal? "cases")).getArr?)
  let rows ← entries.toList.mapM fun entry => do
    let path : String ← IO.ofExcept (do (← entry.getObjVal? "path").getStr?)
    let case ← IO.ofExcept (Json.parse (← IO.FS.readFile (root / path)))
    let id := (do (← case.getObjVal? "id").getStr?).toOption.getD path
    let label := (do (← entry.getObjVal? "label").getStr?).toOption.getD id
    let start ← IO.monoNanosNow
    let row := runCase label case (params entry)
    -- Force evaluation before reading the clock again.
    let text := row.compress
    let stop ← IO.monoNanosNow
    pure (row.setObjVal! "elapsed_ms" (toJson ((stop - start) / 1000000 + (if text.isEmpty then 1 else 0))))
  let agree := rows.filter fun r =>
    (r.getObjVal? "expected").toOption == (r.getObjVal? "observed").toOption
  return Json.mkObj [("schema", "gp-reach-slice/v1"), ("case_count", toJson rows.length),
    ("agree", toJson agree.length), ("cases", toJson rows)]

end GPProfile.Slice

def main (args : List String) : IO UInt32 := do
  match args with
  | [root, manifestPath] =>
    let manifest ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile manifestPath))
    IO.println (← GPProfile.Slice.run root manifest).pretty
    return 0
  | _ => IO.eprintln "usage: gp_reach_slice <repo-root> <manifest.json>"; return 2
