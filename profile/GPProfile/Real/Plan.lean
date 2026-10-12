import GP50.Queries
import GPProfile.Plan
import GPProfile.Real.Admission

/-!
3b case plans: 3a's `Plan`, over the summed profile `ops3`. A frontend turns a case into profile
inputs only (statements, scopes, certificates, rule data); the untrusted proposer files each item
through the commit guard; the Kernel fold with `admission3` decides; the case is ACCEPT only when
every requested claim is held. Authority never comes from the plan itself.

3a's fast filing paths are not reused: 3b corpus plans have a handful of items, so every append is
guarded separately (`Ledger3.file`).
-/

namespace GPProfile.Real
open Lean GP50 GPProfile

/-- How an item is offered support. -/
inductive Support3 where
  | none
  /-- A receipt. `boundTo` binds it to a different statement (a detached receipt: the Kernel's exact
  binding check refuses it, GP-X02, GP-X311). -/
  | receipt (cert : Cert3) (boundTo : Option Stmt3 := none)
  | rule (data : RuleData3) (premises : List Nat)
  /-- The Kernel's narrowing (K2) from a held claim of the same statement at a wider scope. -/
  | narrow (premise : Nat)
  /-- An inference route audit with these premise steps and no registered rule instance (the v0.37
  zero-step audit, GP-X343). Filed as a derived warrant; no rule admits it, so it is never evidence. -/
  | route (steps : List Nat)

structure Item3 where
  key : Nat
  stmt : Stmt3
  scope : Scope3
  /-- Binding inputs beyond the statement. -/
  extra : List String := []
  /-- The binding inputs a receipt was issued against, when not the claim's own (a receipt pinned to
  a fixture, offered for a claim about a mutated fixture: the Kernel's exact binding check refuses). -/
  receiptExtra : Option (List String) := none
  support : Support3

structure Plan3 where
  items : List Item3
  requested : List Nat
  /-- Refusals decided while elaborating the case. -/
  elaboration : Option String := none

/-! ## Canonical binding text -/

def existCanon : Exist → String
  | .empty => "EMPTY"
  | .nonempty => "NONEMPTY"

/-- The canonical text of a real system: `[vars, eqs, guards, [[poly, sign], ...]]`. -/
def realCanon (r : RealSys) (e : Exist) : Json :=
  Json.arr #[toJson r.vars, Json.arr (r.eqs.map sparseCanon).toArray,
    Json.arr (r.guards.map sparseCanon).toArray,
    Json.arr (r.signs.map fun (p, σ) => Json.arr #[sparseCanon p, toJson σ]).toArray, Json.str (existCanon e)]

def ratsCanon (cs : List Rat) : Json := Json.arr (cs.map fun c => Json.str (toString c)).toArray

/-- The canonical text of a number-field point: `[m, r, vars, eqs, guards, coords]`. -/
def nfCanon (p : NFPoint) : Json :=
  Json.arr #[ratsCanon p.m, Json.arr (p.r.map ratsCanon).toArray, toJson p.vars,
    Json.arr (p.eqs.map sparseCanon).toArray, Json.arr (p.guards.map sparseCanon).toArray,
    Json.arr (p.coords.map fun c => Json.arr (c.map ratsCanon).toArray).toArray]

/-- The canonical text of a 3b statement; the family is part of the text. -/
def stmt3Canon : Stmt3 → String
  | .alg s => (Json.arr #["ALG", Json.str (stmtCanon s)]).compress
  | .orderFree s => (Json.arr #["ORDER_FREE", Json.str (stmtCanon s)]).compress
  | .real r e => (Json.arr #["REAL", realCanon r e]).compress
  | .nf p => (Json.arr #["NUMBER_FIELD", nfCanon p]).compress
  | .realCover r bs =>
    let branch (b : RBranch) : Json := Json.arr #[Json.arr (b.eqs.map sparseCanon).toArray,
      Json.arr (b.guards.map sparseCanon).toArray,
      Json.arr (b.signs.map fun (p, σ) => Json.arr #[sparseCanon p, toJson σ]).toArray]
    (Json.arr #["REAL_COVER", realCanon r .nonempty, Json.arr (bs.map branch).toArray]).compress
  | .goal g =>
    let graphs (L : List EdgeList) : Json :=
      Json.arr (L.map fun l => Json.arr (l.map fun (i, j) => Json.arr #[toJson i, toJson j]).toArray).toArray
    match g with
    | .goal n m v => (Json.arr #["GOAL", toJson n, toJson m, toJson v]).compress
    | .cover n m L => (Json.arr #["GOAL_COVER", toJson n, toJson m, graphs L]).compress
    | .spine n m L => (Json.arr #["GOAL_SPINE", toJson n, toJson m, graphs L]).compress

def scope3Canon : Scope3 → String
  | .alg sc => (Json.arr #["ALG", Json.str (scopeCanon sc)]).compress
  | .semireal => "[\"SEMIREAL\"]"
  | .real => "[\"REAL\"]"
  | .ratField => "[\"RAT_FIELD\"]"

def binding3Of (stmt : Stmt3) (scope : Scope3) (extra : List String) : Binding :=
  { statementHash := stmt3Canon stmt, scopeHash := scope3Canon scope, modelHash := "gp-profile-3b/v1"
    inputHashes := extra, authority := "3b-corpus", authorityVersion := 1, kernelVersion := 1 }

/-! ## Filing -/

structure Ledger3 where
  clauses : List Clause3 := []
  receipts : List Receipt3 := []
  rules : List RuleInst3 := []
  events : List Event := []

def Ledger3.admission (l : Ledger3) : Admission := admission3 l.clauses l.receipts l.rules

/-- One item's clause, receipt or rule, and events, appended without the guard. -/
def Ledger3.fileRaw (l : Ledger3) (i : Item3) : Ledger3 :=
  let b := binding3Of i.stmt i.scope i.extra
  let clause : Clause3 := ⟨i.key, 1, b, i.stmt, i.scope⟩
  let declare := [Event.declareClaim i.key, .current ⟨i.key, 1, b⟩]
  let base : Ledger3 := { l with clauses := l.clauses ++ [clause], events := l.events ++ declare }
  match i.support with
  | .none => base
  | .receipt cert boundTo =>
    let rb := match boundTo, i.receiptExtra with
      | none, none => b
      | s, e => binding3Of (s.getD i.stmt) i.scope (e.getD i.extra)
    let name := s!"receipt-{i.key}"
    let w : Warrant := ⟨i.key, i.key, 1, b, .receipt name⟩
    { base with receipts := l.receipts ++ [⟨name, i.key, 1, rb, cert⟩], events := base.events ++ [.warrant w] }
  | .rule data premises =>
    let name := s!"rule-{i.key}"
    let w : Warrant := ⟨i.key, i.key, 1, b, .derived premises name⟩
    { base with rules := l.rules ++ [⟨name, i.key, premises, data⟩], events := base.events ++ [.warrant w] }
  | .narrow premise =>
    { base with events := base.events ++ [.warrant ⟨i.key, i.key, 1, b, .narrow premise⟩] }
  | .route steps =>
    { base with events := base.events ++ [.warrant ⟨i.key, i.key, 1, b, .derived steps s!"route-{i.key}"⟩] }

/-- File one item. The commit guard (3a's `guard`: the log still folds) lands the append only if
the log still resolves. -/
def Ledger3.file (l : Ledger3) (i : Item3) : Except String Ledger3 :=
  match guard (l.fileRaw i).events with
  | .ok _ => pure (l.fileRaw i)
  | .error e => throw s!"commit guard refused append: {e}"

def fileAll3 (items : List Item3) (l : Ledger3) : Except String Ledger3 :=
  items.foldlM (fun l i => l.file i) l

structure Outcome3 where
  accepted : Bool
  state : RuntimeState
  ledger : Ledger3
  earned : List Nat

/-- Run a plan: file every item through the commit guard, fold with `admission3`, report. -/
def Plan3.run (p : Plan3) : Except String Outcome3 := do
  let ledger ← fileAll3 p.items {}
  let state ← fold ledger.admission ledger.events
  let accepted := p.elaboration.isNone && !p.requested.isEmpty && p.requested.all (held state ·)
  pure ⟨accepted, state, ledger, (Queries.earned state (p.items.map (·.key)) [] []).map (·.claim)⟩

end GPProfile.Real
