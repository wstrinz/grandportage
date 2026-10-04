import GP50.Queries
import GPProfile.Rules
import GPProfile.Canonical

/-!
Case plans (post-G2 §1.8–1.9). A family adapter turns a case into profile inputs only:
statements, scopes, certificate and rule data. The untrusted proposer files each item through
the commit guard; the Kernel fold decides; the case is ACCEPT only when every requested claim
is held. Authority never comes from the plan itself.
-/

namespace GPProfile
open Lean GP50

/-- How an item is offered support. A receipt may be bound to a different (original)
statement and binding inputs: that is how custody of a receipt under a proposed change is
expressed, and the Kernel's exact binding check decides it. -/
inductive Support where
  | none
  | receipt (cert : Cert) (boundTo : Option (Stmt × List String) := none)
  | rule (data : RuleData) (premises : List Nat)
  /-- A recorded bounded search (G3a review §7, the TIMEOUT-as-non-evidence lineage): kept for
  provenance, with no admission path. -/
  | searched (bound : Nat)
  deriving Repr

structure Item where
  key : Nat
  stmt : Stmt
  scope : Scope
  /-- Binding inputs beyond the statement, e.g. a chart or a source citation. -/
  extra : List String := []
  support : Support
  deriving Repr

structure Plan where
  items : List Item
  requested : List Nat
  /-- Refusals decided while elaborating the case (signature, malformed maps). -/
  elaboration : Option String := none
  deriving Repr

def bindingOf (stmt : Stmt) (scope : Scope) (extra : List String) : Binding :=
  { statementHash := stmtCanon stmt, scopeHash := scopeCanon scope, modelHash := "gp-profile-3a/v1"
    inputHashes := extra, authority := "3a-corpus", authorityVersion := 1, kernelVersion := 1 }

structure Ledger where
  clauses : List Clause := []
  receipts : List Receipt := []
  rules : List RuleInst := []
  records : List BinderRecord := []
  events : List Event := []

def Ledger.admission (l : Ledger) : Admission := admissionWithRules l.clauses l.receipts l.rules l.records

/-- A4: mint a theorem warrant for a claim when the binder bound a theorem for exactly its
statement and scope. The warrant is filed next to the receipt, through the commit guard. -/
def Ledger.mintTheorem (l : Ledger) (i : Item) : Except String (Ledger × Option String) := do
  let b := bindingOf i.stmt i.scope i.extra
  match l.records.find? fun r => r.statementHash == b.statementHash && r.scopeHash == b.scopeHash with
  | none => pure (l, none)
  | some r =>
    let w : Warrant := ⟨1000 + i.key, i.key, 1, b, .theoremWarrant r.declaration⟩
    let next := { l with events := l.events ++ [.warrant w] }
    match fold next.admission next.events with
    | .ok _ => pure (next, some r.declaration)
    | .error e => throw s!"commit guard refused theorem warrant: {e}"

/-- File one item. The commit guard lands the append only if the log still folds. -/
def Ledger.file (l : Ledger) (i : Item) : Except String Ledger := do
  let b := bindingOf i.stmt i.scope i.extra
  let clause : Clause := ⟨i.key, 1, b, i.stmt, i.scope⟩
  let declare := [Event.declareClaim i.key, .current ⟨i.key, 1, b⟩]
  let base : Ledger := { l with clauses := l.clauses ++ [clause], events := l.events ++ declare }
  let next : Ledger := match i.support with
    | .none | .searched _ => base
    | .receipt cert boundTo =>
      let rb := match boundTo with
        | some (s, m) => bindingOf s i.scope m
        | none => b
      let name := s!"receipt-{i.key}"
      let w : Warrant := ⟨i.key, i.key, 1, b, .receipt name⟩
      { base with receipts := l.receipts ++ [⟨name, i.key, 1, rb, cert⟩], events := base.events ++ [.warrant w] }
    | .rule data premises =>
      let name := s!"rule-{i.key}"
      let w : Warrant := ⟨i.key, i.key, 1, b, .derived premises name⟩
      { base with rules := l.rules ++ [⟨name, i.key, premises, data⟩], events := base.events ++ [.warrant w] }
  match fold next.admission next.events with
  | .ok _ => pure next
  | .error e => throw s!"commit guard refused append: {e}"

/-- The widest strictly wider reach among re-replays of a held receipt's certificate. -/
def widenCert (stmt : Stmt) (scope : Scope) (cert : Cert) : Option (Scope × Cert) :=
  let withField : Cert → Field → Cert
    | .ideal _ qs m k, f => .ideal f qs m k
    | .point _ vs, f => .point f vs
    | .proper _ a b, f => .proper f a b
    | c, _ => c
  let candidates := [cert, withField cert .rat].eraseDups.filterMap fun c => (reach stmt c).map (·, c)
  let wider := candidates.filter fun (r, _) => scope.le r && !r.le scope
  (wider.find? fun (r, _) => wider.all fun (r', _) => r'.le r).orElse fun _ => wider.head?

structure Outcome where
  accepted : Bool
  state : RuntimeState
  widened : List (Nat × Scope)
  earned : List Nat
  theorems : List (Nat × String) := []

/-- Run a plan: file every item, fold, then file the proposer's widenings and report. -/
def Plan.run (p : Plan) (records : List BinderRecord := []) : Except String Outcome := do
  let ledger ← p.items.foldlM (fun l i => l.file i) ({ records } : Ledger)
  -- A4: theorem warrants next to receipts wherever the binder bound one.
  let (ledger, theorems) ← p.items.foldlM (fun (acc : Ledger × List (Nat × String)) i => do
      match i.support with
      | .receipt _ none =>
        let (l, d) ← acc.1.mintTheorem i
        pure (l, acc.2 ++ (d.map (i.key, ·)).toList)
      | _ => pure acc) (ledger, [])
  let state ← fold ledger.admission ledger.events
  let accepted := p.elaboration.isNone && !p.requested.isEmpty && p.requested.all (held state)
  let base := (p.items.map (·.key)).foldl max 0 + 1
  let (ledger, widened, _) ← p.items.foldlM (fun (acc : Ledger × List (Nat × Scope) × Nat) i => do
      let (l, ws, next) := acc
      match i.support with
      | .receipt cert none =>
        if !held state i.key then pure acc else
        match widenCert i.stmt i.scope cert with
        | some (r, c) =>
          let item : Item := { key := next, stmt := i.stmt, scope := r, extra := i.extra, support := .receipt c }
          pure (← l.file item, ws ++ [(i.key, r)], next + 1)
        | none => pure acc
      | _ => pure acc) (ledger, [], base)
  -- A4 at the computed reach: theorem warrants for the widened claims.
  let widenedItems := (widened.zip (List.range widened.length)).filterMap fun ((k, r), j) =>
    (p.items.find? (·.key == k)).map fun i => ({ i with key := base + j, scope := r } : Item)
  let (ledger, theorems) ← widenedItems.foldlM (fun (acc : Ledger × List (Nat × String)) i => do
      let (l, d) ← acc.1.mintTheorem i
      pure (l, acc.2 ++ (d.map (i.key, ·)).toList)) (ledger, theorems)
  let final ← fold ledger.admission ledger.events
  pure ⟨accepted, final, widened, (Queries.earned final (p.items.map (·.key)) [] []).map (·.claim), theorems⟩

end GPProfile
