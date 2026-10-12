import Std.Data.HashSet
import GP50.Queries
import GPProfile.Rules
import GPProfile.Memo
import GPProfile.Canonical
import GPProfile.Guard

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

/-- Whether a log folds never depends on the admission: `fold` fails only in `resolve`. So the
commit guard decides with `Admission.refuseAll` and replays no certificate (3P F2: replaying every
receipt on every append made filing quadratic). -/
theorem fold_ok_admission (a b : Admission) (events : List Event) :
    (fold a events).isOk = (fold b events).isOk := by
  simp only [fold]
  cases resolve events <;> rfl

theorem fold_ok_resolve (a : Admission) (events : List Event) :
    (fold a events).isOk = (resolve events).isOk := by
  simp only [fold]
  cases resolve events <;> rfl

/-- The commit guard: the log still folds, which is exactly that it resolves (`fold_ok_resolve`), with
the same error. Resolving alone skips the closure (3P F2). -/
def guard (events : List Event) : Except String Unit :=
  match resolve events with
  | .ok _ => .ok ()
  | .error e => .error e

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

/-- Theorem warrants take ids in their own range, `theoremWarrantBase + key`. Claim keys, and the
receipt and rule warrants filed under them, stay below 2^53 (counter keys, and the content-derived
keys in [2^32, 2^32 + 2^52)), so a theorem warrant's id never meets another claim's warrant id. -/
def theoremWarrantBase : Nat := 2 ^ 60

def theoremWarrantId (key : Nat) : Nat := theoremWarrantBase + key

/-- A4: mint a theorem warrant for a claim when the binder bound a theorem for exactly its
statement and scope. The warrant is filed next to the receipt, through the commit guard. -/
def Ledger.mintTheorem (l : Ledger) (i : Item) : Except String (Ledger × Option String) := do
  let b := bindingOf i.stmt i.scope i.extra
  match l.records.find? fun r => r.statementHash == b.statementHash && r.scopeHash == b.scopeHash with
  | none => pure (l, none)
  | some r =>
    let w : Warrant := ⟨theoremWarrantId i.key, i.key, 1, b, .theoremWarrant r.declaration⟩
    let next := { l with events := l.events ++ [.warrant w] }
    match guard next.events with
    | .ok _ => pure (next, some r.declaration)
    | .error e => throw s!"commit guard refused theorem warrant: {e}"

/-- One item's clause, receipt or rule, and events, appended without the guard. -/
def Ledger.fileRaw (l : Ledger) (i : Item) : Ledger :=
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
  next

/-- File one item. The commit guard lands the append only if the log still folds. -/
def Ledger.file (l : Ledger) (i : Item) : Except String Ledger :=
  match guard (l.fileRaw i).events with
  | .ok _ => pure (l.fileRaw i)
  | .error e => throw s!"commit guard refused append: {e}"

/-- File items in order, each through the commit guard. -/
def fileAll (items : List Item) (l : Ledger) : Except String Ledger := items.foldlM (fun l i => l.file i) l

/-- Append a ledger's clauses, receipts, rules and events to `l`'s (records stay `l`'s). -/
def Ledger.add (l d : Ledger) : Ledger :=
  { l with clauses := l.clauses ++ d.clauses, receipts := l.receipts ++ d.receipts,
           rules := l.rules ++ d.rules, events := l.events ++ d.events }

/-- `fileRaw` appends what it appends to the empty ledger. -/
theorem fileRaw_add (l : Ledger) (i : Item) : l.fileRaw i = l.add (({} : Ledger).fileRaw i) := by
  unfold Ledger.fileRaw Ledger.add
  cases i.support <;> simp [List.append_assoc]

/-- The unguarded filing of `items` with each list appended once, so linear rather than quadratic in
the log length (`fileRawAll_eq`). -/
def fileRawAll (items : List Item) (l : Ledger) : Ledger :=
  let ds := items.map fun i => ({} : Ledger).fileRaw i
  l.add { clauses := ds.flatMap (·.clauses), receipts := ds.flatMap (·.receipts),
          rules := ds.flatMap (·.rules), events := ds.flatMap (·.events) }

theorem fileRawAll_eq : ∀ (items : List Item) (l : Ledger),
    fileRawAll items l = items.foldl (fun l i => l.fileRaw i) l
  | [], l => by simp [fileRawAll, Ledger.add]
  | i :: is, l => by
    rw [List.foldl_cons, ← fileRawAll_eq is, fileRaw_add]
    simp [fileRawAll, Ledger.add, List.append_assoc]

/-- The same filing with one `resolve` at the end (`fileAllFast_eq`). Profile logs only accumulate
conflicts (`Guard.resolve_prefix`), so when the final log resolves, every guard along the way passed.
When it does not, the guarded loop runs, so the refusal and its message are unchanged. -/
def fileAllFast (items : List Item) (l : Ledger) : Except String Ledger :=
  let raw := fileRawAll items l
  match guard raw.events with
  | .ok _ => .ok raw
  | .error _ => fileAll items l

theorem fileRaw_events (l : Ledger) (i : Item) :
    ∃ t, (l.fileRaw i).events = l.events ++ t ∧ Guard.Simple t := by
  unfold Ledger.fileRaw
  cases i.support with
  | none => exact ⟨_, rfl, by intro e he; simp at he; rcases he with rfl | rfl <;> rfl⟩
  | searched _ => exact ⟨_, rfl, by intro e he; simp at he; rcases he with rfl | rfl <;> rfl⟩
  | receipt cert boundTo =>
    refine ⟨_, by simp only [List.append_assoc]; rfl, ?_⟩
    intro e he; simp at he; rcases he with rfl | rfl | rfl <;> rfl
  | rule data premises =>
    refine ⟨_, by simp only [List.append_assoc]; rfl, ?_⟩
    intro e he; simp at he; rcases he with rfl | rfl | rfl <;> rfl

theorem foldl_fileRaw_events : ∀ (items : List Item) (l : Ledger),
    ∃ t, (items.foldl (fun l i => l.fileRaw i) l).events = l.events ++ t ∧ Guard.Simple t
  | [], l => ⟨[], by simp, by intro e he; simp at he⟩
  | i :: is, l => by
    obtain ⟨t₁, h₁, s₁⟩ := fileRaw_events l i
    obtain ⟨t₂, h₂, s₂⟩ := foldl_fileRaw_events is (l.fileRaw i)
    refine ⟨t₁ ++ t₂, by simp only [List.foldl_cons, h₂, h₁, List.append_assoc], ?_⟩
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact s₁ e he
    · exact s₂ e he

theorem guard_ok_iff (events : List Event) : (∃ u, guard events = .ok u) ↔ ∃ s, resolve events = .ok s := by
  unfold guard
  cases resolve events <;> simp

theorem fileAll_of_resolves : ∀ (items : List Item) (l : Ledger), Guard.Simple l.events →
    (∃ s, resolve (items.foldl (fun l i => l.fileRaw i) l).events = .ok s) →
    fileAll items l = .ok (items.foldl (fun l i => l.fileRaw i) l)
  | [], l, _, _ => rfl
  | i :: is, l, hs, hres => by
    obtain ⟨t₁, h₁, s₁⟩ := fileRaw_events l i
    obtain ⟨t₂, h₂, s₂⟩ := foldl_fileRaw_events is (l.fileRaw i)
    have hsi : Guard.Simple (l.fileRaw i).events := by
      rw [h₁]; intro e he
      rcases List.mem_append.mp he with he | he
      · exact hs e he
      · exact s₁ e he
    have hall : Guard.Simple ((l.fileRaw i).events ++ t₂) := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hsi e he
      · exact s₂ e he
    simp only [List.foldl_cons] at hres
    rw [h₂] at hres
    obtain ⟨u, hu⟩ := (guard_ok_iff _).mpr (Guard.resolve_prefix hall hres)
    have hfile : l.file i = .ok (l.fileRaw i) := by
      unfold Ledger.file
      rw [hu]; rfl
    have ih := fileAll_of_resolves is (l.fileRaw i) hsi (by rw [h₂]; exact hres)
    simp only [fileAll, List.foldlM_cons, hfile] at ih ⊢
    exact ih

/-- Fast filing equals guarded filing on any log the profile starts (`Simple` events). -/
theorem fileAllFast_eq (items : List Item) (l : Ledger) (hs : Guard.Simple l.events) :
    fileAllFast items l = fileAll items l := by
  unfold fileAllFast
  dsimp only
  rw [fileRawAll_eq]
  cases hg : guard (items.foldl (fun l i => l.fileRaw i) l).events with
  | error e => rfl
  | ok u =>
    exact (fileAll_of_resolves items l hs ((guard_ok_iff _).mp ⟨u, hg⟩)).symm

/-- The widest strictly wider reach among re-replays of a held receipt's certificate. -/
def widenCert (stmt : Stmt) (scope : Scope) (cert : Cert) : Option (Scope × Cert) :=
  let withField : Cert → Field → Cert
    | .ideal _ qs m k, f => .ideal f qs m k
    | .point _ vs, f => .point f vs
    | .proper _ a b, f => .proper f a b
    | .idealSel mask _ qs m k, f => .idealSel mask f qs m k
    | .properCoeff _ mono, f => .properCoeff f mono
    | c, _ => c
  let candidates := [cert, withField cert .rat].eraseDups.filterMap fun c => (reach stmt c).map (·, c)
  let wider := candidates.filter fun (r, _) => scope.le r && !r.le scope
  (wider.find? fun (r, _) => wider.all fun (r', _) => r'.le r).orElse fun _ => wider.head?

/-- A held receipt's widening, when its certificate replays at a strictly wider reach. -/
def widenOf (state : RuntimeState) (i : Item) : Option (Item × Scope × Cert) :=
  match i.support with
  | .receipt cert none =>
    if !held state i.key then none else (widenCert i.stmt i.scope cert).map fun (r, c) => (i, r, c)
  | _ => none

/-- `widenOf` with membership in a set of held claims (`widenOfWith_ofList`). -/
def widenOfWith (heldKeys : Std.HashSet Nat) (i : Item) : Option (Item × Scope × Cert) :=
  match i.support with
  | .receipt cert none =>
    if !heldKeys.contains i.key then none else (widenCert i.stmt i.scope cert).map fun (r, c) => (i, r, c)
  | _ => none

theorem widenOfWith_ofList (state : RuntimeState) :
    widenOfWith (Std.HashSet.ofList state.claims) = widenOf state := by
  funext i
  unfold widenOfWith widenOf held
  rw [Std.HashSet.contains_ofList]

/-- `xs.filterMap f`, with `f` computed in parallel (`parFilterMap_eq`). -/
def parFilterMap {α β : Type} (f : α → Option β) (xs : List α) : List β := (parMap f xs).filterMap id

theorem parFilterMap_eq {α β : Type} (f : α → Option β) (xs : List α) : parFilterMap f xs = xs.filterMap f := by
  simp [parFilterMap, parMap_eq, List.filterMap_map]

/-- The widened claims as items keyed `next`, `next + 1`, ... in plan order. -/
def widenItems : Nat → List (Item × Scope × Cert) → List Item
  | _, [] => []
  | next, (i, r, c) :: rest =>
    { key := next, stmt := i.stmt, scope := r, extra := i.extra, support := .receipt c } :: widenItems (next + 1) rest

/-- One step of the guarded per-claim widening loop `Plan.run` ran before `widenLoop_eq`. -/
def widenStep (state : RuntimeState) (acc : Ledger × List (Nat × Scope) × Nat) (i : Item) :
    Except String (Ledger × List (Nat × Scope) × Nat) := do
  let (l, ws, next) := acc
  match i.support with
  | .receipt cert none =>
    if !held state i.key then pure acc else
    match widenCert i.stmt i.scope cert with
    | some (r, c) =>
      let item : Item := { key := next, stmt := i.stmt, scope := r, extra := i.extra, support := .receipt c }
      pure (← l.file item, ws ++ [(i.key, r)], next + 1)
    | none => pure acc
  | _ => pure acc

/-- The loop is `fileAll` of the widened items, with the widened list and next key it accumulates. -/
theorem widenLoop_eq (state : RuntimeState) : ∀ (items : List Item) (l : Ledger) (ws : List (Nat × Scope))
    (next : Nat), items.foldlM (widenStep state) (l, ws, next) =
      (fileAll (widenItems next (items.filterMap (widenOf state))) l).map fun l' =>
        (l', ws ++ (items.filterMap (widenOf state)).map (fun (i, r, _) => (i.key, r)),
          next + (items.filterMap (widenOf state)).length)
  | [], l, ws, next => by simp [widenItems, fileAll, Except.map, pure, Except.pure]
  | i :: is, l, ws, next => by
    simp only [List.foldlM_cons, List.filterMap_cons]
    cases hs : i.support with
    | receipt cert boundTo =>
      cases boundTo with
      | some b =>
        rw [show widenStep state (l, ws, next) i = pure (l, ws, next) by simp [widenStep, hs],
          show widenOf state i = none by simp [widenOf, hs]]
        exact widenLoop_eq state is l ws next
      | none =>
        by_cases hh : held state i.key
        · cases hw : widenCert i.stmt i.scope cert with
          | none =>
            rw [show widenStep state (l, ws, next) i = pure (l, ws, next) by simp [widenStep, hs, hh, hw],
              show widenOf state i = none by simp [widenOf, hs, hh, hw]]
            exact widenLoop_eq state is l ws next
          | some rc =>
            obtain ⟨r, c⟩ := rc
            have h₁ : widenStep state (l, ws, next) i =
                (fun a => (a, ws ++ [(i.key, r)], next + 1)) <$>
                  l.file { key := next, stmt := i.stmt, scope := r, extra := i.extra, support := .receipt c } := by
              simp [widenStep, hs, hh, hw]
            have h₂ : widenOf state i = some (i, r, c) := by simp [widenOf, hs, hh, hw]
            rw [h₁, h₂]
            simp only [widenItems, fileAll, List.foldlM_cons]
            cases hf : l.file { key := next, stmt := i.stmt, scope := r, extra := i.extra, support := .receipt c } with
            | error e => rfl
            | ok l₁ =>
              have ih := widenLoop_eq state is l₁ (ws ++ [(i.key, r)]) (next + 1)
              simp only [fileAll] at ih
              simp only [Functor.map, Except.map, bind, Except.bind] at ih ⊢
              rw [ih]
              simp [List.append_assoc, Nat.add_assoc, Nat.add_comm 1]
        · rw [show widenStep state (l, ws, next) i = pure (l, ws, next) by simp [widenStep, hs, hh],
            show widenOf state i = none by simp [widenOf, hs, hh]]
          exact widenLoop_eq state is l ws next
    | none =>
      rw [show widenStep state (l, ws, next) i = pure (l, ws, next) by simp [widenStep, hs],
        show widenOf state i = none by simp [widenOf, hs]]
      exact widenLoop_eq state is l ws next
    | searched _ =>
      rw [show widenStep state (l, ws, next) i = pure (l, ws, next) by simp [widenStep, hs],
        show widenOf state i = none by simp [widenOf, hs]]
      exact widenLoop_eq state is l ws next
    | rule _ _ =>
      rw [show widenStep state (l, ws, next) i = pure (l, ws, next) by simp [widenStep, hs],
        show widenOf state i = none by simp [widenOf, hs]]
      exact widenLoop_eq state is l ws next

structure Outcome where
  accepted : Bool
  state : RuntimeState
  widened : List (Nat × Scope)
  earned : List Nat
  theorems : List (Nat × String) := []

/-- `Ledger.admission` with its receipt checks read through a memo (`admissionMemo_eq`). -/
def Ledger.admissionMemo (l : Ledger) (m : CheckMemo) : Admission :=
  admissionWithRulesMemo m l.clauses l.receipts l.rules l.records

theorem Ledger.admissionMemo_eq (l : Ledger) (m : CheckMemo) : l.admissionMemo m = l.admission :=
  admissionWithRulesMemo_eq m l.clauses l.receipts l.rules l.records

/-- Every receipt item's check, computed once per run (P1); the folds and the report reuse them. -/
def Plan.checkMemo (p : Plan) : CheckMemo :=
  CheckMemo.ofList (p.items.filterMap fun i => match i.support with
    | .receipt cert _ => some (i.key, i.stmt, i.scope, cert)
    | _ => none)

/-- Run a plan: file every item, fold, then file the proposer's widenings and report. Both folds read
receipt checks through `m`, which changes no verdict (`Ledger.admissionMemo_eq`). -/
def Plan.runWith (p : Plan) (m : CheckMemo) (records : List BinderRecord := []) : Except String Outcome := do
  -- One `resolve` for the whole filing (`fileAllFast_eq`: the same result as guarding each append).
  let ledger ← fileAllFast p.items ({ records } : Ledger)
  -- A4: theorem warrants next to receipts wherever the binder bound one.
  let (ledger, theorems) ← p.items.foldlM (fun (acc : Ledger × List (Nat × String)) i => do
      match i.support with
      | .receipt _ none =>
        let (l, d) ← acc.1.mintTheorem i
        pure (l, acc.2 ++ (d.map (i.key, ·)).toList)
      | _ => pure acc) (ledger, [])
  let state ← fold (ledger.admissionMemo m) ledger.events
  -- `held state` as a set lookup (`Std.HashSet.contains_ofList`), not a scan of the claim list.
  let heldKeys := Std.HashSet.ofList state.claims
  let accepted := p.elaboration.isNone && !p.requested.isEmpty && p.requested.all heldKeys.contains
  let base := (p.items.map (·.key)).foldl max 0 + 1
  -- The widenings, filed with one `resolve` (`widenLoop_eq`, `fileAllFast_eq`: the same result as
  -- guarding each widened claim in turn).
  let ws := parFilterMap (widenOfWith heldKeys) p.items  -- = p.items.filterMap (widenOf state)
  let ledger ← fileAllFast (widenItems base ws) ledger
  let widened := ws.map fun (i, r, _) => (i.key, r)
  -- A4 at the computed reach: theorem warrants for the widened claims.
  let widenedItems := (widened.zip (List.range widened.length)).filterMap fun ((k, r), j) =>
    (p.items.find? (·.key == k)).map fun i => ({ i with key := base + j, scope := r } : Item)
  let (ledger, theorems) ← widenedItems.foldlM (fun (acc : Ledger × List (Nat × String)) i => do
      let (l, d) ← acc.1.mintTheorem i
      pure (l, acc.2 ++ (d.map (i.key, ·)).toList)) (ledger, theorems)
  let final ← fold (ledger.admissionMemo m) ledger.events
  pure ⟨accepted, final, widened, (Queries.earned final (p.items.map (·.key)) [] []).map (·.claim), theorems⟩

/-- `Plan.runWith` with a memo of this plan's checks. -/
def Plan.run (p : Plan) (records : List BinderRecord := []) : Except String Outcome :=
  p.runWith p.checkMemo records

end GPProfile
