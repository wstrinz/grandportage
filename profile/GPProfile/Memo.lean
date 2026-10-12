import GPProfile.Rules
import Std.Data.HashMap

/-!
Certificate checks computed once per run (post-G4 Track K, P1). A run checks each receipt in its
first fold, again in its second fold, and again when it reports the item. `CheckMemo` holds
results that carry their own correctness: an entry is stored with a proof that its result is
`check` of its stored inputs, and a lookup reuses it only when the current inputs equal the
stored ones. So `checkWith` equals `check` for every memo (`checkWith_eq`), whatever produced it.
-/

namespace GPProfile
open GP50

/-- A stored check: claim key, statement, scope, certificate, and its result. -/
abbrev CheckEntry := Nat × Stmt × Scope × Cert × Check

def CheckEntry.Sound (e : CheckEntry) : Prop := e.2.2.2.2 = check e.2.1 e.2.2.1 e.2.2.2.1

structure CheckMemo where
  map : Std.HashMap Nat CheckEntry
  sound : ∀ (k : Nat) (e : CheckEntry), map[k]? = some e → CheckEntry.Sound e

def CheckMemo.empty : CheckMemo := ⟨{}, by intro k e h; simp at h⟩

/-- Store an entry under its claim key (a later entry for the same key replaces an earlier one). -/
def CheckMemo.insert (m : CheckMemo) (e : {e : CheckEntry // CheckEntry.Sound e}) : CheckMemo :=
  ⟨m.map.insert e.1.1 e.1, by
    intro k x h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · cases h; exact e.2
    · exact m.sound k x h⟩

/-- The entry for one receipt item, its check computed here. -/
def checkEntry (k : Nat) (stmt : Stmt) (scope : Scope) (cert : Cert) : {e : CheckEntry // CheckEntry.Sound e} :=
  ⟨(k, stmt, scope, cert, check stmt scope cert), rfl⟩

/-- A memo of every listed check, computed in parallel. -/
def CheckMemo.ofList (xs : List (Nat × Stmt × Scope × Cert)) : CheckMemo :=
  (parMap (fun x => checkEntry x.1 x.2.1 x.2.2.1 x.2.2.2) xs).foldl CheckMemo.insert CheckMemo.empty

/-- `check`, reusing a stored result when its inputs are exactly these (`checkWith_eq`). -/
def checkWith (m : CheckMemo) (k : Nat) (stmt : Stmt) (scope : Scope) (cert : Cert) : Check :=
  match m.map[k]? with
  | some e => if e.2.1 = stmt ∧ e.2.2.1 = scope ∧ e.2.2.2.1 = cert then e.2.2.2.2 else check stmt scope cert
  | none => check stmt scope cert

theorem checkWith_eq (m : CheckMemo) (k : Nat) (stmt : Stmt) (scope : Scope) (cert : Cert) :
    checkWith m k stmt scope cert = check stmt scope cert := by
  unfold checkWith
  cases h : m.map[k]? with
  | none => rfl
  | some e =>
    simp only
    split
    · rename_i heq
      obtain ⟨h1, h2, h3⟩ := heq
      have hs := m.sound k e h
      unfold CheckEntry.Sound at hs
      rw [hs, h1, h2, h3]
    · rfl

/-- `receiptOkIx` with each check read through the memo (`receiptOkMemo_eq`). -/
def receiptOkMemo (m : CheckMemo) (byKey : Std.HashMap Nat (List Clause)) (r : Receipt) : Bool :=
  match (byKey.getD r.claim []).find? (fun c => c.key == r.claim) with
  | some c => (checkWith m c.key c.stmt c.scope r.cert).ok
  | none => false

theorem receiptOkMemo_eq (m : CheckMemo) (byKey : Std.HashMap Nat (List Clause)) :
    receiptOkMemo m byKey = receiptOkIx byKey := by
  funext r
  unfold receiptOkMemo receiptOkIx
  cases (byKey.getD r.claim []).find? (fun c => c.key == r.claim) with
  | none => rfl
  | some c => exact congrArg Check.ok (checkWith_eq m c.key c.stmt c.scope r.cert)

/-- `admissionWithRules`, its receipt verdicts read through the memo (`admissionWithRulesMemo_eq`). -/
def admissionWithRulesMemo (m : CheckMemo) (clauses : List Clause) (receipts : List Receipt)
    (rules : List RuleInst) (records : List BinderRecord := []) : Admission :=
  let wf := Index.nodupB (clauses.map (·.key)) && Index.nodupB (receipts.map (·.name))
  let distinct := Index.nodupB (rules.map (·.name))
  let unique := Index.nodupB (clauses.map (·.key))
  let byKey := Index.bucket (·.key) clauses
  let receiptVs := parMap (fun r => (r, receiptOkMemo m byKey r)) receipts
  let ruleVs := parMap (fun r => (r, ruleOkIx byKey r)) rules
  let base : Admission :=
    { receipt := acceptsTableIx wf byKey (Index.bucket (·.1.name) receiptVs), proof := acceptsProof clauses records,
      rule := acceptsRuleTableIx distinct unique byKey (Index.bucket (·.1.name) ruleVs),
      narrow := fun _ _ => false }
  Semantic.withNarrowing ops clauses base

theorem admissionWithRulesMemo_eq (m : CheckMemo) (clauses : List Clause) (receipts : List Receipt)
    (rules : List RuleInst) (records : List BinderRecord) :
    admissionWithRulesMemo m clauses receipts rules records = admissionWithRules clauses receipts rules records := by
  unfold admissionWithRulesMemo admissionWithRules
  simp only [receiptOkMemo_eq]

end GPProfile
