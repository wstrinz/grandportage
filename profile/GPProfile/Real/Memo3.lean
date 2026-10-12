import GPProfile.Real.Frontend

/-!
3b receipt checks computed once per run (ud22 performance, DECISIONS 2026-10-10; Track K's `CheckMemo`
for 3a). A `gp_ledger3` run checked each receipt in the fold, again for the report's `check` field, and
twice more for its diagnosis (`caseTreeExplain` walks the tree, then replays `caseTreeCheck`). A
`CheckMemo3` holds results that carry their own correctness: an entry is stored with a proof that its
verdict is `certOk3` of its stored inputs, and a lookup reuses it only when the current statement,
scope and certificate equal the stored ones. So `certOk3With` is `certOk3` for every memo
(`certOk3With_eq`), whatever produced it, and the admission and report built on it are the original
ones (`admission3With_eq`, `Plan3.runWith_eq`, `explain3With_eq`).

The memo lives for one run only: nothing is stored across runs, and every run replays every receipt.

Entries are computed in parallel, one claim per task (`parEach_eq`, in `plan3Memo`); `certOk3` itself
runs its `@[csimp]` twins (`caseTreeCheckPar`, `orderedCheckFast`).
-/

namespace GPProfile.Real
open GP50 GPProfile

deriving instance DecidableEq for CaseTree
deriving instance DecidableEq for CaseTreeCert
deriving instance DecidableEq for RealWitness
deriving instance DecidableEq for AlgPointCert
deriving instance DecidableEq for NFCert
deriving instance DecidableEq for RootCoverCert
deriving instance DecidableEq for Cert3

/-! ## The memo -/

/-- A stored check: statement, scope, certificate and verdict. -/
abbrev CheckEntry3 := Stmt3 × Scope3 × Cert3 × Bool

def CheckEntry3.Sound (e : CheckEntry3) : Prop := e.2.2.2 = certOk3 e.1 e.2.1 e.2.2.1

structure CheckMemo3 where
  map : Std.HashMap Nat CheckEntry3
  sound : ∀ (k : Nat) (e : CheckEntry3), map[k]? = some e → CheckEntry3.Sound e

def CheckMemo3.empty : CheckMemo3 := ⟨{}, by intro k e h; simp at h⟩

/-- Store an entry under a claim key (a later entry for the same key replaces an earlier one). -/
def CheckMemo3.insert (m : CheckMemo3) (k : Nat) (e : {e : CheckEntry3 // CheckEntry3.Sound e}) : CheckMemo3 :=
  ⟨m.map.insert k e.1, by
    intro k' x h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · cases h; exact e.2
    · exact m.sound k' x h⟩

/-- One receipt's entry, its verdict computed here. -/
def checkEntry3 (stmt : Stmt3) (scope : Scope3) (cert : Cert3) : {e : CheckEntry3 // CheckEntry3.Sound e} :=
  ⟨(stmt, scope, cert, certOk3 stmt scope cert), rfl⟩

/-- An elaborated item's memo entry: its receipt's verdict, computed here. -/
def itemEntry (r : Except String Item3) : Option (Nat × {e : CheckEntry3 // CheckEntry3.Sound e}) :=
  match r with
  | .ok i => match i.support with
    | .receipt c _ => some (i.key, checkEntry3 i.stmt i.scope c)
    | _ => none
  | .error _ => none

def CheckMemo3.ofEntries (es : List (Option (Nat × {e : CheckEntry3 // CheckEntry3.Sound e}))) : CheckMemo3 :=
  es.foldl (fun m e => match e with | some (k, x) => m.insert k x | none => m) CheckMemo3.empty

/-- Decidable equality that first compares addresses (core's `withPtrEqDecEq`, logically the
derived `DecidableEq`): the fold looks a receipt up with the very objects the memo stored. -/
@[inline] def ptrDecEq {α : Type} [DecidableEq α] (a b : α) : Decidable (a = b) :=
  withPtrEqDecEq a b fun _ => inferInstance

/-- `certOk3`, reusing a stored verdict when its inputs are exactly these (`certOk3With_eq`). -/
def certOk3With (m : CheckMemo3) (k : Nat) (stmt : Stmt3) (scope : Scope3) (cert : Cert3) : Bool :=
  match m.map[k]? with
  | some e =>
    match ptrDecEq e.1 stmt, ptrDecEq e.2.1 scope, ptrDecEq e.2.2.1 cert with
    | isTrue _, isTrue _, isTrue _ => e.2.2.2
    | _, _, _ => certOk3 stmt scope cert
  | none => certOk3 stmt scope cert

theorem certOk3With_eq (m : CheckMemo3) (k : Nat) (stmt : Stmt3) (scope : Scope3) (cert : Cert3) :
    certOk3With m k stmt scope cert = certOk3 stmt scope cert := by
  unfold certOk3With
  cases h : m.map[k]? with
  | none => rfl
  | some e =>
    simp only
    split
    · rename_i h1 h2 h3 _ _ _
      have hs := m.sound k e h
      unfold CheckEntry3.Sound at hs
      rw [hs, h1, h2, h3]
    · rfl

/-! ## The admission and the run, read through the memo -/

/-- `accepts3With`, each receipt's verdict read through the memo. -/
def accepts3Memo (m : CheckMemo3) (wf : Bool) (clauses : List Clause3) (receipts : List Receipt3)
    (w : Warrant) (name : String) : Bool :=
  wf &&
    clauses.any fun c => c.key == w.claim && c.version == w.version && decide (c.binding = w.binding) &&
      receipts.any fun r => r.name == name && r.claim == c.key && r.version == c.version &&
        decide (r.binding = c.binding) && certOk3With m c.key c.stmt c.scope r.cert

theorem accepts3Memo_eq (m : CheckMemo3) (wf : Bool) (clauses : List Clause3) (receipts : List Receipt3) :
    accepts3Memo m wf clauses receipts = accepts3With wf clauses receipts := by
  have h : certOk3With m = fun _ => certOk3 := by
    funext k st sc c
    exact certOk3With_eq m k st sc c
  funext w name
  simp only [accepts3Memo, accepts3With, h]

/-- `admission3`, its receipt verdicts read through the memo (`admission3With_eq`). -/
def admission3With (m : CheckMemo3) (clauses : List Clause3) (receipts : List Receipt3)
    (rules : List RuleInst3) : Admission :=
  Semantic.withNarrowing ops3 clauses
    { base3 clauses receipts rules with receipt := accepts3Memo m (wellFormed3 clauses receipts) clauses receipts }

theorem admission3With_eq (m : CheckMemo3) (clauses : List Clause3) (receipts : List Receipt3)
    (rules : List RuleInst3) : admission3With m clauses receipts rules = admission3 clauses receipts rules := by
  simp only [admission3With, admission3, accepts3Memo_eq]
  rfl

/-- `Plan3.run`, folding with `admission3With` (`Plan3.runWith_eq`). -/
def Plan3.runWith (m : CheckMemo3) (p : Plan3) : Except String Outcome3 := do
  let ledger ← fileAll3 p.items {}
  let state ← fold (admission3With m ledger.clauses ledger.receipts ledger.rules) ledger.events
  let accepted := p.elaboration.isNone && !p.requested.isEmpty && p.requested.all (held state ·)
  pure ⟨accepted, state, ledger, (Queries.earned state (p.items.map (·.key)) [] []).map (·.claim)⟩

theorem Plan3.runWith_eq (m : CheckMemo3) (p : Plan3) : p.runWith m = p.run := by
  simp only [Plan3.runWith, Plan3.run, Ledger3.admission, admission3With_eq]

/-! ## Diagnostics of an accepted receipt -/

theorem rhombusExplain_none {n : Nat} {pts : List (Nat × Nat)} {r : RealSys} {h : Rhombus}
    (ok : rhombusOk n pts r h = true) : rhombusExplain n pts r h = none := by
  simp only [rhombusOk, Bool.and_eq_true] at ok
  simp [rhombusExplain, ok]

theorem sosExplain_ok {s : Stmt} {c : PCert} (h : sosCheck s c = true) : sosExplain s c = .ok () := by
  unfold sosCheck at h
  unfold sosExplain
  split at h <;> simp_all

theorem caseTreeExplainGo_ok (pts : List (Nat × Nat)) (r : RealSys) (t : CaseTree)
    (h : caseTreeGo pts r t = true) : caseTreeExplainGo pts r t = .ok () := by
  induction t generalizing r with
  | collision c =>
    simp only [caseTreeGo, collisionOk, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hr, hx⟩, hy⟩, hg⟩ := h
    simp only [caseTreeExplainGo]
    simp only [hx, hy, hg, Bool.and_self]
    generalize c.rhombi = l at hr ⊢
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hr
      simpa [List.forIn_cons, rhombusExplain_none hr.1] using ih hr.2
  | unit d t ih =>
    simp only [caseTreeGo, unitOk, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hr, hs⟩, hx⟩, hy⟩, he⟩, hb⟩, ht⟩ := h
    simp only [caseTreeExplainGo]
    simp only [hs, hx, hy, he, hb, ih _ ht, Bool.and_self]
    generalize d.rhombi = l at hr ⊢
    induction l with
    | nil => rfl
    | cons a l ih' =>
      simp only [List.all_cons, Bool.and_eq_true] at hr
      simpa [List.forIn_cons, rhombusExplain_none hr.1] using ih' hr.2
  | ordered c =>
    simp only [caseTreeGo] at h
    simp [caseTreeExplainGo, orderedExplain_ok h]
    rfl
  | zero p t f iht ihf =>
    simp only [caseTreeGo, Bool.and_eq_true] at h
    simp [caseTreeExplainGo, iht _ h.1, ihf _ h.2]
  | sign p n z q ihn ihz ihq =>
    simp only [caseTreeGo, Bool.and_eq_true] at h
    simp [caseTreeExplainGo, ihn _ h.1.1, ihz _ h.1.2, ihq _ h.2]

theorem pointExplain_ok {r : RealSys} {w : RealWitness} (h : pointCheck r w = true) : pointExplain r w = .ok () := by
  unfold pointCheck at h
  unfold pointExplain
  split at h
  · rename_i s a ws hc
    simp [hc, h, bind, Except.bind, pure, Except.pure]
  · cases h

theorem caseTreeExplain_ok {r : RealSys} {c : CaseTreeCert} (h : caseTreeCheck r c = true) :
    caseTreeExplain r c = .ok () := by
  have h' := h
  simp only [caseTreeCheck, Bool.and_eq_true] at h'
  simp [caseTreeExplain, h'.1, caseTreeExplainGo_ok _ _ _ h'.2, h]

/-- The diagnosis `explain3` gives an accepted receipt of the replay-heavy kinds, known without
replaying it (`accepted_explain3`); `none` for every other kind. -/
def acceptedText : Stmt3 → Scope3 → Cert3 → Option String
  | .real _ .empty, .real, .caseTree _ => some "case tree replay accepted"
  | .orderFree _, .real, .caseTree _ => some "case tree replay accepted"
  | .real _ .empty, .real, .ordered _ => some "ordered Positivstellensatz replay accepted"
  | .orderFree _, .semireal, .sos _ => some "SOS replay accepted"
  | .orderFree _, .real, .sos _ => some "SOS replay accepted"
  | .real _ .nonempty, .real, .point _ => some "point replay accepted"
  | .orderFree _, .real, .point _ => some "point replay accepted (a point over ℝ)"
  | _, _, _ => none

theorem accepted_explain3 (st : Stmt3) (sc : Scope3) (c : Cert3) (t : String) (v : certOk3 st sc c = true)
    (h : acceptedText st sc c = some t) : explain3 st sc c = t := by
  unfold acceptedText at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp_all [certOk3, explain3, caseTreeExplain_ok, orderedExplain_ok, sosExplain_ok, pointExplain_ok]

/-- `explain3` given the receipt's verdict `v` (`explain3With_eq`: with the true verdict, it is `explain3`). -/
def explain3With (v : Bool) (st : Stmt3) (sc : Scope3) (c : Cert3) : String :=
  if v then (acceptedText st sc c).getD (explain3 st sc c) else explain3 st sc c

theorem explain3With_eq (st : Stmt3) (sc : Scope3) (c : Cert3) :
    explain3With (certOk3 st sc c) st sc c = explain3 st sc c := by
  unfold explain3With
  split
  · rename_i v
    cases h : acceptedText st sc c with
    | none => rfl
    | some t => simp [accepted_explain3 st sc c t v h]
  · rfl

end GPProfile.Real
