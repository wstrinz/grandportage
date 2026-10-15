import GPProfile.Corpus
import GPProfile.Diagnose
import GPProfile.Matroid
import Std.Data.HashSet
import GP50.Decoder

/-!
The campaign ledger runner (post-G3a handoff §4.6). It reads a ledger written in the explicit
statement surface (`claims`, `requested`) on stdin, files it through the commit guard and the Kernel
fold, and prints every claim's status, check and computed reach. The `gp` CLI renders the views;
this executable decides. Nothing here constructs a verdict outside `Plan.run` (here `Plan.runWith`).
`withdrawn` (optional, GP 0.51) lists withdrawn claim keys: both folds retract their warrants
(`GPProfile.Withdraw.runWith_withdrawn`), and their items carry `"withdrawn": true`.
-/

namespace GPProfile.LedgerRun
open Lean GP50 GPProfile

def scopeJson (s : Scope) : Json :=
  Json.mkObj [("char0", toJson s.char0), ("primes", match s.primes with
    | .finite ps => Json.mkObj [("finite", toJson ps)]
    | .cofinite e => Json.mkObj [("cofinite", toJson e)])]

def checkJson : Check → Json
  | .accepted r => Json.mkObj [("result", "accepted"), ("reach", scopeJson r)]
  | .outsideReach r => Json.mkObj [("result", "outside reach"), ("reach", scopeJson r)]
  | .illFormed ps => Json.mkObj [("result", "ill-formed"), ("primes", toJson ps)]
  | .notCanonical => Json.mkObj [("result", "not canonical")]
  | .replayFailed => Json.mkObj [("result", "replay failed")]

/-- `contra` needs equal variables and equations, so contradicting statements share this key
(`contraKey_eq`). Coefficients are left out; equal equations still give equal keys. -/
def contraKey (s : Stmt) : UInt64 := hash (s.vars, s.eqs.map (·.map Prod.fst))

theorem contraKey_eq {a b : Stmt} (h : contra a b = true) : contraKey a = contraKey b := by
  unfold contra at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  simp [contraKey, h.1.1, h.1.2]

/-- Items grouped by `contraKey`, each group in item order (`refuterIndex_getD`). -/
def refuterIndex (items : List Item) : Std.HashMap UInt64 (List Item) :=
  items.foldr (fun j m => m.insert (contraKey j.stmt) (j :: m.getD (contraKey j.stmt) [])) {}

theorem refuterIndex_getD (items : List Item) (k : UInt64) :
    (refuterIndex items).getD k [] = items.filter (fun j => contraKey j.stmt == k) := by
  induction items with
  | nil => simp [refuterIndex]
  | cons j rest ih =>
    simp only [refuterIndex, List.foldr_cons] at ih ⊢
    rw [Std.HashMap.getD_insert, List.filter_cons]
    by_cases hk : contraKey j.stmt = k
    · subst hk; simp [ih]
    · simp [hk, ih]

/-- The refuter search over one `contraKey` group finds what the scan of every item finds. -/
theorem refuter_find_eq (items : List Item) (s : Stmt) (q : Item → Bool) :
    ((refuterIndex items).getD (contraKey s) []).find? (fun j => q j && contra s j.stmt) =
      items.find? (fun j => q j && contra s j.stmt) := by
  rw [refuterIndex_getD, List.find?_filter]
  congr 1
  funext j
  cases hc : contra s j.stmt
  · simp
  · simp [contraKey_eq hc]

/-- `heldKeys` is the outcome's held claims as a set, so a lookup is `held` without the list scan.
`index` is `refuterIndex` of the plan's items; by `refuter_find_eq` the refuter is the first match
in item order. -/
def itemJson (heldKeys : Std.HashSet Nat) (index : Std.HashMap UInt64 (List Item)) (m : CheckMemo)
    (literals : Bool) (withdrawn : Std.HashSet Nat) (i : Item) : Json :=
  let refuter := ((index.getD (contraKey i.stmt) []).find? fun j => j.key != i.key && heldKeys.contains j.key &&
    i.scope.overlaps j.scope && ops.contra i.stmt j.stmt).map (·.key)
  let base : List (String × Json) := [("key", toJson i.key), ("kind", toJson (Corpus.kindName i.stmt.kind)),
    ("support", toJson (Corpus.supportName i.support)), ("held", toJson (heldKeys.contains i.key)),
    ("scope", scopeJson i.scope), ("refuter", toJson refuter)] ++
    (if literals then [("stmtLit", toJson (Corpus.stmtLit i.stmt)), ("scopeLit", toJson (Corpus.scopeLit i.scope))]
     else []) ++
    -- Only when true, so a ledger with no withdrawal prints exactly what 0.50 printed.
    (if withdrawn.contains i.key then [("withdrawn", toJson true)] else [])
  Json.mkObj (base ++ match i.support with
    | .receipt cert _ =>
      let c := checkWith m i.key i.stmt i.scope cert  -- = `check i.stmt i.scope cert` (`checkWith_eq`)
      [("check", checkJson c)] ++ (if c.ok then [] else [("diagnosis", toJson (diagnose i.stmt cert))])
    | .rule _ premises => [("premises", toJson premises)]
    | _ => [])

/-- Matroid claims whose system is exactly the Lean encoder's output (ENCODING-FRAME's side
condition; `GPBinding.Matroid.frame_iff` is the theorem). -/
def frameChecks (frames : Json) (items : List Item) : Json :=
  let entries := (frames.getArr?.toOption.getD #[]).toList
  -- The first item per key, as `items.find? (·.key == key)` would return it.
  let byKey : Std.HashMap Nat Item := items.foldl (fun m i => m.insertIfNew i.key i) {}
  -- Each frame re-derives its system independently, so the entries run in parallel (`parMap_eq`).
  toJson ((parMap (fun f => do
    let key ← (f.getObjValAs? Nat "key").toOption
    let n ← (f.getObjValAs? Nat "n").toOption
    let lines ← (f.getObjValAs? (List (List Nat)) "lines").toOption
    let i ← byKey[key]?
    pure (Json.mkObj [("key", toJson key),
      ("equal", toJson ((Matroid.Data.stmt ⟨n, lines⟩ i.stmt.kind) == some i.stmt))])) entries).filterMap id)

/-- The ledger's withdrawn claim keys (`withdrawn`, GP 0.51): absent is none, malformed is an error. -/
def withdrawnOf (plan0 : Json) : Except String (List Nat) :=
  (Families.nats plan0 "withdrawn").mapError (s!"withdrawn: {·}")

def runLedger (plan0 : Json) (withCandidates : Bool := false) : Json :=
  let frames := (plan0.getObjVal? "frames").toOption.getD (Json.arr #[])
  let plan := match plan0 with
    | .obj kvs => Json.obj ((kvs.erase "frames").erase "withdrawn")
    | j => j
  let case := Json.mkObj [("id", "ledger"), ("inputs", plan)]
  match withdrawnOf plan0, Families.plan case [] with
  | .error e, _ | _, .error e => Json.mkObj [("error", toJson e)]
  | .ok withdrawn, .ok p0 =>
    let p := { p0 with withdrawn }
    match p.elaboration with
    | some e => Json.mkObj [("elaboration", toJson e)]
    | none =>
      let m := p.checkMemo
      match p.runWith m with
      | .error e => Json.mkObj [("error", toJson e)]
      | .ok o =>
        let widened := o.widened.map fun (k, r) => Json.mkObj [("key", toJson k), ("reach", scopeJson r)]
        Json.mkObj (([("schema", Json.str "gp-ledger-run/v1"), ("items", toJson (parMap (itemJson (Std.HashSet.ofList o.state.claims) (refuterIndex p.items) m withCandidates
            (Std.HashSet.ofList withdrawn)) p.items)),
          ("widened", toJson widened), ("earned", toJson o.earned),
          ("frames", frameChecks frames p.items)] : List (String × Json)) ++
          (if withCandidates then [("candidates", toJson (Corpus.candidates "ledger" case []))] else []))

/-- The merge guard's question (post-G2 §1.5): does the log a merge would land still fold? The
ledger's claims are filed as `Plan.run` files them, unguarded (`fileRawAll`), the withdrawals' retracts
(`withdrawEvents`) and the ledger's lifecycle events (`lifecycle`, Kernel event JSON) are appended, and the
Kernel's `resolve` decides once (`guard`; `fold_ok_resolve`: the log folds exactly when it resolves). No
receipt is replayed. -/
def guardLedger (plan0 : Json) : Json :=
  let lifecycle := match plan0.getObjVal? "lifecycle" with
    | .ok (.arr es) => es.toList
    | _ => []
  let plan := match plan0 with
    | .obj kvs => Json.obj (((kvs.erase "frames").erase "lifecycle").erase "withdrawn")
    | j => j
  match withdrawnOf plan0, Families.plan (Json.mkObj [("id", "ledger"), ("inputs", plan)]) [] with
  | .error e, _ | _, .error e => Json.mkObj [("error", toJson e)]
  | .ok withdrawn, .ok p =>
    match p.elaboration, lifecycle.mapM Decoder.decodeEvent with
    | some e, _ => Json.mkObj [("elaboration", toJson e)]
    | none, .error e => Json.mkObj [("error", toJson s!"lifecycle event: {e}")]
    | none, .ok extra =>
      match guard ((fileRawAll p.items {}).events ++ withdrawEvents withdrawn ++ extra) with
      | .ok _ => Json.mkObj [("guard", "ok")]
      | .error e => Json.mkObj [("error", toJson e)]

end GPProfile.LedgerRun

def main (args : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let mut text := ""
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    text := text ++ line
  match Lean.Json.parse text with
  | .error e => IO.eprintln s!"gp_ledger: input is not JSON: {e}"; return 2
  | .ok plan =>
    if args.contains "--guard" then
      IO.println (GPProfile.LedgerRun.guardLedger plan).compress
      return 0
    IO.println (GPProfile.LedgerRun.runLedger plan (args.contains "--candidates")).compress
    return 0
