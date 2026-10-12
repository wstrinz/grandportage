import GPProfile.Corpus
import GPProfile.Families
import GPProfile.Diagnose
import GPProfile.Real.Frontend
import GPProfile.Real.Memo3
import GPProfile.UDG
import GPProfile.Real.GoalSurface
import GP50.Decoder

/-!
The 3b campaign ledger runner (`gp_ledger3`, behind `tools/gp.py`). It reads the 3b part of a
ledger on stdin, written in the explicit 3b statement surface (`claims`, `requested`), files every
claim through the commit guard and folds with `admission3` (`Plan3.run`), and prints every claim's
status with its check and mechanism. The `gp` CLI renders the views; this executable decides, and
nothing here constructs a verdict outside `Plan3.run`. `check`, `diagnosis` and `mechanism` are
reporting only.

A claim names its `family`:
- `alg`: a 3a claim in the 3a surface (`Families.surfaceHead`, `surfaceItem`), with its 3a
  certificate or lifted 3a rule, or an `alg_point` certificate;
- `orderFree` and `real`: `variables`, `equations`, `nonzero`, `signs` (`[polynomial, -1 | 0 | 1]`,
  `real` only), `kind` `EMPTY` or `NONEMPTY`, and `context` `semireal`, `real` or `rat_field`;
- `realCover`: a `real` parent and `branches` (`equations`, `nonzero`, `signs`), at `real`;
- `nf`: `symbol`, `minimal_polynomial`, `variables`, `equations`, `nonzero` and `point`, at
  characteristic 0.

Certificates (`type`): `sos`, `ordered`, `real_point`, `alg_point`, `nf`, `rational_root`,
`root_cover`, `case_tree`, `cover_all`. Rules: `k1a`, `k1b`, `narrow`, and the goal rules `realize`, `spine`,
`decide` (A2; the goal family `goal`, `cover`, `spine` is read by `GoalSurface`). Untrusted searches (`algPointPropose`, `nfPropose`)
fill what a receipt leaves out; their output is replayed by the checkers like any receipt.

`udgFrames` (optional, HW61 G-2): entries `{key, n, edges, gauge}` for graph-bound (`gp claim --udg`)
claims. Each is reported `equal` exactly when the claim is order-free and its statement is the Lean
encoder's (`GPProfile.UDG.Data.stmt`) for that graph, gauge and kind: ENCODING-FRAME's side
condition, with `GPBinding.UDG.udg_frame_iff` the theorem. Reporting only; the fold is unchanged.

Fast paths (ud22 performance, 2026-10-10) are `@[csimp]` twins at the end of this file: the
definitions above stay the specification. A run checks each receipt once (`CheckMemo3`, read by the
fold and the report); each claim elaborates and is checked in its own task.
-/

namespace GPProfile.Real.LedgerRun3
open Lean GP50 GPProfile GPProfile.Families GPProfile.Real

/-! ## Inputs -/

/-- A list of polynomial or rational texts (strings or JSON numbers). -/
def texts (j : Json) (k : String) : Except String (List String) :=
  match obj? j k with
  | some v => do (← v.getArr?).toList.mapM text
  | none => pure []

def rats (j : Json) (k : String) : Except String (List Rat) := do (← texts j k).mapM ratOf

def polys (vars : List String) (j : Json) (k : String) : Except String (List Sparse) := do
  (← texts j k).mapM (canonP vars)

/-- Sign atoms `[polynomial, σ]` with `σ ∈ {-1, 0, 1}`. -/
def signsOf (vars : List String) (j : Json) : Except String (List (Sparse × Int)) := do
  match obj? j "signs" with
  | none => pure []
  | some a => (← a.getArr?).toList.mapM fun atom => do
    match (← atom.getArr?).toList with
    | [p, s] =>
      let σ ← s.getInt?
      unless σ == -1 || σ == 0 || σ == 1 do throw "a sign is -1, 0 or 1"
      pure (← canonP vars (← text p), σ)
    | _ => throw "a sign atom is [polynomial, sign]"

def sysOf (j : Json) : Except String RealSys := do
  let vars ← strs j "variables"
  pure ⟨vars, ← polys vars j "equations", ← polys vars j "nonzero", ← signsOf vars j⟩

def existOf (j : Json) : Except String Exist :=
  match str? j "kind" with
  | some "EMPTY" => pure .empty
  | some "NONEMPTY" => pure .nonempty
  | _ => throw "an order-free or real claim has kind EMPTY or NONEMPTY"

def algScopeOf (c : Json) : Except String Scope :=
  match (obj? c "characteristic").bind (·.getNat?.toOption), obj? c "outside" with
  | some p, none => pure (.only p)
  | none, some _ => do pure (.outside (← nats c "outside"))
  | none, none => pure .char0Only
  | some _, some _ => throw "a claim has a characteristic or an outside list, not both"

def scope3Of (c : Json) : Except String Scope3 :=
  match str? c "context" with
  | some "semireal" => pure .semireal
  | some "real" => pure .real
  | some "rat_field" => pure .ratField
  | some x => throw s!"unknown context {x}"
  | none => do pure (.alg (← algScopeOf c))

/-- Coordinates in `symbol`, one per variable, as coefficient lists. -/
def coordsIn (sym : String) (vars : List String) (pt : Json) : Except String (List (List Rat)) :=
  vars.mapM fun v => do uniOf sym (← text (← need (obj? pt v) s!"point lacks {v}"))

def nfOf (c : Json) : Except String NFPoint := do
  let sym ← need (str? c "symbol") "no symbol"
  let m ← uniOf sym (← need (str? c "minimal_polynomial") "no minimal_polynomial")
  let vars ← strs c "variables"
  let pt ← need (obj? c "point") "no point"
  let coords ← vars.mapM fun v => do nfCoordinate sym m (← need (obj? pt v) s!"point lacks {v}")
  pure ⟨m, [], vars, ← polys vars c "equations", ← polys vars c "nonzero", coords.map ([·])⟩

def branchesOf (vars : List String) (c : Json) : Except String (List RBranch) := do
  match obj? c "branches" with
  | some (.arr bs) => bs.toList.mapM fun b => do
    pure ⟨← polys vars b "equations", ← polys vars b "nonzero", ← signsOf vars b⟩
  | _ => throw "a cover has a list of branches"

/-- The statement of a non-`alg` claim. -/
def stmtOf (fam : String) (c : Json) : Except String Stmt3 := do
  match fam with
  | "orderFree" =>
    let r ← sysOf c
    unless r.signs.isEmpty do throw "an order-free claim has no sign atoms"
    let k : Kind := match ← existOf c with | .empty => .empty | .nonempty => .nonempty
    pure (.orderFree ⟨r.vars, r.eqs, r.guards, k⟩)
  | "real" => pure (.real (← sysOf c) (← existOf c))
  | "realCover" => let r ← sysOf c; pure (.realCover r (← branchesOf r.vars c))
  | "nf" => pure (.nf (← nfOf c))
  | f => (GoalSurface.stmtOf? f c).getD (throw s!"unknown family {f}")

def Stmt3.vars : Stmt3 → List String
  | .alg s | .orderFree s => s.vars
  | .real r _ | .realCover r _ => r.vars
  | .nf p => p.vars
  | .goal _ => []

/-! ## Certificates and rules -/

/-- Squares `"p"` (weight 1) or `[weight, "p"]`. -/
def squaresOf (vars : List String) (j : Json) : Except String (List (Rat × Sparse)) := do
  (← j.getArr?).toList.mapM fun s => do
    match s with
    | .str t => pure (1, ← canonP vars t)
    | _ =>
      match (← s.getArr?).toList with
      | [w, p] => pure (← ratOf (← text w), ← canonP vars (← text p))
      | _ => throw "a square is \"p\" or [weight, \"p\"]"

/-- A Gram block `{monomials, matrix}`. -/
def gramOf (vars : List String) (j : Json) : Except String Block := do
  let monos ← (← strs j "monomials").mapM (surfaceMonomial vars)
  let rows ← match obj? j "matrix" with
    | some (.arr rs) => rs.toList.mapM fun r => do (← r.getArr?).toList.mapM fun x => do ratOf (← text x)
    | _ => throw "a Gram block has a matrix"
  pure (.gram monos rows)

/-- The SOS blocks of a certificate or cone term: `squares` and `gram` (a list of Gram blocks). -/
def blocksOf (vars : List String) (c : Json) : Except String (List Block) := do
  let sq ← match obj? c "squares" with
    | some j => pure [Block.squares (← squaresOf vars j)]
    | none => pure []
  let gr ← match obj? c "gram" with
    | some (.arr gs) => gs.toList.mapM (gramOf vars)
    | some _ => throw "gram is a list of blocks"
    | none => pure []
  pure (sq ++ gr)

/-- A real point: `symbol`, `polynomial`, `interval` and `point` in the symbol; with no polynomial,
a rational `point` (θ the root 0 of θ in [-1, 1]). -/
def witnessOf (vars : List String) (c : Json) : Except String RealWitness := do
  let pt ← need (obj? c "point") "no point"
  match str? c "polynomial" with
  | none => pure ⟨[0, 1], -1, 1, (← ratPoint vars pt).map ([·])⟩
  | some mT =>
    let sym ← need (str? c "symbol") "no symbol"
    let [lo, hi] ← rats c "interval" | throw "interval must be [lo, hi]"
    pure ⟨← uniOf sym mT, lo, hi, ← coordsIn sym vars pt⟩

def algPointOf (s : Stmt) (c : Json) : Except String Cert3 := do
  let sym ← need (str? c "symbol") "no symbol"
  let m ← uniOf sym (← need (str? c "polynomial") "no polynomial")
  let coords ← coordsIn sym s.vars (← need (obj? c "point") "no point")
  match obj? c "bezout" with
  | some (.arr bs) =>
    let pairs ← bs.toList.mapM fun b => do
      match (← b.getArr?).toList with
      | [a, b] => pure (← uniOf sym (← text a), ← uniOf sym (← text b))
      | _ => throw "a Bezout pair is [a, b]"
    pure (.algPoint ⟨m, coords, pairs⟩)
  | some _ => throw "bezout is a list of pairs"
  | none => pure (.algPoint ((algPointPropose s m coords).getD ⟨m, coords, []⟩))

/-- Selected guards (`guards`): indices, each an index `i` or `[i, e]` (`e` copies of `i`, so
`gᵢ^e` in the product). Absent: every guard. -/
def guardSelOf (c : Json) : Except String (Option (List Nat)) := do
  match obj? c "guards" with
  | none => pure none
  | some (.arr gs) => some <$> (gs.toList.mapM fun g => do
      match g with
      | Json.arr #[i, e] =>
        let (i, e) := (← i.getNat?, ← e.getNat?)
        unless e ≤ maxExponent do throw s!"a guard exponent is at most {maxExponent}"
        pure (List.replicate e i)
      | _ => pure [← g.getNat?]).map List.flatten
  | some _ => throw "guards is a list of guard indices (or [index, exponent] pairs)"

def orderedOf (vars : List String) (c : Json) : Except String OCert := do
  let cone ← match obj? c "cone" with
    | some (.arr ts) => ts.toList.mapM fun t => do
      let bs ← blocksOf vars t
      bs.mapM fun b => do pure (⟨← nats t "atoms", b⟩ : ConeTerm)
    | _ => pure []
  pure ⟨← polys vars c "cofactors", ← nats c "positive_powers", natField c "guard_power", cone.flatten,
    ← guardSelOf c⟩

/-- A list of exactly `k` naturals. -/
def natsK (j : Json) (k : Nat) (what : String) : Except String (List Nat) := do
  let ns ← (← j.getArr?).toList.mapM fun x => x.getNat?
  unless ns.length == k do throw s!"{what} has {k} entries"
  pure ns

/-- A weighted rhombus `[λ, [a, b, c, d]]`, or with citations
`[λ, [a, b, c, d], [eab, ebc, ecd, eda], [gac, gbd]]`. -/
def rhombusOf (j : Json) : Except String (Rat × Rhombus) := do
  let (w, cyc, es, gs) ← match (← j.getArr?).toList with
    | [w, cyc] => pure (w, cyc, Json.arr #[0, 0, 0, 0], Json.arr #[0, 0])
    | [w, cyc, es, gs] => pure (w, cyc, es, gs)
    | _ => throw "a rhombus is [weight, [a, b, c, d]] (with optional citations)"
  let [a, b, c, d] ← natsK cyc 4 "a rhombus cycle" | throw "a rhombus cycle has 4 vertices"
  let [eab, ebc, ecd, eda] ← natsK es 4 "a rhombus's edge citations" | throw "4 edge citations"
  let [gac, gbd] ← natsK gs 2 "a rhombus's diagonal citations" | throw "2 diagonal citations"
  pure (← ratOf (← text w), ⟨a, b, c, d, eab, ebc, ecd, eda, gac, gbd⟩)

/-- A case-tree node: `collision`, `unit` (an L1b step, with its `then` child), `ordered`, or a
`split` (`zero` or `sign`) on `poly`. -/
partial def caseTreeOf (vars : List String) (j : Json) : Except String CaseTree := do
  if let some c := obj? j "collision" then
    let rs ← match obj? c "rhombi" with
      | some (.arr rs) => rs.toList.mapM rhombusOf
      | _ => throw "a collision has a list of rhombi"
    let [u, v] ← natsK (← need (obj? c "pair") "a collision has a pair") 2 "a collision pair"
      | throw "a collision pair is [u, v]"
    return .collision ⟨rs, u, v, natField c "guard"⟩
  if let some c := obj? j "unit" then
    let rs ← match obj? c "rhombi" with
      | some (.arr rs) => rs.toList.mapM rhombusOf
      | _ => throw "a unit step has a list of rhombi"
    let [u, v] ← natsK (← need (obj? c "pair") "a unit step has a pair") 2 "a unit pair"
      | throw "a unit pair is [u, v]"
    let [a, b] ← natsK (← need (obj? c "via") "a unit step has a via edge") 2 "a via edge"
      | throw "a via edge is [a, b]"
    let sign ← match obj? c "sign" with
      | some s => s.getInt?
      | none => pure 1
    let t ← caseTreeOf vars (← need (obj? j "then") "a unit step lacks its then branch")
    return .unit ⟨rs, u, v, a, b, sign, natField c "edge"⟩ t
  if let some c := obj? j "ordered" then return .ordered (← orderedOf vars c)
  let child := fun (k : String) => do caseTreeOf vars (← need (obj? j k) s!"a split lacks its {k} branch")
  match str? j "split" with
  | some "zero" =>
    let p ← canonP vars (← need (str? j "poly") "a split has a poly")
    pure (.zero p (← child "zero") (← child "nonzero"))
  | some "sign" =>
    let p ← canonP vars (← need (str? j "poly") "a split has a poly")
    pure (.sign p (← child "neg") (← child "zero") (← child "pos"))
  | _ => throw "a case-tree node is a collision, a unit step, an ordered leaf, or a zero or sign split"

/-- A variable's index. -/
def varIdx (vars : List String) (v : String) : Except String Nat :=
  match vars.idxOf? v with
  | some i => pure i
  | none => throw s!"unknown variable {v}"

/-- A case-tree certificate: `points` (`[x, y]` variable names per vertex) and `tree`; citations
are searched (untrusted, replayed) unless `cited` is true. -/
def caseTreeCertOf (r : RealSys) (c : Json) : Except String CaseTreeCert := do
  let pts ← match obj? c "points" with
    | some (.arr ps) => ps.toList.mapM fun p => do
      match (← p.getArr?).toList with
      | [x, y] => pure (← varIdx r.vars (← text x), ← varIdx r.vars (← text y))
      | _ => throw "a point is [x, y]"
    | _ => throw "a case tree has points"
  let cert : CaseTreeCert := ⟨pts, ← caseTreeOf r.vars (← need (obj? c "tree") "a case tree has a tree")⟩
  pure (if (obj? c "cited").bind (·.getBool?.toOption) == some true then cert else caseTreeCite r cert)

def certOf (stmt : Stmt3) (c : Json) : Except String Cert3 := do
  let vars := Stmt3.vars stmt
  match (str? c "type").getD "" with
  | "sos" => pure (.sos ⟨← polys vars c "cofactors", natField c "guard_power", ← blocksOf vars c,
      ← guardSelOf c⟩)
  | "ordered" => pure (.ordered (← orderedOf vars c))
  | "case_tree" =>
    match stmt with
    | .real r _ => pure (.caseTree (← caseTreeCertOf r c))
    | .orderFree s => pure (.caseTree (← caseTreeCertOf (orderFreeSys s) c))
    | _ => throw "a case_tree certificate is for an EMPTY claim over ℝ"
  | "real_point" => pure (.point (← witnessOf vars c))
  | "alg_point" =>
    match stmt with
    | .alg s => algPointOf s c
    | _ => throw "an alg_point certificate is for a 3a NOT_IN_IDEAL(1) claim"
  | "nf" =>
    match stmt with
    | .nf p => pure (.nf (nfPropose p ((nats c "gcd_degrees").toOption.filter (!·.isEmpty))))
    | _ => throw "an nf certificate is for a number-field point claim"
  | "rational_root" => pure .ratRoot
  | "cover_all" => pure .coverAll
  | "root_cover" =>
    let [lo, hi] ← rats c "interval" | throw "interval must be [lo, hi]"
    let w ← match obj? c "point", stmt with
      | some _, _ => witnessOf vars c
      | none, .realCover r _ =>
        let some m := r.eqs.head? | throw "the parent has no equation"
        pure ⟨uniCoeffs m, lo, hi, [[0, 1]]⟩
      | none, _ => throw "a root_cover certificate is for a cover claim"
    pure (.rootCover ⟨lo, hi, w⟩)
  | t => throw s!"unknown certificate type {t}"

def ruleOf (rule : Json) (premises : List Nat) : Except String Support3 :=
  match str? rule "type", premises with
  | some "k1a", _ => pure (.rule .k1Empty premises)
  | some "k1b", _ => pure (.rule .k1Nonempty premises)
  | some "narrow", [k] => pure (.narrow k)
  | some "narrow", _ => throw "narrow has exactly one premise"
  | _, _ => (GoalSurface.ruleOf? rule premises).getD (throw "unknown rule type")

/-- A 3a item as an `alg` item of the summed profile. -/
def liftItem (i : Item) : Except String Item3 := do
  let support : Support3 ← match i.support with
    | .none => pure .none
    | .receipt c none => pure (.receipt (.alg c))
    | .rule d ps => pure (.rule (.lift d) ps)
    | _ => throw "unsupported 3a support"
  pure { key := i.key, stmt := .alg i.stmt, scope := .alg i.scope, extra := i.extra, support }

def isThreeB (j : Option Json) (k : String) (types : List String) : Bool :=
  (j.bind fun x => str? x k).any types.contains

/-- An `alg` claim: the 3a surface, or an `alg_point` certificate, or a 3b rule. -/
def algItem (stmts : Std.HashMap Nat Stmt3) (c : Json) : Except String Item3 := do
  let c' := match c with | .obj kvs => Json.obj (kvs.erase "family") | j => j
  let h ← surfaceHead c'
  if isThreeB (obj? c "certificate") "type" ["alg_point"] then
    return { key := h.key, stmt := .alg h.stmt, scope := .alg h.scope, extra := h.extra,
             support := .receipt (← certOf (.alg h.stmt) (← need (obj? c "certificate") "no certificate")) }
  if isThreeB (obj? c "rule") "type" ["k1a", "k1b", "narrow"] then
    return { key := h.key, stmt := .alg h.stmt, scope := .alg h.scope, extra := h.extra,
             support := ← ruleOf (← need (obj? c "rule") "no rule") h.premises }
  let prem? := h.premises.head?.bind fun k => match stmts[k]? with | some (.alg s) => some s | _ => none
  liftItem (← surfaceItem prem? c' h)

def keyOf (c : Json) : Except String Nat := need ((obj? c "key").bind (·.getNat?.toOption)) "claim without key"

def claimKeys : List String :=
  ["key", "family", "variables", "equations", "nonzero", "signs", "branches", "kind", "context", "characteristic",
   "outside", "symbol", "minimal_polynomial", "point", "inputs", "certificate", "rule", "premises"] ++ GoalSurface.keys

/-- A claim's statement, for premise lookups (`alg` claims through the 3a surface head). -/
def headStmt (c : Json) : Except String (Nat × Stmt3) := do
  let fam ← need (str? c "family") "no family"
  if fam == "alg" then
    let c' := match c with | .obj kvs => Json.obj (kvs.erase "family") | j => j
    let h ← surfaceHead c'
    return (h.key, .alg h.stmt)
  pure (← keyOf c, ← stmtOf fam c)

def item3 (stmts : Std.HashMap Nat Stmt3) (c : Json) : Except String Item3 := do
  let fam ← need (str? c "family") "no family"
  if fam == "alg" then return ← algItem stmts c
  unless onlyKeys c claimKeys do throw "unknown claim key"
  let key ← keyOf c
  let stmt ← stmtOf fam c
  let scope ← scope3Of c
  let premises ← nats c "premises"
  let support ← match obj? c "certificate", obj? c "rule" with
    | some cert, none => do pure (.receipt (← certOf stmt cert))
    | none, some r => ruleOf r premises
    | none, none => pure .none
    | _, _ => throw "a claim has a certificate or a rule, not both"
  pure { key, stmt, scope, extra := ← strs c "inputs", support }

/-- An error, prefixed with the claim key it belongs to. -/
def named {α : Type} (c : Json) (r : Except String α) : Except String α :=
  r.mapError fun e => s!"claim {((obj? c "key").bind (·.getNat?.toOption)).getD 0}: {e}"

/-- The plan: every statement first (so premises resolve in any order), then every item. -/
def plan3 (inputs : Json) : Except String Plan3 := do
  let claims ← match obj? inputs "claims" with
    | some (.arr cs) => pure cs.toList
    | _ => throw "no claims"
  let heads ← claims.mapM fun c => named c (headStmt c)
  let stmts : Std.HashMap Nat Stmt3 := heads.foldl (fun m (k, s) => m.insertIfNew k s) {}
  let items ← claims.mapM fun c => named c (item3 stmts c)
  pure { items, requested := ← nats inputs "requested" }

/-! ## Output -/

def scopeJson (s : Scope) : Json :=
  Json.mkObj [("char0", toJson s.char0), ("primes", match s.primes with
    | .finite ps => Json.mkObj [("finite", toJson ps)]
    | .cofinite e => Json.mkObj [("cofinite", toJson e)])]

def kindName3 : Stmt3 → String
  | .alg s | .orderFree s => Corpus.kindName s.kind
  | .real _ e => existCanon e
  | .nf _ => "NF_POINT"
  | .realCover _ _ => "COVER"
  | .goal (.goal ..) => "GOAL" | .goal (.cover ..) => "COVER_COMPLETE" | .goal (.spine ..) => "SPINE"

/-- Scopes that share a field: 3a's overlap within `alg`, else one inside the other (reporting). -/
def overlaps3 : Scope3 → Scope3 → Bool
  | .alg a, .alg b => a.overlaps b
  | a, b => Scope3.le a b || Scope3.le b a

/-- The receipt's check, for reporting: 3a's own check (with reach) for a 3a certificate, else
the 3b checker's verdict and its explanation. The fold has already decided `held` (`h`, read here
only for the wording of an accepted 3a receipt's diagnosis). -/
def checkFields (i : Item3) (c : Cert3) (h : Bool) : List (String × Json) :=
  match i.stmt, i.scope, c with
  | .alg s, .alg sc, .alg c3 =>
    let chk := check s sc c3
    -- `diagnose` names a refusal; an accepted receipt's reach covers the requested scope.
    let d := match chk with
      | .accepted _ => (if h then "held: " else "") ++ "3a receipt accepted; its reach covers the requested scope"
      | _ => diagnose s c3
    let r := match chk with
      | .accepted r => Json.mkObj [("result", "accepted"), ("reach", scopeJson r)]
      | .outsideReach r => Json.mkObj [("result", "outside reach"), ("reach", scopeJson r)]
      | .illFormed ps => Json.mkObj [("result", "ill-formed"), ("primes", toJson ps)]
      | .notCanonical => Json.mkObj [("result", "not canonical")]
      | .replayFailed => Json.mkObj [("result", "replay failed")]
    [("check", r), ("diagnosis", toJson d)]
  | st, sc, _ =>
    [("check", Json.mkObj [("result", if certOk3 st sc c then "accepted" else "replay failed")]),
     ("diagnosis", toJson (explain3 st sc c))]

def itemJson3 (p : Plan3) (o : Outcome3) (i : Item3) : Json :=
  let h := held o.state i.key
  let refuter := (p.items.find? fun j => j.key != i.key && held o.state j.key && overlaps3 i.scope j.scope &&
    ops3.contra i.stmt j.stmt).map (·.key)
  let base : List (String × Json) := [("key", toJson i.key), ("family", toJson (familyName i.stmt)),
    ("kind", toJson (kindName3 i.stmt)), ("scope", toJson (scopeName i.scope)),
    ("support", toJson (supportName3 i.support)), ("held", toJson h), ("refuter", toJson refuter),
    ("mechanism", toJson (if h then s!"held by {supportName3 i.support}" else refusal p o.state i))]
  Json.mkObj (base ++ match i.support with
    | .receipt c _ => checkFields i c h
    | .rule _ ps => [("premises", toJson ps)]
    | .narrow k => [("premises", toJson [k])]
    | _ => [])

/-- Graph-bound claims whose order-free statement is exactly the Lean encoder's for their graph
(`frameChecks` in `GPProfile.Ledger`, for unit-distance graphs). Entries run in parallel. -/
def udgFrameChecks (frames : Json) (items : List Item3) : Json :=
  let entries := (frames.getArr?.toOption.getD #[]).toList
  let byKey : Std.HashMap Nat Item3 := items.foldl (fun m i => m.insertIfNew i.key i) {}
  toJson ((parMap (fun f => do
    let key ← (f.getObjValAs? Nat "key").toOption
    let n ← (f.getObjValAs? Nat "n").toOption
    let edges ← (f.getObjValAs? (List (List Nat)) "edges").toOption
    let gauge := ((f.getObjValAs? Bool "gauge").toOption).getD false
    let i ← byKey[key]?
    let pairs := edges.filterMap fun | [a, b] => some (a, b) | _ => none
    let equal := pairs.length == edges.length && match i.stmt with
      | .orderFree s => UDG.Data.stmt ⟨n, pairs, gauge⟩ s.kind == some s
      | _ => false
    pure (Json.mkObj [("key", toJson key), ("equal", toJson equal)])) entries).filterMap id)

def runLedger3 (inputs : Json) : Json :=
  match plan3 inputs with
  | .error e => Json.mkObj [("error", toJson e)]
  | .ok p =>
    match p.run with
    | .error e => Json.mkObj [("error", toJson e)]
    | .ok o => Json.mkObj [("schema", "gp-ledger3-run/v1"), ("items", toJson (p.items.map (itemJson3 p o))),
      ("earned", toJson o.earned),
      ("udgFrames", udgFrameChecks ((obj? inputs "udgFrames").getD (Json.arr #[])) p.items)]

/-- `gp_ledger3 --guard`, the merge guard for the 3b part (`GPProfile.LedgerRun.guardLedger`'s twin): every
claim is filed as `Plan3.run` files it, unguarded (`Ledger3.fileRaw`), the `lifecycle` events (Kernel event
JSON) are appended, and the Kernel's `resolve` decides once (`guard`). No receipt is replayed. -/
def guardLedger3 (inputs : Json) : Json :=
  let lifecycle := match obj? inputs "lifecycle" with | some (.arr es) => es.toList | _ => []
  match plan3 inputs, lifecycle.mapM Decoder.decodeEvent with
  | .error e, _ => Json.mkObj [("error", toJson e)]
  | .ok _, .error e => Json.mkObj [("error", toJson s!"lifecycle event: {e}")]
  | .ok p, .ok extra =>
    match guard ((p.items.foldl Ledger3.fileRaw {}).events ++ extra) with
    | .ok _ => Json.mkObj [("guard", "ok")]
    | .error e => Json.mkObj [("error", toJson e)]

/-! ## Fast paths (each `@[csimp]`, proved equal to the definition it replaces) -/

/-- `plan3` up to the items: the claims and every claim's statement. -/
def plan3Head (inputs : Json) : Except String (List Json × Std.HashMap Nat Stmt3) := do
  let claims ← match obj? inputs "claims" with
    | some (.arr cs) => pure cs.toList
    | _ => throw "no claims"
  let heads ← claims.mapM fun c => named c (headStmt c)
  pure (claims, heads.foldl (fun m (k, s) => m.insertIfNew k s) {})

/-- `plan3` from each claim's elaborated item. -/
def plan3From (inputs : Json) (its : List (Except String Item3)) : Except String Plan3 := do
  let items ← its.mapM id
  pure { items, requested := ← nats inputs "requested" }

theorem plan3_split (inputs : Json) : plan3 inputs =
    (plan3Head inputs >>= fun h => plan3From inputs (h.1.map fun c => named c (item3 h.2 c))) := by
  unfold plan3 plan3Head plan3From
  cases obj? inputs "claims" with
  | none => rfl
  | some j => cases j <;> simp only [bind_assoc, pure_bind, List.mapM_map, Function.comp_def, id_eq] <;> rfl

/-- `plan3`, and a memo of every receipt's verdict. Each claim elaborates and is checked in its own
task, so checks overlap the elaboration of other claims (`plan3Memo_fst`: the plan is `plan3`'s). -/
def plan3Memo (inputs : Json) : Except String Plan3 × CheckMemo3 :=
  match plan3Head inputs with
  | .error e => (.error e, CheckMemo3.empty)
  | .ok (claims, stmts) =>
    -- Large claims (case trees) start first, on their own threads: they bound the run.
    let prio := fun (c : Json) => if c.compress.length > 32768 then Task.Priority.dedicated else Task.Priority.default
    let done := parEachPrio prio (fun c => let it := named c (item3 stmts c); (it, itemEntry it)) claims
    (plan3From inputs (done.map (·.1)), CheckMemo3.ofEntries (done.map (·.2)))

theorem plan3Memo_fst (inputs : Json) : (plan3Memo inputs).1 = plan3 inputs := by
  rw [plan3_split]
  unfold plan3Memo
  cases plan3Head inputs with
  | error e => rfl
  | ok h => simp only [parEachPrio_eq, List.map_map, Function.comp_def]; rfl

/-- `checkFields`, the verdict read through the memo and an accepted diagnosis not replayed again. -/
def checkFieldsWith (m : CheckMemo3) (i : Item3) (c : Cert3) (h : Bool) : List (String × Json) :=
  match i.stmt, i.scope, c with
  | .alg _, .alg _, .alg _ => checkFields i c h
  | st, sc, _ =>
    let v := certOk3With m i.key st sc c
    [("check", Json.mkObj [("result", if v then "accepted" else "replay failed")]),
     ("diagnosis", toJson (explain3With v st sc c))]

theorem checkFieldsWith_eq (m : CheckMemo3) (i : Item3) (c : Cert3) (h : Bool) :
    checkFieldsWith m i c h = checkFields i c h := by
  unfold checkFieldsWith
  split
  · rfl
  · rename_i hne
    unfold checkFields
    split
    · exfalso
      apply hne <;> first | assumption | rfl
    · simp only [certOk3With_eq, explain3With_eq]

/-- `itemJson3` with `checkFieldsWith` (`itemJson3With_eq`). -/
def itemJson3With (m : CheckMemo3) (p : Plan3) (o : Outcome3) (i : Item3) : Json :=
  let h := held o.state i.key
  let refuter := (p.items.find? fun j => j.key != i.key && held o.state j.key && overlaps3 i.scope j.scope &&
    ops3.contra i.stmt j.stmt).map (·.key)
  let base : List (String × Json) := [("key", toJson i.key), ("family", toJson (familyName i.stmt)),
    ("kind", toJson (kindName3 i.stmt)), ("scope", toJson (scopeName i.scope)),
    ("support", toJson (supportName3 i.support)), ("held", toJson h), ("refuter", toJson refuter),
    ("mechanism", toJson (if h then s!"held by {supportName3 i.support}" else refusal p o.state i))]
  Json.mkObj (base ++ match i.support with
    | .receipt c _ => checkFieldsWith m i c h
    | .rule _ ps => [("premises", toJson ps)]
    | .narrow k => [("premises", toJson [k])]
    | _ => [])

theorem itemJson3With_eq (m : CheckMemo3) (p : Plan3) (o : Outcome3) :
    itemJson3With m p o = itemJson3 p o := by
  funext i
  simp only [itemJson3With, itemJson3, checkFieldsWith_eq]

/-- `runLedger3`: one memo of every receipt's verdict (`plan3Memo`), read by the fold
(`Plan3.runWith_eq`) and the report (`itemJson3With_eq`). -/
def runLedger3Fast (inputs : Json) : Json :=
  let pm := plan3Memo inputs
  match pm.1 with
  | .error e => Json.mkObj [("error", toJson e)]
  | .ok p =>
    -- The frame checks need only the plan: they run while the fold and the report do.
    let udg := Task.spawn fun _ => udgFrameChecks ((obj? inputs "udgFrames").getD (Json.arr #[])) p.items
    match p.runWith pm.2 with
    | .error e => Json.mkObj [("error", toJson e)]
    | .ok o => Json.mkObj [("schema", "gp-ledger3-run/v1"), ("items", toJson (p.items.map (itemJson3With pm.2 p o))),
      ("earned", toJson o.earned), ("udgFrames", udg.get)]

@[csimp] theorem runLedger3_eq_fast : @runLedger3 = @runLedger3Fast := by
  funext inputs
  simp only [runLedger3, runLedger3Fast, plan3Memo_fst, Plan3.runWith_eq, itemJson3With_eq] <;> rfl

end GPProfile.Real.LedgerRun3

open GPProfile.Real in
def main (args : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let mut text := ""
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    text := text ++ line
  match Lean.Json.parse text with
  | .error e => IO.eprintln s!"gp_ledger3: input is not JSON: {e}"; return 2
  | .ok plan =>
    let run := if args.contains "--guard" then LedgerRun3.guardLedger3 else LedgerRun3.runLedger3
    IO.println (run plan).compress; return 0
