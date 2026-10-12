import GPProfile.Families.Base
import GPProfile.Real.Plan
import GPProfile.Real.Sections
import GPProfile.Real.Universe
import GPProfile.Real.NumberFieldFrontend

/-!
The 3b corpus frontend (3B-PROFILE-DESIGN.md, "Corpus frontend"): case JSON to a `Plan3` of the
summed profile. Like 3a's families, adapters are recognized by input keys, never by case id, and
they build profile inputs only: the Kernel fold decides.

Target contexts. `C` maps to the `alg` family at characteristic 0 (`Scope.char0Only`), so an SOS
receipt there refuses (GP-A10-C, GP-X345). `Q` maps to `orderFree` EMPTY at `semireal` (every
semireal field, ℚ included). `R` maps to `orderFree` at `real`, reached from `semireal` by the
Kernel's narrowing (K2). A case with no named context is read over ℚ.

Selected-root sign claims (generator `m`, interval `[lo, hi]`, expression `e`, sign `σ`) are `real`
NONEMPTY systems in one variable `w`: `m(w) = 0`, `sign e(w) = σ`, and the interval as sign atoms
(`w - lo` is `0` when `m(lo) = 0`, else `+1`; `w - hi` is `0` when `m(hi) = 0`, else `-1`). The held
meaning is "some real root of `m` in `[lo, hi]` has the sign": root uniqueness in the interval is
not proved (isolation is an untrusted search). The witness is the selected root itself.

Cases that need a checker that does not exist yet are routed to `pending` with the checker id
(post-M1 build order): never ACCEPT, never a fabricated REFUSE.
-/

namespace GPProfile.Real
open Lean GP50 GPProfile GPProfile.Families

/-- A case's route: a plan for the Kernel, or the checker it still needs. -/
inductive Route3 where
  | plan (p : Plan3)
  | pending (checker : String) (why : String)

/-! ## Inputs -/

def parseP (vars : List String) (t : String) : Except String Sparse := parse vars t

def strsOf (inputs : Json) (k : String) : Except String (List String) := do
  match obj? inputs k with
  | some v => (← v.getArr?).toList.mapM text
  | none => throw s!"missing input '{k}'"

/-- A rational constant written as a polynomial with no variables (`"2"`, `"-1/3"`). -/
def ratOf (t : String) : Except String Rat := do
  match ← parseP [] t with
  | [] => pure 0
  | [([], c)] => pure c
  | _ => throw s!"not a rational constant: '{t}'"

/-- The variables: declared, or the identifiers of the polynomials in order of appearance. -/
def varsOf (inputs : Json) (polys : List String) : Except String (List String) := do
  if has inputs "variables" then strsOf inputs "variables" else pure (polys.flatMap identifiers).eraseDups

/-- A univariate sparse polynomial as coefficients, lowest degree first. -/
def uniCoeffs (p : Sparse) : List Rat :=
  let d := p.foldl (fun d (e, _) => max d (e.headD 0)) 0
  (List.range (d + 1)).map fun i => (p.filter fun (e, _) => e.headD 0 == i).foldl (fun a (_, c) => a + c) 0

/-- `w - c` in one variable. -/
def linMinus (c : Rat) : Sparse := (canonical 1 [([1], 1), ([0], -c)]).getD []

def emptyStmt (vars : List String) (eqs : List Sparse) : Stmt := ⟨vars, eqs, [], .empty⟩

/-! ## Positivstellensatz/SOS cases -/

/-- `1 + Σ squares² + Σ cofactorᵢ · generatorᵢ = 0`: a `PCert` with guard exponent 0. -/
def sosCert (vars : List String) (squares cofactors : List String) : Except String PCert := do
  let sq ← squares.mapM (parseP vars)
  let qs ← cofactors.mapM (parseP vars)
  pure ⟨qs, 0, [.squares (sq.map ((1 : Rat), ·))], none⟩

/-- A family statement for an order-free claim at a named context. -/
def atContext (ctx : String) (s : Stmt) : Except String (Stmt3 × Scope3) :=
  match ctx with
  | "C" | "CC" => pure (.alg s, .alg Scope.char0Only)
  | "Q" | "QQ" => pure (.orderFree s, .semireal)
  | "R" | "RR" => pure (.orderFree s, .real)
  | c => throw s!"unknown target context '{c}'"

/-- An SOS receipt for the model's EMPTY claim at a context. The receipt binds the certificate's own
generators, so a certificate written for another model is detached (GP-X02, GP-X311). Over `R` the
receipt is filed at `semireal` and the claim reaches `real` by the Kernel's narrowing. -/
def sosPlan (ctx : String) (vars : List String) (model cert : List Sparse) (c : PCert) : Except String Plan3 := do
  let s := emptyStmt vars model
  let boundTo (wrap : Stmt → Stmt3) : Option Stmt3 :=
    if cert == model then none else some (wrap (emptyStmt vars cert))
  match ← atContext ctx s with
  | (.orderFree _, .real) =>
    pure { items := [{ key := 1, stmt := .orderFree s, scope := .semireal,
                       support := .receipt (.sos c) (boundTo .orderFree) },
                     { key := 2, stmt := .orderFree s, scope := .real, support := .narrow 1 }],
           requested := [2] }
  | (st, sc) =>
    let wrap : Stmt → Stmt3 := match st with | .alg _ => .alg | _ => .orderFree
    pure { items := [{ key := 1, stmt := st, scope := sc, support := .receipt (.sos c) (boundTo wrap) }],
           requested := [1] }

/-- `generators`, `squares`, `cofactors` and an optional `target_context`. -/
def sosTargetFamily (inputs : Json) : Except String Plan3 := do
  let gens ← strsOf inputs "generators"
  let vars ← varsOf inputs gens
  let model ← gens.mapM (parseP vars)
  sosPlan ((str? inputs "target_context").getD "Q") vars model model
    (← sosCert vars (← strsOf inputs "squares") (← strsOf inputs "cofactors"))

/-- A model and the generators a certificate was written for (GP-X01/X02, GP-X308–X311). -/
def sosModelFamily (inputs : Json) (modelKey certKey cofKey : String) : Except String Plan3 := do
  let mt ← strsOf inputs modelKey
  let ct ← strsOf inputs certKey
  let vars ← varsOf inputs (mt ++ ct)
  sosPlan "Q" vars (← mt.mapM (parseP vars)) (← ct.mapM (parseP vars))
    (← sosCert vars (← strsOf inputs "squares") (← strsOf inputs cofKey))

/-- GP-X343: an EMPTY claim whose only support is a route audit with these steps. A zero-step
route has no premises and no rule instance: the Kernel admits no derived warrant without one. The
same SOS identity is filed separately (claim 2, not requested) as the positive receipt control. -/
def routeAuditFamily (inputs : Json) : Except String Plan3 := do
  let gens ← strsOf inputs "generators"
  let vars ← varsOf inputs gens
  let s := emptyStmt vars (← gens.mapM (parseP vars))
  let steps ← nats inputs "route_steps"
  unless steps.isEmpty do throw "route steps beyond zero are not expressible"
  let (st, sc) ← atContext ((str? inputs "field").getD "Q") s
  let c ← sosCert vars (← strsOf inputs "squares") (← strsOf inputs "cofactors")
  let controls : List Item3 := match sc with
    | .real => [{ key := 2, stmt := st, scope := .semireal, support := .receipt (.sos c) },
                { key := 3, stmt := st, scope := .real, support := .narrow 2 }]
    | _ => [{ key := 2, stmt := st, scope := sc, support := .receipt (.sos c) }]
  pure { items := { key := 1, stmt := st, scope := sc, support := .route steps } :: controls, requested := [1] }

/-- GP-X345: ordered (SOS) receipts on the branches of a true cover, offered for the parent's
EMPTY claim at the `C` context. The cover is a 3a COVER claim whose branches are the parent's locus
(`identical_loci_cover`), held by a one-leaf split tree. The branch claims are `orderFree` EMPTY at
`semireal`, held by their SOS receipts. The parent is offered 3a's `byCover` rule, lifted: lifted
rules see only `alg` clauses, so the ordered premises do not bind and the rule refuses. -/
def orderedCoverFamily (inputs : Json) : Except String Plan3 := do
  let eqT ← strsOf inputs "source_equations"
  let vars ← varsOf inputs eqT
  let s := emptyStmt vars (← eqT.mapM (parseP vars))
  let branches ← strsOf inputs "branches"
  unless (obj? inputs "identical_loci_cover") == some (.bool true) do throw "only identical-loci covers are expressible"
  let sosJ ← match obj? inputs "ordered_sos" with | some j => pure j | none => throw "missing ordered_sos"
  let c ← sosCert vars (← strsOf sosJ "squares") (← strsOf sosJ "cofactors")
  let (parent, scope) ← atContext ((str? inputs "field").getD "Q") s
  let n := branches.length
  let cover : Stmt := { s with kind := .cover (branches.map fun _ => ([], [])) }
  let coverItem : Item3 :=
    { key := 1, stmt := .alg cover, scope := .alg Scope.char0Only, support := .receipt (.alg (.cover (.leaf 0 [] []))) }
  let branchItems := (List.range n).map fun j =>
    ({ key := j + 2, stmt := .orderFree s, scope := .semireal, support := .receipt (.sos c) } : Item3)
  let parentItem : Item3 :=
    { key := n + 2, stmt := parent, scope, support := .rule (.lift .byCover) ((List.range (n + 1)).map (· + 1)) }
  pure { items := coverItem :: branchItems ++ [parentItem], requested := [n + 2] }

/-! ## Selected-root sign receipts -/

/-- `generator`, `interval`, `expression`, `claimed_sign` (GP-X351–X354, GP-X404, GP-X405). -/
def selectedSignFamily (inputs : Json) : Except String Plan3 := do
  let gT ← text ((obj? inputs "generator").getD .null)
  let eT ← text ((obj? inputs "expression").getD .null)
  let [v] := (identifiers gT ++ identifiers eT).eraseDups | throw "selected-root signs need one variable"
  let m ← parseP [v] gT
  let e ← parseP [v] eT
  let [loT, hiT] ← strsOf inputs "interval" | throw "interval must be [lo, hi]"
  let lo ← ratOf loT
  let hi ← ratOf hiT
  let σ : Int ← match (obj? inputs "claimed_sign").map (·.getInt?) with
    | some (Except.ok k) => pure k
    | _ => throw "claimed_sign must be an integer"
  let mU := uniCoeffs m
  let atRoot (c : Rat) : Bool := RAlg.evalQ (RAlg.ofU mU) c == 0
  let sys : RealSys := ⟨[v], [m], [],
    [(e, σ), (linMinus lo, if atRoot lo then 0 else 1), (linMinus hi, if atRoot hi then 0 else -1)]⟩
  let w : RealWitness := ⟨mU, lo, hi, [[0, 1]]⟩
  pure { items := [{ key := 1, stmt := .real sys .nonempty, scope := .real, support := .receipt (.point w) }],
         requested := [1] }

/-! ## Selected-root covers (GP-X273, GP-X274) -/

/-- A selection `{field, variables, equations, selected_real_interval}`: one variable, one
equation `m`, the interval as sign atoms (encoded as in `selectedSignFamily`). -/
def selectionOf (j : Json) : Except String (String × Sparse × Rat × Rat × List (Sparse × Int)) := do
  unless (str? j "field").all (· == "Q") do throw "selected-root covers are read over Q"
  let [v] ← strsOf j "variables" | throw "a selection has one variable"
  let [mT] ← strsOf j "equations" | throw "a selection has one equation"
  let m ← parseP [v] mT
  let [loT, hiT] ← strsOf j "selected_real_interval" | throw "selected_real_interval must be [lo, hi]"
  let lo ← ratOf loT
  let hi ← ratOf hiT
  let atRoot (c : Rat) : Bool := RAlg.evalQ (RAlg.ofU (uniCoeffs m)) c == 0
  pure (v, m, lo, hi, [(linMinus lo, if atRoot lo then 0 else 1), (linMinus hi, if atRoot hi then 0 else -1)])

/-- `parent`, `branches`: a `realCover` claim at `real`, held by a selected-root cover receipt
(`rootCoverCheck`: Descartes uniqueness on the parent's interval, and a point replay of the parent
joined with a branch). -/
def selectedCoverFamily (inputs : Json) : Except String Plan3 := do
  let (v, m, lo, hi, atoms) ← selectionOf ((obj? inputs "parent").getD .null)
  let bJ ← match obj? inputs "branches" with | some b => b.getArr? | none => throw "missing branches"
  let branches ← bJ.toList.mapM fun j => do
    let (v', m', _, _, atoms') ← selectionOf j
    unless v' == v do throw "branches share the parent's variable"
    pure ({ eqs := [m'], guards := [], signs := atoms' } : RBranch)
  let parent : RealSys := ⟨[v], [m], [], atoms⟩
  let c : RootCoverCert := ⟨lo, hi, ⟨uniCoeffs m, lo, hi, [[0, 1]]⟩⟩
  pure { items := [{ key := 1, stmt := .realCover parent branches, scope := .real,
                     support := .receipt (.rootCover c) }], requested := [1] }

/-! ## Instantiation fixtures (DECISIONS.md, 2026-10-09 3b stop-and-ask calls) -/

/-- GP-X56 fixture: `variables`, `equations`, `source_context` `Q`, `certificate`
`rational_root`, `target` `char0_extensions`. The EMPTY claim at `ratField` is held by the
rational-root receipt; the same order-free claim in every characteristic-0 field is offered only
the Kernel's narrowing, and no scope order leads from `ratField` to an `alg` scope. -/
def ratRootFamily (inputs : Json) : Except String Plan3 := do
  unless str? inputs "source_context" == some "Q" && str? inputs "certificate" == some "rational_root" &&
      str? inputs "target" == some "char0_extensions" do throw "unsupported rational-root fixture"
  let eqT ← strsOf inputs "equations"
  let vars ← varsOf inputs eqT
  let s := emptyStmt vars (← eqT.mapM (parseP vars))
  pure { items := [{ key := 1, stmt := .orderFree s, scope := .ratField, support := .receipt .ratRoot },
                   { key := 2, stmt := .orderFree s, scope := .alg Scope.char0Only, support := .narrow 1 }],
         requested := [2] }

/-- GP-A11a fixture: a selected-root sign (`generator`, `interval`, `expression`, `claimed_sign`) held
at `real`, and a `substitution` (a ring automorphism). The attempted conclusion is the image system
with the sign atom copied unchanged; it is offered 3a's map rule, lifted, which binds only `alg`
premises: no rule moves sign atoms across a conjugation. -/
def conjugateSignFamily (inputs : Json) : Except String Plan3 := do
  let gT ← text ((obj? inputs "generator").getD .null)
  let eT ← text ((obj? inputs "expression").getD .null)
  let [v] := (identifiers gT ++ identifiers eT).eraseDups | throw "selected-root signs need one variable"
  let kvs ← match obj? inputs "substitution" with
    | some j => j.getObj?
    | none => throw "missing substitution"
  let [⟨v', phiJ⟩] := kvs.toArray.toList | throw "substitution must map the one variable"
  unless v' == v do throw "substitution must map the selected variable"
  let phi ← parseP [v] (← text phiJ)
  let p ← selectedSignFamily (inputs.setObjVal! "field" (Json.str "Q"))
  let some i := p.items.head? | throw "no selected-root item"
  let .real sys .nonempty := i.stmt | throw "not a selected-root system"
  let img (q : Sparse) : Except String Sparse := match compose 1 [phi] 1 q with
    | some r => pure r
    | none => throw "substitution does not compose"
  let e ← parseP [v] eT
  -- The image: every polynomial composed with φ (an involution), except the copied sign atom.
  let (eAtom, σ) :: interval := sys.signs | throw "no sign atom"
  unless eAtom == e do throw "the first atom is the predicate"
  let eqs ← sys.eqs.mapM img
  let atoms ← interval.mapM fun (q, τ) => do pure (← img q, τ)
  let image : RealSys := ⟨[v], eqs, [], (e, σ) :: atoms⟩
  pure { items := [i, { key := 2, stmt := .real image .nonempty, scope := .real,
                        support := .rule (.lift (.map [phi] [] [])) [1] }], requested := [2] }

/-! ## Dispatch -/

def pending (c why : String) : Except String Route3 := pure (.pending c why)

/-- Dispatch on input keys. -/
def frontend3 (case : Json) : Except String Route3 := do
  let inputs ← case.getObjVal? "inputs"
  let k := onlyKeys inputs
  let control := str? inputs "control"
  if has inputs "squares" && has inputs "generators" &&
      k ["variables", "generators", "squares", "cofactors", "target_context"] then
    return .plan (← sosTargetFamily inputs)
  if has inputs "certificate_generators" &&
      k ["variables", "model_generators", "certificate_generators", "cofactors", "squares"] then
    return .plan (← sosModelFamily inputs "model_generators" "certificate_generators" "cofactors")
  if has inputs "evidence_equations" &&
      k ["variables", "model_equations", "evidence_equations", "multipliers", "squares"] then
    return .plan (← sosModelFamily inputs "model_equations" "evidence_equations" "multipliers")
  if control == some "zero_step_vs_receipt" && k ["control", "field", "generators", "certificate",
      "squares", "cofactors", "route_steps", "attempted_authority"] then
    return .plan (← routeAuditFamily inputs)
  if control == some "legacy_partition_ordered_receipts" && k ["control", "source_equations", "branches",
      "identical_loci_cover", "cover_projection_supplied", "ordered_sos", "field", "branch_receipts_recorded"] then
    return .plan (← orderedCoverFamily inputs)
  if has inputs "generator" && has inputs "interval" && k ["control", "generator", "interval", "expression",
      "claimed_sign", "field", "point_universe"] && (str? inputs "field").all (· == "Q") &&
      (str? inputs "point_universe").all (· == "REAL_CLOSURE") then
    return .plan (← selectedSignFamily inputs)
  -- Point universes and images (R7): 3a statements and lifted 3a rules only.
  if has inputs "source_universe" && k ["variables", "equations", "source_universe", "target_universe",
      "relation", "question", "debt_reason"] then
    return .plan (← universeStepFamily inputs)
  if has inputs "native_empty_union_encoding" && k ["control", "coefficient_domain", "variables",
      "parent_equations", "semantic_branches", "native_empty_union_encoding", "geometric_test", "point_universe"] then
    return .plan (← coverUniverseFamily inputs)
  if has inputs "projection" && k ["equations", "projection", "reading", "point"] then
    return .plan (← imageFamily inputs)
  -- Number-field points (C4).
  if has inputs "field" && has inputs "model" && k ["control", "field", "model", "coordinate"] then
    return .plan (← nfPointFamily inputs)
  if has inputs "field_polynomial" && k ["variables", "generators", "guards", "point_universe", "field_polynomial",
      "coordinate", "proposed_change"] then
    return .plan (← nfUniverseFamily inputs)
  -- Selected-root covers and the 2026-10-09 fixtures (X56, A11a).
  if has inputs "parent" && has inputs "branches" && k ["parent", "branches"] then
    return .plan (← selectedCoverFamily inputs)
  if str? inputs "certificate" == some "rational_root" && k ["variables", "equations", "source_context",
      "claim", "certificate", "target"] && str? inputs "claim" == some "EMPTY" then
    return .plan (← ratRootFamily inputs)
  if has inputs "substitution" && has inputs "generator" && k ["generator", "interval", "expression",
      "claimed_sign", "substitution"] then
    return .plan (← conjugateSignFamily inputs)
  -- Pending: the checker each remaining family needs (M1 build order).
  if has inputs "minimal_polynomial" || (obj? inputs "field").any (has · "minimal_polynomial") ||
      has inputs "field_polynomial" then
    return ← pending "C4" "number-field witness (field arithmetic, irreducibility, universe of the point)"
  if has inputs "section" && k ["source", "target", "eliminated", "section", "proof_rows",
      "previously_bound_rows"] then
    return .plan (← sectionFamily inputs)
  if has inputs "membership_rows" && k ["source", "output", "eliminated", "membership_rows",
      "previously_bound_rows", "execution_evidence"] then
    return .plan (← outputFamily inputs)
  if has inputs "fixture_sha256" then
    match obj? case "fixture" with
    | some fixture => return .plan (← finiteUnitFamily fixture inputs)
    | none => return ← pending "C5" "the pinned fixture is absent or its bytes do not match the pin"
  throw "inputs fit no 3b frontend family"

/-! ## Diagnostics (reporting only; verdicts come from the fold) -/

/-- Why a certificate does or does not support a statement at a scope (agrees with `certOk3`). -/
def explain3 : Stmt3 → Scope3 → Cert3 → String
  | .orderFree s, .semireal, .sos c | .orderFree s, .real, .sos c =>
    match sosExplain s c with
    | .ok _ => "SOS replay accepted"
    | .error e => s!"SOS replay refused ({reprStr e})"
  | .real r .nonempty, .real, .point w =>
    match pointExplain r w with
    | .ok _ => "point replay accepted"
    | .error e => s!"point replay refused ({e})"
  | .orderFree s, .real, .point w =>
    if s.kind != .nonempty then "a point receipt proves NONEMPTY only" else
    match pointExplain (orderFreeSys s) w with
    | .ok _ => "point replay accepted (a point over ℝ)"
    | .error e => s!"point replay refused ({e})"
  | .alg s, .alg sc, .alg c => if (check s sc c).ok then "3a receipt accepted" else "3a receipt refused"
  | .alg s, .alg sc, .algPoint c =>
    if !sc.le Scope.char0Only then "algPoint is admitted only inside characteristic 0" else
    match algPointExplain s c with
    | .ok _ => "algPoint accepted"
    | .error e => s!"algPoint refused ({e})"
  | .nf p, .alg sc, .nf c =>
    if !sc.le Scope.char0Only then "a number-field receipt is admitted only inside characteristic 0" else
    match nfExplain p c with
    | .ok _ => "number-field replay accepted"
    | .error e => s!"number-field replay refused ({e})"
  | .orderFree s, .ratField, .ratRoot =>
    if ratRootCheck s then "rational-root certificate accepted" else "rational-root certificate refused"
  | .realCover r bs, .real, .rootCover c => rootCoverExplain r bs c
  | .real r .empty, .real, .ordered c =>
    match orderedExplain r c with
    | .ok _ => "ordered Positivstellensatz replay accepted"
    | .error e => s!"ordered Positivstellensatz replay refused ({reprStr e})"
  | .real r .empty, .real, .caseTree c =>
    match caseTreeExplain r c with
    | .ok _ => "case tree replay accepted"
    | .error e => s!"case tree replay refused ({e})"
  | .orderFree s, .real, .caseTree c =>
    if s.kind != .empty then "a case tree proves EMPTY only" else
    match caseTreeExplain (orderFreeSys s) c with
    | .ok _ => "case tree replay accepted"
    | .error e => s!"case tree replay refused ({e})"
  | .goal (.cover n m L), .real, .coverAll =>
    if coverAllCheck n m L then "exhaustive cover accepted: every graph with at least m edges is listed"
    else if coverLimit < coverCount n m then s!"too many graphs to list ({coverCount n m}); completeness needs another warrant"
    else "not exhaustive: a graph on n vertices with at least m edges is not listed"
  | _, _, .caseTree _ => "a case tree is admitted only for EMPTY claims at real scope (over ℝ)"
  | _, _, .ordered _ => "an ordered certificate is admitted only for real-system EMPTY claims at real scope"
  | _, _, .sos _ => "an SOS certificate is admitted only for order-free claims at semireal or real scope"
  | _, _, _ => "no admission for this evidence at this family and scope"

def familyName : Stmt3 → String
  | .alg _ => "alg" | .orderFree _ => "orderFree" | .real _ _ => "real" | .nf _ => "nf"
  | .realCover _ _ => "realCover" | .goal (.goal ..) => "goal" | .goal (.cover ..) => "cover"
  | .goal (.spine ..) => "spine"

def scopeName : Scope3 → String
  | .alg sc => s!"alg {scopeCanon sc}" | .semireal => "semireal" | .real => "real"
  | .ratField => "ratField"

def certName : Cert3 → String
  | .alg _ => "3a receipt" | .sos _ => "SOS receipt" | .point _ => "point receipt" | .algPoint _ => "algPoint receipt"
  | .nf _ => "number-field receipt" | .ratRoot => "rational-root receipt"
  | .rootCover _ => "selected-root cover receipt" | .ordered _ => "ordered Positivstellensatz receipt"
  | .caseTree _ => "case-tree receipt" | .coverAll => "exhaustive cover receipt"

def supportName3 : Support3 → String
  | .none => "none"
  | .receipt c none => certName c
  | .receipt c (some _) => s!"{certName c} bound to another statement"
  | .rule (.lift _) _ => "lifted 3a rule"
  | .rule .k1Empty _ => "rule K1a"
  | .rule .k1Nonempty _ => "rule K1b"
  | .rule (.realize ..) _ => "rule realize"
  | .rule .spine _ => "rule spine"
  | .rule .decide _ => "rule decide"
  | .narrow k => s!"narrowing (K2) from claim {k}"
  | .route steps => s!"route audit ({steps.length} steps)"

/-- Why a requested claim is not held. -/
def refusal (p : Plan3) (state : RuntimeState) (i : Item3) : String :=
  match i.support with
  | .none => "unsupported"
  | .receipt _ (some s) =>
    if s == i.stmt then "custody: the receipt is bound to different inputs"
    else "custody: the receipt is bound to a different statement"
  | .receipt c none => s!"checker: {explain3 i.stmt i.scope c}"
  | .rule (.lift d) ps =>
    if ps.any fun k => (p.items.find? (·.key == k)).any fun j => familyName j.stmt != "alg" then
      "rule refused: a lifted 3a rule binds only alg premises"
    else (liftNoRow p i d ps).getD "rule refused"
  | .rule (.realize ..) _ => "rule realize refused: its premise must be an order-free NONEMPTY claim over ℝ whose " ++
    "statement is exactly the Lean encoder's for the rule's graph, on the goal's n vertices with at least its m edges"
  | .rule .spine _ => "rule spine refused: it needs one order-free EMPTY claim over ℝ per cover graph, in order, " ++
    "each exactly the Lean encoder's statement for that graph"
  | .rule .decide _ => "rule decide refused: it needs spine n m L and cover n m L over ℝ, with the goal's n and m and " ++
    "the same graphs L"
  | .rule _ _ => "rule refused"
  | .narrow k =>
    if !held state k then s!"narrowing from unheld claim {k}" else
    match p.items.find? (·.key == k) with
    | some j => if Scope3.le i.scope j.scope then "narrowing refused"
      else s!"narrowing refused: no scope order from {scopeName j.scope} to {scopeName i.scope}"
    | none => "narrowing refused"
  | .route steps => s!"a {steps.length}-step route audit has no rule instance: not evidence"

end GPProfile.Real
