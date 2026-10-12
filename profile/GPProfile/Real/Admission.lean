import GPProfile.Rules
import GPProfile.Real.Profile
import GPProfile.Real.SOS
import GPProfile.Real.AlgPoint
import GPProfile.Real.NumberField
import GPProfile.Real.RootCover
import GPProfile.Real.Ordered
import GPProfile.Real.CaseTree
import GPProfile.Real.CaseTreePar

/-!
3b admission ([3B-PROFILE-DESIGN.md](../../../docs/3B-PROFILE-DESIGN.md), "Evidence" and "Kind-1
rules"). Receipts and K3 rules for the summed profile `ops3`, with 3a's binding discipline: a
warrant binds the clause of its claim key, version and binding; claim keys and receipt names are
unique; a receipt names its claim, version and binding.

Receipt acceptance, by family and scope:

- `alg s` at `alg sc` with a 3a certificate: exactly 3a's `check s sc c`;
- `alg s` at an `alg` scope inside characteristic 0 with an `algPoint` certificate:
  `algPointCheck s c`;
- `orderFree s` (EMPTY) at `semireal` or `real` with an SOS certificate: `sosCheck s c`;
- `real r .nonempty` at `real` with a point: `pointCheck r w`; `orderFree s` (NONEMPTY) at `real`
  with a point: `pointCheck` of `s` as a real system without sign atoms;
- `nf p` at an `alg` scope inside characteristic 0 with a number-field certificate: `nfCheck p c`;
- `orderFree s` (EMPTY) at `ratField` with a rational-root certificate: `ratRootCheck s`;
- `realCover r bs` at `real` with a selected-root cover certificate: `rootCoverCheck r bs c`;
- `real r .empty` at `real` with an ordered Positivstellensatz certificate: `orderedCheck r c`
  (C7; never at `semireal`, whose fields have no fixed ordering);
- `real r .empty` at `real`, or `orderFree s` (EMPTY) at `real`, with a refutation case tree:
  `caseTreeCheck` (G-6: splits, L1a collision and ordered leaves; ℝ only);
- `goal (cover n m L)` at `real` with a `cover_all` receipt: `coverAllCheck n m L` (A2: every graph on
  `n` vertices with at least `m` edges is listed).

Everything else refuses. In particular an SOS certificate never supports an `alg` statement or
anything at an `alg` scope (GP-A10-C, GP-X345).

Rules: 3a's rules act on `alg` clauses through 3a's own `acceptsRule`, on the projection of the
clause list to its `alg` clauses (`algClauses`). The kind-1 rules K1a and K1b carry a 3a EMPTY or
NONEMPTY claim, held at a scope containing characteristic 0, to `orderFree` at `semireal` (K1a) or
`real` (K1b): every semireal field, ℝ included, has characteristic 0.

The goal rules (A2, `GPProfile.Real.Goal`), each concluding at `real` from premises at `real`:
`realize` (one encoder-exact NONEMPTY claim ⇒ `goal n m true`), `spine` (one encoder-exact EMPTY claim
per graph of `L` ⇒ `spine n m L`) and `decide` (`spine n m L` and `cover n m L` ⇒ `goal n m false`).
-/

namespace GPProfile.Real
open GPProfile GP50

abbrev Clause3 := Semantic.Clause ops3

/-! ## Evidence -/

inductive Cert3 where
  /-- A 3a certificate, for an `alg` statement at an `alg` scope. -/
  | alg (c : Cert)
  /-- A Positivstellensatz/SOS refutation (`sosCheck`). -/
  | sos (c : PCert)
  /-- A real algebraic point (`pointCheck`). -/
  | point (w : RealWitness)
  /-- An algebraic point with Bezout certificates (`algPointCheck`): NOT_IN_IDEAL(1) at
  characteristic 0, u(22)'s complex relaxation. -/
  | algPoint (c : AlgPointCert)
  /-- A number-field point certificate (`nfCheck`): irreducibility of `m`, equations reduce to 0
  and guards are units in the finite algebra (C4, C5). -/
  | nf (c : NFCert)
  /-- A rational-root certificate (`ratRootCheck`): EMPTY over ℚ. -/
  | ratRoot
  /-- A selected-root cover (`rootCoverCheck`): Descartes uniqueness plus a branch point. -/
  | rootCover (c : RootCoverCert)
  /-- An ordered Positivstellensatz refutation (`orderedCheck`, C7): EMPTY over ℝ with sign atoms. -/
  | ordered (c : OCert)
  /-- A refutation case tree (`caseTreeCheck`, G-6): EMPTY over ℝ. -/
  | caseTree (c : CaseTreeCert)
  /-- An exhaustive cover (`coverAllCheck`, A2): every graph with at least `m` edges is listed. -/
  | coverAll

structure Receipt3 where
  name : String
  claim : Nat
  version : Nat
  binding : Binding
  cert : Cert3

/-- A 3a statement read as a real system without sign atoms. -/
def orderFreeSys (s : Stmt) : RealSys := ⟨s.vars, s.eqs, s.guards, []⟩

/-- Whether a certificate supports a statement at a scope. -/
def certOk3 : Stmt3 → Scope3 → Cert3 → Bool
  | .alg s, .alg sc, .alg c => (check s sc c).ok
  | .alg s, .alg sc, .algPoint c => sc.le Scope.char0Only && algPointCheck s c
  | .orderFree s, .semireal, .sos c => sosCheck s c
  | .orderFree s, .real, .sos c => sosCheck s c
  | .real r .nonempty, .real, .point w => pointCheck r w
  | .real r .empty, .real, .ordered c => orderedCheck r c
  | .real r .empty, .real, .caseTree c => caseTreeCheck r c
  | .orderFree s, .real, .caseTree c => s.kind == .empty && caseTreeCheck (orderFreeSys s) c
  | .orderFree s, .real, .point w => s.kind == .nonempty && pointCheck (orderFreeSys s) w
  | .nf p, .alg sc, .nf c => sc.le Scope.char0Only && nfCheck p c
  | .orderFree s, .ratField, .ratRoot => ratRootCheck s
  | .realCover r bs, .real, .rootCover c => rootCoverCheck r bs c
  | .goal (.cover n m L), .real, .coverAll => coverAllCheck n m L
  | _, _, _ => false

def wellFormed3 (clauses : List Clause3) (receipts : List Receipt3) : Bool :=
  (clauses.map (·.key)).eraseDups.length == clauses.length &&
    (receipts.map (·.name)).eraseDups.length == receipts.length

/-- 3a's `acceptsWith`, over the summed profile. -/
def accepts3With (wf : Bool) (clauses : List Clause3) (receipts : List Receipt3) (w : Warrant)
    (name : String) : Bool :=
  wf &&
    clauses.any fun c => c.key == w.claim && c.version == w.version && decide (c.binding = w.binding) &&
      receipts.any fun r => r.name == name && r.claim == c.key && r.version == c.version &&
        decide (r.binding = c.binding) && certOk3 c.stmt c.scope r.cert

/-! ## Rules -/

inductive RuleData3 where
  /-- A 3a rule, on `alg` clauses only. -/
  | lift (d : RuleData)
  /-- K1a: `alg s` EMPTY at a scope with characteristic 0 ⇒ `orderFree s` EMPTY at `semireal`. -/
  | k1Empty
  /-- K1b: `alg s` NONEMPTY at a scope with characteristic 0 ⇒ `orderFree s` NONEMPTY at `real`. -/
  | k1Nonempty
  /-- A2 `realize`: a graph's encoder-exact NONEMPTY claim over ℝ ⇒ `goal n m true` (the graph's
  edges and gauge are data; the check compares statements). -/
  | realize (edges : EdgeList) (gauge : Bool)
  /-- A2 `spine`: one encoder-exact EMPTY claim over ℝ per graph of `L` ⇒ `spine n m L`. -/
  | spine
  /-- A2 `decide`: `spine n m L` and `cover n m L` ⇒ `goal n m false`. -/
  | decide
  deriving Repr, DecidableEq

structure RuleInst3 where
  name : String
  conclusion : Nat
  premises : List Nat
  data : RuleData3
  deriving Repr, DecidableEq

/-- An `alg` clause as a 3a clause. -/
def Clause3.toAlg (c : Clause3) : Option Clause :=
  match c.stmt, c.scope with
  | .alg s, .alg sc => some { key := c.key, version := c.version, binding := c.binding, stmt := s, scope := sc }
  | _, _ => none

/-- The `alg` clauses, as 3a clauses: the clause list 3a's rules see. -/
def algClauses (clauses : List Clause3) : List Clause := clauses.filterMap Clause3.toAlg

def keysUnique3 (clauses : List Clause3) : Bool :=
  (clauses.map (·.key)).eraseDups.length == clauses.length

/-- `Semantic.boundClause ops3` with its key-uniqueness check passed in (`boundWith3_eq`). -/
def boundWith3 (unique : Bool) (clauses : List Clause3) (w : Warrant) : Option Clause3 :=
  if !unique then none else
    clauses.find? fun c => c.key == w.claim && c.version == w.version && c.binding == w.binding

theorem boundWith3_eq (clauses : List Clause3) (w : Warrant) :
    boundWith3 (keysUnique3 clauses) clauses w = Semantic.boundClause ops3 clauses w := rfl

/-- A kind-1 instance: the single premise is `alg s` of kind `k` at a scope with characteristic 0,
and the conclusion is `orderFree s` at a scope inside `target`. -/
def k1Ok (k : Kind) (target : Scope3) (c : Clause3) : List Clause3 → Bool
  | [p] =>
    match p.stmt, p.scope, c.stmt with
    | .alg s, .alg sc, .orderFree s' => decide (s' = s) && s.kind == k && sc.char0 && Scope3.le c.scope target
    | _, _, _ => false
  | _ => false

/-! ### The goal rules (A2) -/

/-- `realize`: the conclusion is `goal n m true` at `real`; the one premise is an order-free claim at
`real` whose statement passes `realizeOk` for the rule's graph. -/
def realizeRuleOk (edges : EdgeList) (gauge : Bool) (c : Clause3) : List Clause3 → Bool
  | [p] =>
    match c.stmt, c.scope, p.stmt, p.scope with
    | .goal (.goal n m true), .real, .orderFree s, .real => realizeOk n m edges gauge s
    | _, _, _, _ => false
  | _ => false

/-- One premise per graph, in order: each an order-free claim at `real` passing `exclusionOk`. -/
def spinePremisesOk (n : Nat) : List EdgeList → List Clause3 → Bool
  | [], [] => true
  | l :: L, p :: ps =>
    (match p.stmt, p.scope with
      | .orderFree s, .real => exclusionOk n l s
      | _, _ => false) && spinePremisesOk n L ps
  | _, _ => false

/-- `spine`: the conclusion is `spine n m L` at `real`. -/
def spineRuleOk (c : Clause3) (ps : List Clause3) : Bool :=
  match c.stmt, c.scope with
  | .goal (.spine n _ L), .real => spinePremisesOk n L ps
  | _, _ => false

/-- `decide`: the conclusion is `goal n m false` at `real`; the premises are `spine n m L` and
`cover n m L` at `real`, with identical `n`, `m` and `L`. -/
def decideRuleOk (c : Clause3) : List Clause3 → Bool
  | [sp, cv] =>
    match c.stmt, c.scope, sp.stmt, sp.scope, cv.stmt, cv.scope with
    | .goal (.goal n m false), .real, .goal (.spine n₁ m₁ L₁), .real, .goal (.cover n₂ m₂ L₂), .real =>
      n₁ == n && m₁ == m && n₂ == n && m₂ == m && decide (L₁ = L₂)
    | _, _, _, _, _, _ => false
  | _ => false

/-- The 3a rule instance a lifted rule names. -/
def RuleInst3.lift (r : RuleInst3) (d : RuleData) : RuleInst := ⟨r.name, r.conclusion, r.premises, d⟩

/-- One rule instance's verdict. A lifted rule is 3a's `acceptsRule` on the `alg` clauses. -/
def ruleOk3 (unique uniqueAlg : Bool) (clauses : List Clause3) (algCl : List Clause) (r : RuleInst3)
    (w : Warrant) (premises : List Warrant) : Bool :=
  match r.data with
  | .lift d => acceptsRuleWith (namesDistinct [r.lift d]) uniqueAlg algCl [r.lift d] w premises r.name
  | .k1Empty =>
    match boundWith3 unique clauses w, premises.mapM (boundWith3 unique clauses) with
    | some c, some ps => k1Ok .empty .semireal c ps
    | _, _ => false
  | .k1Nonempty =>
    match boundWith3 unique clauses w, premises.mapM (boundWith3 unique clauses) with
    | some c, some ps => k1Ok .nonempty .real c ps
    | _, _ => false
  | .realize edges gauge =>
    match boundWith3 unique clauses w, premises.mapM (boundWith3 unique clauses) with
    | some c, some ps => realizeRuleOk edges gauge c ps
    | _, _ => false
  | .spine =>
    match boundWith3 unique clauses w, premises.mapM (boundWith3 unique clauses) with
    | some c, some ps => spineRuleOk c ps
    | _, _ => false
  | .decide =>
    match boundWith3 unique clauses w, premises.mapM (boundWith3 unique clauses) with
    | some c, some ps => decideRuleOk c ps
    | _, _ => false

def namesDistinct3 (rules : List RuleInst3) : Bool := (rules.map (·.name)).eraseDups.length == rules.length

def acceptsRule3With (distinct unique uniqueAlg : Bool) (clauses : List Clause3) (algCl : List Clause)
    (rules : List RuleInst3) (w : Warrant) (premises : List Warrant) (name : String) : Bool :=
  distinct && unique &&
    rules.any fun r => r.name == name && r.conclusion == w.claim &&
      r.premises == premises.map (·.claim) && ruleOk3 unique uniqueAlg clauses algCl r w premises

/-! ## Admission -/

/-- Receipts and rules; each uniqueness check and the `alg` projection once per admission. -/
def base3 (clauses : List Clause3) (receipts : List Receipt3) (rules : List RuleInst3) : Admission :=
  let algCl := algClauses clauses
  { receipt := accepts3With (wellFormed3 clauses receipts) clauses receipts
    proof := fun _ _ => false
    rule := acceptsRule3With (namesDistinct3 rules) (keysUnique3 clauses) (keysUnique algCl) clauses
      algCl rules
    narrow := fun _ _ => false }

/-- 3b admission: receipts, rules (3a's lifted, kind-1) and the Kernel's narrowing. -/
def admission3 (clauses : List Clause3) (receipts : List Receipt3) (rules : List RuleInst3) : Admission :=
  Semantic.withNarrowing ops3 clauses (base3 clauses receipts rules)

end GPProfile.Real
