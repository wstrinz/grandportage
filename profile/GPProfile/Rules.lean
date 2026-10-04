import GPProfile.Algebra

/-!
K3 rules R1–R4 and their C4 relation certificates (post-G2 §3.3–3.4). Every rule is carry
kind 3. A rule instance names its conclusion and premise claims; acceptance checks the bound
clauses' statements against the rule's direction table, replays the relation certificate's
C1/C3 obligations, and requires the conclusion scope inside every premise scope and inside the
certificate's computed reach.
-/

namespace GPProfile
open Hex GP50

/-! ## Scope intersection -/

def Scope.meet (a b : Scope) : Scope := ⟨a.char0 && b.char0, meetPrimes a.primes b.primes⟩

def Scope.all : Scope := .outside []

/-- The reach of a list of certificate obligations: the meet of their reaches. -/
def reachAll (obs : List (Stmt × Cert)) : Option Scope :=
  (obs.mapM fun o => reach o.1 o.2).map fun rs => rs.foldl Scope.meet Scope.all

/-! ## C4 relation certificates -/

/-- IN_IDEAL transport `L → T` by the sound condition (G3a review §3): each loose equation is
IN_IDEAL on the tight system with its guards (any `k`), and each loose guard is nonvanishing on the
tight locus (C1 on the augmented system, as in `inclusionObligations`). In `K[x][1/g_T]/I_T` the
loose equations vanish and the loose guards are units, so `h·g_Lʲ ∈ I_L` puts `h` in `I_T`. -/
def idealInclusionObligations (T L : Stmt) (eqCerts guardCerts : List Cert) :
    Option (List (Stmt × Cert)) :=
  if T.vars != L.vars || eqCerts.length != L.eqs.length || guardCerts.length != L.guards.length
  then none
  else some ((L.eqs.zip eqCerts).map (fun (e, c) => (⟨T.vars, T.eqs, T.guards, .inIdeal e⟩, c)) ++
    (L.guards.zip guardCerts).map (fun (g, c) => (⟨T.vars, T.eqs ++ [g], T.guards, .empty⟩, c)))

/-- `p ∘ φ`: substitute the source polynomials `φ` for the target variables. -/
def compose (nS : Nat) (phi : List Sparse) (nT : Nat) (p : Sparse) : Option Sparse := do
  let gs ← phi.mapM (toHexQ nS)
  if gs.length != nT then none else
  let q ← toHexQ nT p
  let r := MvPoly.subst (fun i => gs.getD i.val 0) q
  -- Certified round trip: the sparse output reads back as exactly the computed polynomial.
  if toHexQ nS (ofHex r) == some r then some (ofHex r) else none

/-- `φ : locus_S → locus_T`: each target equation composed with `φ` vanishes on the source
locus (C3); each composed target guard is nonvanishing there (C1 on the augmented system). -/
def mapObligations (S T : Stmt) (phi : List Sparse) (eqCerts guardCerts : List Cert) :
    Option (List (Stmt × Cert)) := do
  if phi.length != T.vars.length || eqCerts.length != T.eqs.length ||
      guardCerts.length != T.guards.length then none else
  let eqs ← T.eqs.mapM (compose S.vars.length phi T.vars.length)
  let guards ← T.guards.mapM (compose S.vars.length phi T.vars.length)
  pure ((eqs.zip eqCerts).map (fun (e, c) => (⟨S.vars, S.eqs, S.guards, .vanishesOn e⟩, c)) ++
    (guards.zip guardCerts).map (fun (g, c) => (⟨S.vars, S.eqs ++ [g], S.guards, .empty⟩, c)))

/-- IN_IDEAL along `φ : locus_S → locus_T` (G3a review §3, the R3 IN_IDEAL row): each composed
target equation is IN_IDEAL on the source system with its guards; each composed target guard is
nonvanishing on the source locus (C1, as in `mapObligations`). -/
def idealMapObligations (S T : Stmt) (phi : List Sparse) (eqCerts guardCerts : List Cert) :
    Option (List (Stmt × Cert)) := do
  if phi.length != T.vars.length || eqCerts.length != T.eqs.length ||
      guardCerts.length != T.guards.length then none else
  let eqs ← T.eqs.mapM (compose S.vars.length phi T.vars.length)
  let guards ← T.guards.mapM (compose S.vars.length phi T.vars.length)
  pure ((eqs.zip eqCerts).map (fun (e, c) => (⟨S.vars, S.eqs, S.guards, .inIdeal e⟩, c)) ++
    (guards.zip guardCerts).map (fun (g, c) => (⟨S.vars, S.eqs ++ [g], S.guards, .empty⟩, c)))

/-! ## Rules -/

inductive RuleData where
  /-- R1: IN_IDEAL(h) ⇒ VANISHES_ON(h) on the same locus. -/
  | r1
  /-- R2: inclusion `locus_T ⊆ locus_L` by C4. -/
  | inclusion (eqCerts guardCerts : List Cert)
  /-- R3: polynomial map `φ : locus_S → locus_T` by C4. -/
  | map (phi : List Sparse) (eqCerts guardCerts : List Cert)
  /-- R4: object cover by the structural split on `h`. -/
  | split (h : Sparse)
  /-- Bridge (G3a review §2, §6): NONEMPTY on the system with `h` added as a guard gives
  NOT_IN_IDEAL(h); NONEMPTY gives NOT_IN_IDEAL(1), geometric nonemptiness, on the same system. -/
  | witness
  /-- R4 generalized (G3a review §2): a COVER premise plus, for each branch, the conclusion's
  EMPTY or VANISHES_ON claim on the branch subsystem gives the claim on the whole system. -/
  | byCover
  deriving Repr, DecidableEq

/-- Primes dividing a denominator in the rule's own data (the map `φ`). -/
def RuleData.primes : RuleData → List Nat
  | .map phi _ _ => denominatorPrimes (phi.flatMap Sparse.coeffs)
  | _ => []

/-- Every 3a K3 rule is carry kind 3 (post-G2 §3.4). -/
def RuleData.carryKind (_ : RuleData) : Nat := 3

structure RuleInst where
  name : String
  conclusion : Nat
  premises : List Nat
  data : RuleData
  deriving Repr, DecidableEq

def sameSystem (a b : Stmt) : Bool := a.vars == b.vars && a.eqs == b.eqs && a.guards == b.guards

/-- The direction tables of §3.4, and the relation certificate's computed reach. -/
def ruleReach (C : Stmt) (Ps : List Stmt) : RuleData → Option Scope
  | .r1 =>
    match Ps with
    | [P] =>
      match P.kind, C.kind with
      | .inIdeal h, .vanishesOn h' => if sameSystem P C && h == h' then some Scope.all else none
      | _, _ => none
    | _ => none
  | .inclusion eqCerts guardCerts =>
    match Ps with
    | [P] =>
      if P.kind != C.kind then none else
      match C.kind with
      -- EMPTY and VANISHES_ON move loose → tight: the premise is L, the conclusion T.
      | .empty | .vanishesOn _ => (inclusionObligations C P eqCerts guardCerts).bind reachAll
      -- IN_IDEAL moves loose → tight with ideal-level equation obligations.
      | .inIdeal _ => (idealInclusionObligations C P eqCerts guardCerts).bind reachAll
      -- NONEMPTY moves tight → loose: the premise is T, the conclusion L.
      | .nonempty => (inclusionObligations P C eqCerts guardCerts).bind reachAll
      -- NOT_IN_IDEAL(1), geometric nonemptiness, moves tight → loose too (review §6(ii)).
      | .notInIdeal h =>
        if h == oneP C.vars.length then (inclusionObligations P C eqCerts guardCerts).bind reachAll
        else none
      -- The refutation and cover kinds have no inclusion transport.
      | _ => none
    | _ => none
  | .map phi eqCerts guardCerts =>
    match Ps with
    | [P] =>
      match P.kind, C.kind with
      -- NONEMPTY moves S → T: the premise is the source.
      | .nonempty, .nonempty => (mapObligations P C phi eqCerts guardCerts).bind reachAll
      -- EMPTY moves T → S; EMPTY S → T is refused (GP-X360).
      | .empty, .empty => (mapObligations C P phi eqCerts guardCerts).bind reachAll
      -- VANISHES_ON(h) on T gives VANISHES_ON(h ∘ φ) on S.
      | .vanishesOn h, .vanishesOn h' =>
        if compose C.vars.length phi P.vars.length h == some h' then
          (mapObligations C P phi eqCerts guardCerts).bind reachAll
        else none
      -- NOT_IN_IDEAL(1) moves S → T like NONEMPTY (review §6(ii)).
      | .notInIdeal h, .notInIdeal h' =>
        if h == oneP P.vars.length && h' == oneP C.vars.length then
          (mapObligations P C phi eqCerts guardCerts).bind reachAll
        else none
      -- IN_IDEAL(h) on T gives IN_IDEAL(h ∘ φ) on S, with ideal-level equation obligations.
      | .inIdeal h, .inIdeal h' =>
        if compose C.vars.length phi P.vars.length h == some h' then
          (idealMapObligations C P phi eqCerts guardCerts).bind reachAll
        else none
      | _, _ => none
    | _ => none
  | .witness =>
    match Ps with
    | [P] =>
      match P.kind, C.kind with
      | .nonempty, .notInIdeal h =>
        if P.vars == C.vars && P.eqs == C.eqs &&
            (P.guards == C.guards ++ [h] || (P.guards == C.guards && h == oneP C.vars.length))
        then some Scope.all else none
      | _, _ => none
    | _ => none
  | .byCover =>
    match Ps with
    | P :: Qs =>
      match P.kind with
      | .cover bs =>
        let kindOk := match C.kind with | .empty | .vanishesOn _ => true | _ => false
        if kindOk && sameSystem P C && Qs.length == bs.length &&
            (bs.zip Qs).all (fun (b, Q) => Q == { C with eqs := C.eqs ++ b.1, guards := C.guards ++ b.2 })
        then some Scope.all else none
      | _ => none
    | [] => none
  | .split h =>
    match Ps with
    | [B₁, B₂] =>
      let parentKind := match C.kind with | .empty | .vanishesOn _ => true | _ => false
      if parentKind && B₁ == { C with eqs := C.eqs ++ [h] } && B₂ == { C with guards := C.guards ++ [h] }
      then some Scope.all else none
    | _ => none

def acceptsRule (clauses : List Clause) (rules : List RuleInst) (w : Warrant)
    (premises : List Warrant) (name : String) : Bool :=
  (rules.map (·.name)).eraseDups.length == rules.length &&
  rules.any fun r => r.name == name && r.conclusion == w.claim &&
    r.premises == premises.map (·.claim) &&
    match Semantic.boundClause ops clauses w, premises.mapM (Semantic.boundClause ops clauses) with
    | some c, some ps =>
      c.stmt.canonical && ps.all (fun p => c.scope.le p.scope) &&
        -- The conclusion scope keeps every statement and `φ` coefficient meaningful.
        c.scope.avoids (union c.stmt.primes (union (ps.flatMap (·.stmt.primes)) r.data.primes)) &&
        match ruleReach c.stmt (ps.map (·.stmt)) r.data with
        | some rr => c.scope.le rr
        | none => false
    | _, _ => false

/-- A binder record (G1 decision 2): a named theorem warrant bound to an exact canonical
statement and scope by the binding package's binder, which checked its type and axioms. -/
structure BinderRecord where
  declaration : String
  statementHash : String
  scopeHash : String
  deriving Repr, DecidableEq

/-- Theorem warrants are accepted only against a binder record for the exact bound clause. -/
def acceptsProof (clauses : List Clause) (records : List BinderRecord) (w : Warrant) (decl : String) : Bool :=
  (Semantic.boundClause ops clauses w).isSome &&
  records.any fun r => r.declaration == decl && r.statementHash == w.binding.statementHash &&
    r.scopeHash == w.binding.scopeHash

/-- Receipts, rules, bound theorems and narrowing together. -/
def admissionWithRules (clauses : List Clause) (receipts : List Receipt) (rules : List RuleInst)
    (records : List BinderRecord := []) : Admission :=
  let base : Admission := { receipt := accepts clauses receipts, proof := acceptsProof clauses records, rule := acceptsRule clauses rules, narrow := fun _ _ => false }
  Semantic.withNarrowing ops clauses base

end GPProfile
