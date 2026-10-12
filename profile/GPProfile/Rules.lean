import GPProfile.Algebra
import GP50.ResolveProofs
import GPProfile.Index

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

/-- `Semantic.boundClause` with its key-uniqueness check passed in (3P F2: computed once per fold). -/
def boundWith (unique : Bool) (clauses : List Clause) (w : Warrant) : Option Clause :=
  if !unique then none else
    clauses.find? fun c => c.key == w.claim && c.version == w.version && c.binding == w.binding

def keysUnique (clauses : List Clause) : Bool := (clauses.map (·.key)).eraseDups.length == clauses.length

theorem boundWith_eq (clauses : List Clause) (w : Warrant) :
    boundWith (keysUnique clauses) clauses w = Semantic.boundClause ops clauses w := rfl

/-- `acceptsRule` with its two uniqueness checks passed in. -/
def acceptsRuleWith (distinct unique : Bool) (clauses : List Clause) (rules : List RuleInst) (w : Warrant)
    (premises : List Warrant) (name : String) : Bool :=
  distinct &&
  rules.any fun r => r.name == name && r.conclusion == w.claim &&
    r.premises == premises.map (·.claim) &&
    match boundWith unique clauses w, premises.mapM (boundWith unique clauses) with
    | some c, some ps =>
      c.stmt.canonical && ps.all (fun p => c.scope.le p.scope) &&
        c.scope.avoids (union c.stmt.primes (union (ps.flatMap (·.stmt.primes)) r.data.primes)) &&
        match ruleReach c.stmt (ps.map (·.stmt)) r.data with
        | some rr => c.scope.le rr
        | none => false
    | _, _ => false

def namesDistinct (rules : List RuleInst) : Bool := (rules.map (·.name)).eraseDups.length == rules.length

theorem acceptsRule_eq_acceptsRuleWith (clauses : List Clause) (rules : List RuleInst) :
    acceptsRule clauses rules = acceptsRuleWith (namesDistinct rules) (keysUnique clauses) clauses rules := rfl

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

/-! ## Verdict tables (post-G4 Track K)

An admission answers one query per warrant, and each query used to replay its certificate or rule
obligations. The tables below compute every receipt's and every rule's verdict once per admission,
in parallel chunks, against the clause found by its claim key. Claim keys are unique wherever a query
can succeed, so the clause a query matches is that clause, and the tabled admission equals the
original (`admissionWithRules_eq`).
-/

/-- `xs` in consecutive pieces of at most `size + 1` elements. -/
def chunksOf {α : Type} (size : Nat) : List α → List (List α)
  | [] => []
  | x :: xs => (x :: xs.take size) :: chunksOf size (xs.drop size)
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

theorem flatten_chunksOf {α : Type} (size : Nat) : ∀ xs : List α, (chunksOf size xs).flatten = xs
  | [] => by simp [chunksOf]
  | x :: xs => by
    rw [chunksOf, List.flatten_cons, flatten_chunksOf size (xs.drop size)]
    simp
termination_by xs => xs.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- `xs.map f`, computed in parallel tasks over chunks (`parMap_eq`). -/
def parMap {α β : Type} (f : α → β) (xs : List α) : List β :=
  ((chunksOf (xs.length / 16) xs).map fun ch => Task.spawn fun _ => ch.map f).flatMap Task.get

theorem parMap_eq {α β : Type} (f : α → β) (xs : List α) : parMap f xs = xs.map f := by
  unfold parMap
  have h : ∀ (ch : List α), (Task.spawn fun _ => ch.map f).get = ch.map f := fun _ => rfl
  rw [List.flatMap_map]
  simp only [h]
  rw [List.flatMap_def, ← List.map_flatten, flatten_chunksOf]

theorem any_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons]
    rw [h x List.mem_cons_self, ih fun a ha => h a (List.mem_cons_of_mem _ ha)]

theorem find_key {clauses : List Clause} (hnd : (clauses.map (·.key)).Nodup) {c : Clause}
    (hc : c ∈ clauses) {k : Nat} (hk : c.key = k) : clauses.find? (fun x => x.key == k) = some c := by
  induction clauses with
  | nil => simp at hc
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hc with rfl | hc
    · simp [hk]
    · have hx : (x.key == k) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        exact hnd.1 ⟨c, hc, hk.trans e.symm⟩
      rw [List.find?_cons, hx]
      exact ih hnd.2 hc

/-- A receipt's verdict against the clause of its claim. -/
def receiptOk (clauses : List Clause) (r : Receipt) : Bool :=
  match clauses.find? (fun c => c.key == r.claim) with
  | some c => (check c.stmt c.scope r.cert).ok
  | none => false

def acceptsTable (wf : Bool) (clauses : List Clause) (vs : List (Receipt × Bool)) (w : Warrant)
    (name : String) : Bool :=
  wf &&
    clauses.any fun c => c.key == w.claim && c.version == w.version && decide (c.binding = w.binding) &&
      vs.any fun v => v.1.name == name && v.1.claim == c.key && v.1.version == c.version &&
        decide (v.1.binding = c.binding) && v.2

theorem nodup_keys_of_wf {clauses : List Clause} {receipts : List Receipt}
    (h : wellFormed clauses receipts = true) : (clauses.map (·.key)).Nodup := by
  simp only [wellFormed, Bool.and_eq_true, beq_iff_eq] at h
  exact GP50.nodup_of_eraseDups_length_eq _ (by simpa using h.1)

theorem acceptsTable_eq (clauses : List Clause) (receipts : List Receipt) :
    acceptsTable (wellFormed clauses receipts) clauses (receipts.map fun r => (r, receiptOk clauses r)) =
      acceptsWith (wellFormed clauses receipts) clauses receipts := by
  funext w name
  unfold acceptsTable acceptsWith
  cases hwf : wellFormed clauses receipts with
  | false => rfl
  | true =>
    have hnd := nodup_keys_of_wf hwf
    simp only [Bool.true_and]
    apply any_congr_mem
    intro c hc
    congr 1
    rw [List.any_map]
    apply any_congr_mem
    intro r _
    simp only [Function.comp]
    by_cases hr : (r.name == name && r.claim == c.key && r.version == c.version &&
        decide (r.binding = c.binding)) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at hr
      have hok : receiptOk clauses r = (check c.stmt c.scope r.cert).ok := by
        unfold receiptOk
        rw [find_key hnd hc hr.1.1.2.symm]
      simp [hok]
    · simp only [Bool.not_eq_true] at hr
      simp only [Bool.and_eq_false_iff] at hr ⊢
      rcases hr with ((h | h) | h) | h <;> simp [h]

/-- A rule's verdict against the clauses of its conclusion and premises. -/
def ruleOk (clauses : List Clause) (r : RuleInst) : Bool :=
  match clauses.find? (fun c => c.key == r.conclusion),
      r.premises.mapM (fun k => clauses.find? (fun c => c.key == k)) with
  | some c, some ps =>
    c.stmt.canonical && ps.all (fun p => c.scope.le p.scope) &&
      c.scope.avoids (union c.stmt.primes (union (ps.flatMap (·.stmt.primes)) r.data.primes)) &&
      match ruleReach c.stmt (ps.map (·.stmt)) r.data with
      | some rr => c.scope.le rr
      | none => false
  | _, _ => false

def acceptsRuleTable (distinct unique : Bool) (clauses : List Clause) (vs : List (RuleInst × Bool))
    (w : Warrant) (premises : List Warrant) (name : String) : Bool :=
  distinct &&
  vs.any fun v => v.1.name == name && v.1.conclusion == w.claim &&
    v.1.premises == premises.map (·.claim) &&
    match boundWith unique clauses w, premises.mapM (boundWith unique clauses) with
    | some _, some _ => v.2
    | _, _ => false

theorem nodup_keys_of_unique {clauses : List Clause} (h : keysUnique clauses = true) :
    (clauses.map (·.key)).Nodup := by
  simp only [keysUnique, beq_iff_eq] at h
  exact GP50.nodup_of_eraseDups_length_eq _ (by simpa using h)

theorem boundWith_spec {unique : Bool} {clauses : List Clause} {w : Warrant} {c : Clause}
    (h : boundWith unique clauses w = some c) : c ∈ clauses ∧ c.key = w.claim := by
  unfold boundWith at h
  cases unique with
  | false => simp at h
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
    refine ⟨List.mem_of_find?_eq_some h, ?_⟩
    have := List.find?_some h
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.1

theorem mapM_find_keys {clauses : List Clause} (hnd : (clauses.map (·.key)).Nodup) {unique : Bool} :
    ∀ (premises : List Warrant) (ps : List Clause), premises.mapM (boundWith unique clauses) = some ps →
      (premises.map (·.claim)).mapM (fun k => clauses.find? (fun c => c.key == k)) = some ps
  | [], ps, h => by simpa using h
  | p :: rest, ps, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases hp : boundWith unique clauses p with
    | none => simp [hp] at h
    | some c =>
      cases hrest : rest.mapM (boundWith unique clauses) with
      | none => simp [hp, hrest] at h
      | some cs =>
        simp only [hp, hrest, Option.bind_some, Option.some.injEq] at h
        subst h
        obtain ⟨hc, hk⟩ := boundWith_spec hp
        simp only [List.map_cons, List.mapM_cons, Option.bind_eq_bind, Option.pure_def,
          find_key hnd hc hk, mapM_find_keys hnd rest cs hrest, Option.bind_some]

theorem acceptsRuleTable_eq (clauses : List Clause) (rules : List RuleInst) :
    acceptsRuleTable (namesDistinct rules) (keysUnique clauses) clauses
        (rules.map fun r => (r, ruleOk clauses r)) =
      acceptsRuleWith (namesDistinct rules) (keysUnique clauses) clauses rules := by
  funext w premises name
  unfold acceptsRuleTable acceptsRuleWith
  congr 1
  rw [List.any_map]
  apply any_congr_mem
  intro r _
  simp only [Function.comp]
  by_cases hr : (r.name == name && r.conclusion == w.claim && r.premises == premises.map (·.claim)) = true
  · simp only [Bool.and_eq_true, beq_iff_eq] at hr
    obtain ⟨⟨_, hcon⟩, hprem⟩ := hr
    simp only [hcon, hprem, beq_self_eq_true]
    cases hb : boundWith (keysUnique clauses) clauses w with
    | none => rfl
    | some c =>
      cases hm : premises.mapM (boundWith (keysUnique clauses) clauses) with
      | none => rfl
      | some ps =>
        simp only
        have hu : keysUnique clauses = true := by
          unfold boundWith at hb
          cases h : keysUnique clauses <;> simp_all
        have hnd := nodup_keys_of_unique hu
        obtain ⟨hc, hk⟩ := boundWith_spec hb
        unfold ruleOk
        rw [hcon, find_key hnd hc hk, hprem, mapM_find_keys hnd premises ps hm]
  · simp only [Bool.not_eq_true] at hr
    simp only [Bool.and_eq_false_iff] at hr ⊢
    rcases hr with (h | h) | h <;> simp [h]

/-! ## Indexed tables (post-G4 Track K, P4)

The verdict tables still scanned every clause, receipt and rule per warrant. These twins read them through key indexes built once per admission; each is proved equal to its scan. -/

section
open GPProfile.Index

/-- `receiptOk` with the clause found through a key index (`receiptOkIx_eq`). -/
def receiptOkIx (byKey : Std.HashMap Nat (List Clause)) (r : Receipt) : Bool :=
  match (byKey.getD r.claim []).find? (fun c => c.key == r.claim) with
  | some c => (check c.stmt c.scope r.cert).ok
  | none => false

theorem receiptOkIx_eq (clauses : List Clause) :
    receiptOkIx (bucket (·.key) clauses) = receiptOk clauses := by
  funext r
  unfold receiptOkIx receiptOk
  rw [find?_bucket _ _ _ _ (fun x h => by simpa using h)]

/-- `acceptsTable` reading clauses by claim and verdicts by receipt name (`acceptsTableIx_eq`). -/
def acceptsTableIx (wf : Bool) (byKey : Std.HashMap Nat (List Clause))
    (byName : Std.HashMap String (List (Receipt × Bool))) (w : Warrant) (name : String) : Bool :=
  wf &&
    (byKey.getD w.claim []).any fun c => c.key == w.claim && c.version == w.version &&
      decide (c.binding = w.binding) &&
      (byName.getD name []).any fun v => v.1.name == name && v.1.claim == c.key && v.1.version == c.version &&
        decide (v.1.binding = c.binding) && v.2

theorem acceptsTableIx_eq (wf : Bool) (clauses : List Clause) (vs : List (Receipt × Bool)) :
    acceptsTableIx wf (bucket (·.key) clauses) (bucket (·.1.name) vs) = acceptsTable wf clauses vs := by
  funext w name
  unfold acceptsTableIx acceptsTable
  congr 1
  rw [any_bucket _ _ _ _ (fun x h => by simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.1)]
  apply any_congr_mem
  intro c _
  congr 1
  exact any_bucket _ _ _ _ (fun x h => by simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.1.1)

/-- `boundWith` through the key index (`boundWithIx_eq`). -/
def boundWithIx (unique : Bool) (byKey : Std.HashMap Nat (List Clause)) (w : Warrant) : Option Clause :=
  if !unique then none else
    (byKey.getD w.claim []).find? fun c => c.key == w.claim && c.version == w.version && c.binding == w.binding

theorem boundWithIx_eq (unique : Bool) (clauses : List Clause) :
    boundWithIx unique (bucket (·.key) clauses) = boundWith unique clauses := by
  funext w
  unfold boundWithIx boundWith
  rw [find?_bucket _ _ _ _ (fun x h => by simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1)]

/-- `ruleOk` with clauses found through the key index (`ruleOkIx_eq`). -/
def ruleOkIx (byKey : Std.HashMap Nat (List Clause)) (r : RuleInst) : Bool :=
  match (byKey.getD r.conclusion []).find? (fun c => c.key == r.conclusion),
      r.premises.mapM (fun k => (byKey.getD k []).find? (fun c => c.key == k)) with
  | some c, some ps =>
    c.stmt.canonical && ps.all (fun p => c.scope.le p.scope) &&
      c.scope.avoids (union c.stmt.primes (union (ps.flatMap (·.stmt.primes)) r.data.primes)) &&
      match ruleReach c.stmt (ps.map (·.stmt)) r.data with
      | some rr => c.scope.le rr
      | none => false
  | _, _ => false

theorem ruleOkIx_eq (clauses : List Clause) : ruleOkIx (bucket (·.key) clauses) = ruleOk clauses := by
  have hk : ∀ k, ((bucket (·.key) clauses).getD k []).find? (fun c => c.key == k) =
      clauses.find? (fun c => c.key == k) := fun k =>
    find?_bucket _ _ _ _ (fun x h => by simpa using h)
  funext r
  unfold ruleOkIx ruleOk
  simp only [hk]

/-- `acceptsRuleTable` reading verdicts by rule name and clauses by claim (`acceptsRuleTableIx_eq`). -/
def acceptsRuleTableIx (distinct unique : Bool) (byKey : Std.HashMap Nat (List Clause))
    (byName : Std.HashMap String (List (RuleInst × Bool))) (w : Warrant) (premises : List Warrant)
    (name : String) : Bool :=
  distinct &&
  (byName.getD name []).any fun v => v.1.name == name && v.1.conclusion == w.claim &&
    v.1.premises == premises.map (·.claim) &&
    match boundWithIx unique byKey w, premises.mapM (boundWithIx unique byKey) with
    | some _, some _ => v.2
    | _, _ => false

theorem acceptsRuleTableIx_eq (distinct unique : Bool) (clauses : List Clause) (vs : List (RuleInst × Bool)) :
    acceptsRuleTableIx distinct unique (bucket (·.key) clauses) (bucket (·.1.name) vs) =
      acceptsRuleTable distinct unique clauses vs := by
  funext w premises name
  unfold acceptsRuleTableIx acceptsRuleTable
  rw [boundWithIx_eq]
  congr 1
  exact any_bucket _ _ _ _ (fun x h => by simp only [Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.1)

end

/-- Receipts, rules, bound theorems and narrowing together. -/
def admissionWithRules (clauses : List Clause) (receipts : List Receipt) (rules : List RuleInst)
    (records : List BinderRecord := []) : Admission :=
  -- Each uniqueness check once per fold, not once per warrant (3P F2); `admissionWithRules_eq`.
  -- Uniqueness checks with a hash set, and the tables read through key indexes (P4); both are
  -- `admissionWithRules_eq`.
  let wf := Index.nodupB (clauses.map (·.key)) && Index.nodupB (receipts.map (·.name))
  let distinct := Index.nodupB (rules.map (·.name))
  let unique := Index.nodupB (clauses.map (·.key))
  let byKey := Index.bucket (·.key) clauses
  -- Every verdict once per admission, in parallel (post-G4 Track K); `admissionWithRules_eq`.
  let receiptVs := parMap (fun r => (r, receiptOkIx byKey r)) receipts
  let ruleVs := parMap (fun r => (r, ruleOkIx byKey r)) rules
  let base : Admission :=
    { receipt := acceptsTableIx wf byKey (Index.bucket (·.1.name) receiptVs), proof := acceptsProof clauses records,
      rule := acceptsRuleTableIx distinct unique byKey (Index.bucket (·.1.name) ruleVs),
      narrow := fun _ _ => false }
  Semantic.withNarrowing ops clauses base

theorem admissionWithRules_eq (clauses : List Clause) (receipts : List Receipt) (rules : List RuleInst)
    (records : List BinderRecord) :
    admissionWithRules clauses receipts rules records =
      Semantic.withNarrowing ops clauses
        { receipt := accepts clauses receipts, proof := acceptsProof clauses records,
          rule := acceptsRule clauses rules, narrow := fun _ _ => false } := by
  have hwf : (Index.nodupB (clauses.map (·.key)) && Index.nodupB (receipts.map (·.name))) =
      wellFormed clauses receipts := by simp only [wellFormed, Index.nodupB_eq, List.length_map]
  have hu : Index.nodupB (clauses.map (·.key)) = keysUnique clauses := by simp only [keysUnique, Index.nodupB_eq, List.length_map]
  have hd : Index.nodupB (rules.map (·.name)) = namesDistinct rules := by
    simp only [namesDistinct, Index.nodupB_eq, List.length_map]
  unfold admissionWithRules
  simp only [hwf]
  simp only [hu, hd, receiptOkIx_eq, ruleOkIx_eq, acceptsTableIx_eq, acceptsRuleTableIx_eq, parMap_eq,
    acceptsTable_eq, acceptsRuleTable_eq, accepts_eq_acceptsWith, acceptsRule_eq_acceptsRuleWith]

end GPProfile
