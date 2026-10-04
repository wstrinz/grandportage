import GP50.Narrowing
import GPProfile.Poly

/-!
The 3a algebraic profile, Nullstellensatz regime (post-G2 §3.1–3.3), executable half.
Statements are canonical sparse ASTs; scopes are characteristic sets; checkers replay
certificates with Hex arithmetic and compute reach. The Mathlib soundness theorems live
in the binding package.
-/

namespace GPProfile
open Hex GP50

/-! ## Statements (§3.1) -/

inductive Kind where
  | empty | nonempty
  | inIdeal (h : Sparse)
  | vanishesOn (h : Sparse)
  /-- `h` is not in the ideal of the equations in `K[x][1/∏ guards]`. NOT_IN_IDEAL(1) is geometric
  nonemptiness; "h is not a unit" is NOT_IN_IDEAL(1) with `h` added as an equation (one encoding,
  G3a review §2). -/
  | notInIdeal (h : Sparse)
  /-- Every point of the locus lies in one of the branches (equations, guards). -/
  | cover (branches : List (List Sparse × List Sparse))
  deriving Repr, DecidableEq

structure Stmt where
  vars : List String
  eqs : List Sparse
  guards : List Sparse
  kind : Kind
  deriving Repr, DecidableEq

/-- The constant polynomial 1 in `n` variables. -/
def oneP (n : Nat) : Sparse := [(List.replicate n 0, 1)]

def Kind.target? : Kind → Option Sparse
  | .inIdeal h | .vanishesOn h | .notInIdeal h => some h
  | _ => none

def Kind.branchPolys : Kind → List Sparse
  | .cover bs => bs.flatMap fun b => b.1 ++ b.2
  | _ => []

def Stmt.polys (s : Stmt) : List Sparse :=
  s.eqs ++ s.guards ++ s.kind.target?.toList ++ s.kind.branchPolys

/-- Every polynomial is canonical and has the declared arity. -/
def Stmt.canonical (s : Stmt) : Bool :=
  s.vars.eraseDups.length == s.vars.length &&
    s.polys.all fun p => GPProfile.canonical s.vars.length p == some p

/-- `S_stmt`: primes dividing any coefficient denominator, including the target's. -/
def Stmt.primes (s : Stmt) : List Nat := denominatorPrimes (s.polys.flatMap Sparse.coeffs)

/-! ## Scopes: characteristic sets (§3.2) -/

inductive PrimeSet where
  | finite (primes : List Nat)
  | cofinite (excluded : List Nat)
  deriving Repr, DecidableEq

structure Scope where
  char0 : Bool
  primes : PrimeSet
  deriving Repr, DecidableEq

/-- Exact inclusion of denotations: `char0` plus the selected primes. -/
def Scope.le (a b : Scope) : Bool :=
  (!a.char0 || b.char0) &&
  match a.primes, b.primes with
  | .finite xs, .finite ys => xs.all fun x => !isPrime x || ys.contains x
  | .finite xs, .cofinite e => xs.all fun x => !isPrime x || !e.contains x
  | .cofinite _, .finite _ => false
  | .cofinite ea, .cofinite eb => eb.all fun x => !isPrime x || ea.contains x

/-- Well-formedness (§3.2): the scope's characteristics avoid `S_stmt`. -/
def Scope.avoids (s : Scope) (bad : List Nat) : Bool :=
  match s.primes with
  | .finite ps => ps.all fun p => !isPrime p || !bad.contains p
  | .cofinite e => bad.all fun p => e.contains p

def meetPrimes : PrimeSet → PrimeSet → PrimeSet
  | .finite xs, .finite ys => .finite (xs.filter ys.contains)
  | .finite xs, .cofinite e => .finite (xs.filter fun x => !e.contains x)
  | .cofinite e, .finite ys => .finite (ys.filter fun y => !e.contains y)
  | .cofinite e₁, .cofinite e₂ => .cofinite (union e₁ e₂)

def Scope.only (p : Nat) : Scope := ⟨false, .finite [p]⟩
def Scope.char0Only : Scope := ⟨true, .finite []⟩
def Scope.outside (bad : List Nat) : Scope := ⟨true, .cofinite bad⟩

/-! ## Certificates and checkers (§3.3) -/

inductive Field where
  | rat
  | prime (p : Nat)
  deriving Repr, DecidableEq

/-- A C1/C3 certificate as data: `h^m · (∏ guards)^k = Σ qᵢ·eqᵢ`. -/
structure IdealCert where
  field : Field
  cofactors : List Sparse
  m : Nat
  k : Nat
  deriving Repr, DecidableEq

/-- A split-tree certificate for COVER (G3a review §2): `split h` covers the current subsystem by
`{h = 0}` (equation added) and `{h ≠ 0}` (guard added); a `leaf` puts its subsystem inside one
branch by C4 inclusion; `empty` discharges an empty subsystem by C1. Depth 0 is a single-branch
inclusion, depth 1 the R4 structural split. -/
inductive SplitTree where
  | leaf (branch : Nat) (eqCerts guardCerts : List IdealCert)
  | empty (cert : IdealCert)
  | split (h : Sparse) (zero nonzero : SplitTree)
  deriving Repr, DecidableEq

def SplitTree.size : SplitTree → Nat
  | .leaf .. | .empty _ => 1
  | .split _ a b => a.size + b.size + 1

/-- Split trees beyond this many nodes are refused rather than replayed. -/
def maxTreeSize : Nat := 255

inductive Cert where
  /-- C1/C3: `h^m · (∏ guards)^k = Σ qᵢ·eqᵢ` (C1 has `h = 1`). -/
  | ideal (field : Field) (cofactors : List Sparse) (m k : Nat)
  /-- C2: a point of the locus. -/
  | point (field : Field) (values : List Rat)
  /-- Geometric nonemptiness of `{m = 0}` (G3a review §6(iii)): the single equation takes different
  values at two rational points, so it is non-constant, hence not a unit: `(m)` is proper. -/
  | proper (field : Field) (a b : List Rat)
  /-- COVER: every point of the locus lies in some branch, by a split tree. -/
  | cover (tree : SplitTree)
  deriving Repr, DecidableEq

def IdealCert.toCert (c : IdealCert) : Cert := .ideal c.field c.cofactors c.m c.k

def Cert.field : Cert → Field
  | .ideal f .. | .point f _ | .proper f _ _ => f
  | .cover .. => .rat

def Cert.primes : Cert → List Nat
  | .ideal _ qs .. => denominatorPrimes (qs.flatMap Sparse.coeffs)
  | .point _ vs => denominatorPrimes vs
  | .proper _ a b => denominatorPrimes (a ++ b)
  | .cover .. => []

/-- Exponents beyond this bound are refused rather than expanded. -/
def maxExponent : Nat := 64

/-- Total-degree budget for `h^m · (∏ guards)^k`; larger right-hand sides are refused, not expanded. -/
def maxRhsDegree : Nat := 256

def Sparse.degree (p : Sparse) : Nat := p.foldl (fun d (e, _) => max d (e.foldl (· + ·) 0)) 0

def rhsDegree (s : Stmt) (h : Sparse) (m k : Nat) : Nat :=
  m * h.degree + k * (s.guards.foldl (fun d g => d + g.degree) 0)

/-- The rational HexMvPoly of a sparse polynomial; the binding package states meaning through it. -/
def toHexQ (n : Nat) (p : Sparse) : Option (P n Rat) := toHex n some p

/-- `Σ qᵢ·eqᵢ − h^m·(∏ guards)^k`, computed exactly over ℚ with HexMvPoly arithmetic. -/
def residual (n : Nat) (s : Stmt) (qs : List Sparse) (h : Sparse) (m k : Nat) : Option (P n Rat) :=
  match s.eqs.mapM (toHexQ n), s.guards.mapM (toHexQ n), qs.mapM (toHexQ n),
      toHexQ n h with
  | some eqs, some guards, some qs, some h =>
    if eqs.length == qs.length then
      some ((List.zipWith (· * ·) qs eqs).sum - h ^ m * (if k = 0 then 1 else guards.prod ^ k))
    else none
  | _, _, _, _ => none

/-- A rational that is zero modulo `p`: `p`-integral with numerator divisible by `p`.
Reduction mod `p` is a ring hom on `p`-integral rationals, so an F_p replay is an exact ℚ
replay whose residual vanishes mod `p`; no F_p arithmetic is needed (A3 deviation). -/
def zeroMod (p : Nat) (c : Rat) : Bool := c.den % p != 0 && c.num % p == 0

def unitMod (p : Nat) (c : Rat) : Bool := c.den % p != 0 && c.num % p != 0

/-- The polynomial whose multiple must lie in the ideal, and the exponent `m` it needs. -/
def idealTarget (s : Stmt) (m : Nat) : Option Sparse :=
  match s.kind with
  | .empty => if m == 0 then some [(List.replicate s.vars.length 0, 1)] else none
  | .inIdeal h => if m == 1 then some h else none
  | .vanishesOn h => if 1 ≤ m then some h else none
  | _ => none

def pointFn (values : List Rat) (n : Nat) : Fin n → Rat :=
  fun i => values.getD i.val 0

/-- Equation and guard values at a rational point, by HexMvPoly evaluation. -/
def pointValues (n : Nat) (s : Stmt) (values : List Rat) : Option (List Rat × List Rat) := do
  let eqs ← s.eqs.mapM (toHexQ n)
  let guards ← s.guards.mapM (toHexQ n)
  pure (eqs.map (MvPoly.eval (pointFn values n)), guards.map (MvPoly.eval (pointFn values n)))

/-- The computed reach of a C1/C2/C3 certificate, or `none` when replay fails. -/
def reachBase (s : Stmt) (c : Cert) : Option Scope :=
  let n := s.vars.length
  let bad := union s.primes c.primes
  match c with
  | .ideal field qs m k =>
    if m > maxExponent || k > maxExponent then none else do
    let h ← idealTarget s m
    if rhsDegree s h m k > maxRhsDegree then none else
    let r ← residual n s qs h m k
    match field with
    | .rat => if r == 0 then some (.outside bad) else none
    | .prime p =>
      if !isPrime p || bad.contains p then none
      else if r.termsList.all (fun t => zeroMod p t.2) then some (.only p) else none
  | .point field values =>
    if s.kind != .nonempty || values.length != n then none else do
    let (ev, gv) ← pointValues n s values
    match field with
    | .rat =>
      if ev.all (· == 0) && gv.all (· != 0) then
        -- A guard value whose numerator a prime divides vanishes there (GP-X410).
        some (.outside (gv.foldl (fun acc g => union acc (primeFactors g.num.natAbs)) bad))
      else none
    | .prime p =>
      if !isPrime p || bad.contains p then none
      else if ev.all (zeroMod p) && gv.all (unitMod p) then some (.only p) else none
  | .proper field a b =>
    if s.kind != .notInIdeal (oneP n) || !s.guards.isEmpty || a.length != n || b.length != n then none
    else
      match pointValues n s a, pointValues n s b with
      | some ([va], _), some ([vb], _) =>
        match field with
        | .rat => if va - vb != 0 then some (.outside (union bad (primeFactors (va - vb).num.natAbs)))
          else none
        | .prime p =>
          if !isPrime p || bad.contains p then none
          else if unitMod p (va - vb) then some (.only p) else none
      | _, _ => none
  | .cover .. => none

/-- C4 inclusion `locus_T ⊆ locus_L` as C1/C3 obligations on the tight system. -/
def inclusionObligations (T L : Stmt) (eqCerts guardCerts : List Cert) :
    Option (List (Stmt × Cert)) :=
  if T.vars != L.vars || eqCerts.length != L.eqs.length || guardCerts.length != L.guards.length
  then none
  else some ((L.eqs.zip eqCerts).map (fun (e, c) => (⟨T.vars, T.eqs, T.guards, .vanishesOn e⟩, c)) ++
    (L.guards.zip guardCerts).map (fun (g, c) => (⟨T.vars, T.eqs ++ [g], T.guards, .empty⟩, c)))

/-- The C1/C3 obligations of a split tree for the subsystem `(E, G)`. -/
def treeObligations (v : List String) (bs : List (List Sparse × List Sparse)) :
    List Sparse → List Sparse → SplitTree → Option (List (Stmt × Cert))
  | E, G, .leaf i eqC gC => do
    let b ← bs[i]?
    inclusionObligations ⟨v, E, G, .empty⟩ ⟨v, b.1, b.2, .empty⟩ (eqC.map IdealCert.toCert)
      (gC.map IdealCert.toCert)
  | E, G, .empty c => some [(⟨v, E, G, .empty⟩, c.toCert)]
  | E, G, .split h t₀ t₁ => do
    let a ← treeObligations v bs (E ++ [h]) G t₀
    let b ← treeObligations v bs E (G ++ [h]) t₁
    pure (a ++ b)

/-- The meet of the reaches of C1/C3 obligations. -/
def reachAllBase (obs : List (Stmt × Cert)) : Option (List Scope) :=
  obs.mapM fun o => reachBase o.1 o.2

/-- The computed reach of a certificate for a statement, or `none` when replay fails. -/
def reach (s : Stmt) (c : Cert) : Option Scope :=
  match c with
  -- Points certify NONEMPTY only; NOT_IN_IDEAL comes from NONEMPTY by the bridge rule.
  | .point .. | .proper .. => reachBase s c
  | .cover t =>
    match s.kind with
    | .cover bs => do
      if t.size > maxTreeSize then none else
      let obs ← treeObligations s.vars bs s.eqs s.guards t
      let rs ← reachAllBase obs
      pure (rs.foldl (fun a b => ⟨a.char0 && b.char0, meetPrimes a.primes b.primes⟩) (.outside []))
    | _ => none
  | .ideal .. => reachBase s c

/-! ## Profile operations and receipt admission -/

/-- Whether two scopes share a characteristic (reporting only; cofinite sets always meet). -/
def Scope.overlaps (a b : Scope) : Bool :=
  (a.char0 && b.char0) || match a.primes, b.primes with
    | .finite ps, .finite qs => ps.any qs.contains
    | .finite ps, .cofinite e | .cofinite e, .finite ps => ps.any fun p => !e.contains p
    | .cofinite _, .cofinite _ => true

/-- Kinds that cannot both hold on one system in one characteristic (G3a review §2): EMPTY vs
NONEMPTY; IN_IDEAL(h) vs NOT_IN_IDEAL(h); EMPTY vs NOT_IN_IDEAL(h), since geometric emptiness puts
a power of the guard product in the ideal (Nullstellensatz), hence every `h`. -/
def kindContra : Kind → Kind → Bool
  | .empty, .nonempty => true
  | .empty, .notInIdeal _ => true
  | .inIdeal h, .notInIdeal h' => h == h'
  | _, _ => false

/-- A filed counterexample: NONEMPTY on the system with `h` added as a guard is a point of the locus where `h` does not vanish, refuting VANISHES_ON(h). -/
def witnessContra (a b : Stmt) : Bool :=
  match a.kind, b.kind with
  | .vanishesOn h, .nonempty => b.guards == a.guards ++ [h]
  | _, _ => false

def contra (a b : Stmt) : Bool :=
  a.vars == b.vars && a.eqs == b.eqs &&
    ((a.guards == b.guards && (kindContra a.kind b.kind || kindContra b.kind a.kind)) ||
      witnessContra a b || witnessContra b a)

def ops : Semantic.ProfileOps where
  Stmt := Stmt
  Scope := Scope
  same a b := decide (a = b)
  same_sound := by intro a b h; exact of_decide_eq_true h
  le := Scope.le
  contra := contra

abbrev Clause := Semantic.Clause ops

structure Receipt where
  name : String
  claim : Nat
  version : Nat
  binding : Binding
  cert : Cert
  deriving Repr, DecidableEq

/-- Why a bound receipt does or does not support its clause (diagnostics only). -/
inductive Check where
  | accepted (reach : Scope)
  | notCanonical
  | illFormed (sStmt : List Nat)
  | replayFailed
  | outsideReach (reach : Scope)
  deriving Repr, DecidableEq

def check (stmt : Stmt) (scope : Scope) (cert : Cert) : Check :=
  if !stmt.canonical then .notCanonical
  else if !scope.avoids stmt.primes then .illFormed stmt.primes
  else match reach stmt cert with
    | some r => if scope.le r then .accepted r else .outsideReach r
    | none =>
      -- A prime-field certificate that is not p-integral is refused on reach: report the
      -- reach the same cofactors compute over ℚ (diagnostic only; `ok` stays false).
      match cert with
      | .ideal (.prime p) qs m k =>
        if (union stmt.primes cert.primes).contains p then
          match reach stmt (.ideal .rat qs m k) with
          | some r => .outsideReach r
          | none => .replayFailed
        else .replayFailed
      | _ => .replayFailed

def Check.ok : Check → Bool
  | .accepted _ => true
  | _ => false

def wellFormed (clauses : List Clause) (receipts : List Receipt) : Bool :=
  (clauses.map (·.key)).eraseDups.length == clauses.length &&
    (receipts.map (·.name)).eraseDups.length == receipts.length

def accepts (clauses : List Clause) (receipts : List Receipt) (w : Warrant) (name : String) : Bool :=
  wellFormed clauses receipts &&
    clauses.any fun c => c.key == w.claim && c.version == w.version && decide (c.binding = w.binding) &&
      receipts.any fun r => r.name == name && r.claim == c.key && r.version == c.version &&
        decide (r.binding = c.binding) && (check c.stmt c.scope r.cert).ok

def admission (clauses : List Clause) (receipts : List Receipt) : Admission :=
  Semantic.withNarrowing ops clauses { Admission.refuseAll with receipt := accepts clauses receipts }

end GPProfile
