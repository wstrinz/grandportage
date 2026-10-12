import GPProfile.Real.AlgPoint

/-!
Number-field points (post-G2 §5; checker groups C4 and C5). A statement lives in the signature
`ℚ[t]/(m)` with `m` irreducible over ℚ, optionally extended by a finite algebra
`R = K[Z]/(r)` over `K = ℚ[t]/(m)` (C5's finite quotient witness; `r = []` gives `R = K[Z]`,
which with coordinates constant in `Z` is `K` itself, C4). The statement names a point of `R`:
one coordinate per variable, each an element of `R` written as a list over powers of `Z` of
coefficient lists in `t` (lowest degree first).

**Meaning** (binding, `NumberFieldSound`): `m` is irreducible over ℚ, and in a field `L` of
characteristic 0, for every root `θ` of `m` in `L` and every root `z` of `r(θ, Z)` in `L`, the
point's coordinates at `(θ, z)` make every equation vanish and no guard vanish. Holds quantifies
over the roots of `m` (and of `r`) in `L`; no root is selected.

**Evidence** (`nfCheck`, trusted):
- irreducibility of `m` by the rational-root test (degree 2 or 3, integer coefficients: no
  `±a/b` with `a ∣ m₀`, `b ∣ lc m` is a root; GP-X350);
- every equation reduces to 0 in `R` (exact arithmetic modulo `m`, then modulo `r`);
- every guard `g` has an inverse `u` in `R`: `u · g ≡ 1`; the receipt's reported gcd degree of
  each guard with `r` must be 0, the replayed fact (GP-X320).

Reduction modulo `r` subtracts multiples of `Z^k · r` scaled by the claimed inverse of `r`'s
leading coefficient; any scalar keeps the value at a root of `r`, so that inverse is not trusted
(a wrong one only leaves the result unreduced, and the check refuses). The searches (`nfPropose`)
are untrusted; their output is replayed.
-/

namespace GPProfile.Real
open Hex RAlg

/-- A point of a finite algebra over a number field (see the module doc). -/
structure NFPoint where
  m : List Rat
  r : List (List Rat)
  vars : List String
  eqs : List Sparse
  guards : List Sparse
  coords : List (List (List Rat))
  deriving Repr, DecidableEq

/-- Evidence: the claimed inverse of `r`'s leading coefficient in `K` (search data), one inverse
in `R` per guard, and the receipt's reported gcd degree of each guard with `r`. -/
structure NFCert where
  lcInv : List Rat
  inverses : List (List (List Rat))
  gcdDegrees : List Nat
  deriving Repr

namespace NF

/-- An element of `R`: coefficients in `K` (dense polynomials in `t`), lowest `Z`-degree first. -/
abbrev RE := List D

def addR : RE → RE → RE
  | [], g => g
  | a :: f, [] => a :: f
  | a :: f, b :: g => (a + b) :: addR f g

/-- `c · f`, each coefficient reduced modulo `m`. -/
def smulR (m c : D) : RE → RE
  | [] => []
  | a :: f => (c * a % m) :: smulR m c f

def negR : RE → RE
  | [] => []
  | a :: f => (-a) :: negR f

/-- The product in `K[Z]`, without reduction modulo `r`. -/
def mulRaw (m : D) : RE → RE → RE
  | [], _ => []
  | a :: f, g => addR (smulR m a g) ((0 : D) :: mulRaw m f g)

def shiftN : Nat → RE → RE
  | 0, f => f
  | k + 1, f => (0 : D) :: shiftN k f

/-- Drop zero coefficients at the top. -/
def trimR : RE → RE
  | [] => []
  | a :: f =>
    match trimR f with
    | [] => if a.isZero then [] else [a]
    | b :: t => a :: b :: t

/-- Cancel the top coefficient of `l` against `Z^k · r`, scaled by `top · lcInv`. -/
def redStep (m lcInv : D) (r l : RE) : RE :=
  trimR (addR l (negR (smulR m (l.getLastD 0 * lcInv % m) (shiftN (l.length - r.length) r))))

/-- Reduction modulo `r` (none when `r` has no `Z`). -/
def redR (m lcInv : D) (r : RE) : Nat → RE → RE
  | 0, l => l
  | n + 1, l => if l.length < r.length || r.length < 2 then l else redR m lcInv r n (redStep m lcInv r l)

def mulR (m lcInv : D) (r f g : RE) : RE :=
  redR m lcInv r (f.length + g.length) (trimR (mulRaw m f g))

def powR (m lcInv : D) (r x : RE) : Nat → RE
  | 0 => [1]
  | k + 1 => mulR m lcInv r (powR m lcInv r x k) x

/-- The powers `x^0, …, x^k`. -/
def powTable (m lcInv : D) (r x : RE) : Nat → List RE
  | 0 => [[1]]
  | k + 1 =>
    let t := powTable m lcInv r x k
    t ++ [mulR m lcInv r (t.getLastD [1]) x]

/-- `x^k` from a table when present, else computed. -/
def powAt (m lcInv : D) (r : RE) (tab : List RE) (x : RE) (k : Nat) : RE :=
  match tab[k]? with
  | some p => p
  | none => powR m lcInv r x k

def isZeroR (l : RE) : Bool := l.all (·.isZero)

/-- `∏_{i < k} xs[i]^e[i]` in `R`. -/
def monoR (m lcInv : D) (r : RE) (tabs : List (List RE)) (xs : List RE) (e : List Nat) : Nat → RE
  | 0 => [1]
  | i + 1 =>
    let acc := monoR m lcInv r tabs xs e i
    if e.getD i 0 == 0 then acc else mulR m lcInv r acc (powAt m lcInv r (tabs.getD i []) (xs.getD i []) (e.getD i 0))

/-- A monomial in `n` variables; zero at once when a zero coordinate has a positive exponent. -/
def termR (m lcInv : D) (r : RE) (n : Nat) (tabs : List (List RE)) (xs : List RE) (e : List Nat) : RE :=
  if (List.range n).any (fun i => e.getD i 0 != 0 && isZeroR (xs.getD i [])) then []
  else monoR m lcInv r tabs xs e n

/-- `f(xs)` in `R`. -/
def evalS (m lcInv : D) (r : RE) (n : Nat) (tabs : List (List RE)) (xs : List RE) (f : Sparse) : RE :=
  trimR (f.foldl (fun acc t => addR acc (smulR m (C t.2) (termR m lcInv r n tabs xs t.1))) [])

/-- Power tables up to the largest exponent of each variable in `ps`. -/
def tables (m lcInv : D) (r : RE) (ps : List Sparse) (xs : List RE) : List (List RE) :=
  (List.range xs.length).map fun i =>
    powTable m lcInv r (xs.getD i []) (ps.foldl (fun a p => p.foldl (fun a t => max a (t.1.getD i 0)) a) 0)

/-! ## Irreducibility of `m`: the rational-root test (degree 2 or 3) -/

/-- Coefficient bound for the divisor enumeration. -/
def rrtBound : Nat := 100000

def divisorsN (n : Nat) : List Nat := (List.range (n + 1)).filter fun d => d != 0 && n % d == 0

/-- `m` has degree 2 or 3, integer coefficients, `m(0) ≠ 0`, and no `±a/b` with `a ∣ m(0)`,
`b ∣ lc m` is a root: then `m` has no rational root and is irreducible over ℚ. -/
def rrtOk (m : D) : Bool :=
  (m.size == 3 || m.size == 4) && (List.range m.size).all (fun i => (m.coeff i).den == 1) &&
    m.coeff 0 != 0 && (m.coeff 0).num.natAbs ≤ rrtBound && m.leadingCoeff.num.natAbs ≤ rrtBound &&
    (divisorsN (m.coeff 0).num.natAbs).all fun a => (divisorsN m.leadingCoeff.num.natAbs).all fun b =>
      m.eval ((a : Rat) / (b : Rat)) != 0 && m.eval (-((a : Rat) / (b : Rat))) != 0

end NF

open NF

/-- The data `nfCheck` computes with: `m`, `r`, `lcInv`, coordinates, power tables. -/
structure NFData where
  m : D
  r : NF.RE
  li : D
  xs : List NF.RE
  tabs : List (List NF.RE)

def NFPoint.data (p : NFPoint) (c : NFCert) : NFData :=
  let m := ofU p.m
  let r := p.r.map ofU
  let li := ofU c.lcInv
  let xs := p.coords.map (·.map ofU)
  ⟨m, r, li, xs, tables m li r (p.eqs ++ p.guards) xs⟩

def NFData.eval (d : NFData) (n : Nat) (f : Sparse) : NF.RE := evalS d.m d.li d.r n d.tabs d.xs f

/-- `u · g ≡ 1` in `R`. -/
def NFData.invOk (d : NFData) (n : Nat) (g : Sparse) (u : List (List Rat)) : Bool :=
  isZeroR (addR (mulR d.m d.li d.r (u.map ofU) (d.eval n g)) [C (-1)])

/-- Trusted replay (module doc). -/
def nfCheck (p : NFPoint) (c : NFCert) : Bool :=
  let n := p.vars.length
  let d := p.data c
  rrtOk d.m && p.coords.length == n && p.eqs.all (sparseArity n) && p.guards.all (sparseArity n) &&
    p.guards.length == c.inverses.length && c.gcdDegrees == p.guards.map (fun _ => 0) &&
    p.eqs.all (fun e => isZeroR (d.eval n e)) &&
    (p.guards.zip c.inverses).all fun (g, u) => d.invOk n g u

/-- Why a certificate is refused, for diagnostics (agrees with `nfCheck`). -/
def nfExplain (p : NFPoint) (c : NFCert) : Except String Unit := do
  let n := p.vars.length
  let d := p.data c
  unless rrtOk d.m do
    throw "the rational-root test does not certify m irreducible over ℚ (degree 2–3, integer coefficients, no rational root)"
  unless p.coords.length == n do throw "arity mismatch: one coordinate per variable"
  unless p.eqs.all (sparseArity n) && p.guards.all (sparseArity n) do throw "polynomial arity mismatch"
  unless p.guards.length == c.inverses.length do throw "one inverse per guard required"
  unless c.gcdDegrees == p.guards.map (fun _ => 0) do
    throw "a reported gcd degree with r is not 0: the receipt does not claim a unit"
  unless p.eqs.all (fun e => isZeroR (d.eval n e)) do throw "an equation does not reduce to 0 in R"
  unless (p.guards.zip c.inverses).all (fun (g, u) => d.invOk n g u) do
    throw "a guard has no verified inverse in R (it vanishes at some point)"
  unless nfCheck p c do throw "number-field replay failed"

/-! ## Certificate search (untrusted) -/

namespace NF

/-- An inverse of `a` modulo `m`, by the extended Euclidean algorithm. -/
def invK (m a : D) : Option D := (bezoutFor (coeffs m) (coeffs (a % m))).map fun ab => ofU ab.1 % m

/-- Quotient and remainder in `K[Z]` by `g` (top coefficient invertible). -/
def divModGo (m gInv : D) (g : RE) : Nat → RE → RE → RE × RE
  | 0, q, f => (q, f)
  | k + 1, q, f =>
    let f := trimR f
    if f.length < g.length then (q, f) else
    let c := f.getLastD 0 * gInv % m
    let s := f.length - g.length
    divModGo m gInv g k (addR q (shiftN s [c])) (addR f (negR (smulR m c (shiftN s g))))

/-- `(gcd, s)` with `s · a ≡ gcd` modulo `b`, in `K[Z]`. -/
def xgcdGo (m : D) : Nat → RE → RE → RE → RE → Option (RE × RE)
  | 0, _, _, _, _ => none
  | k + 1, r₀, s₀, r₁, s₁ =>
    let r₁ := trimR r₁
    if r₁.isEmpty then some (trimR r₀, s₀) else do
    let gInv ← invK m (r₁.getLastD 0)
    let (q, rem) := divModGo m gInv r₁ (r₀.length + 1) [] r₀
    xgcdGo m k r₁ s₁ rem (trimR (addR s₀ (negR (mulRaw m q s₁))))

/-- The inverse of `a` in `R = K[Z]/(r)` (in `K` when `r` has no `Z`). -/
def invR (m li : D) (r a : RE) : Option RE :=
  match trimR a with
  | [] => none
  | [c] => (invK m c).map ([·])
  | a =>
    if r.length < 2 then none else do
    let (g, s) ← xgcdGo m (a.length + r.length + 2) a [1] r []
    let [c] := g | none
    let cInv ← invK m c
    pure (redR m li r (s.length + 1) (trimR (smulR m cInv s)))

end NF

/-- Propose a certificate for `p` with the reported gcd degrees (zero by default). A guard with
no inverse gets the zero element, so the replay refuses rather than the search. -/
def nfPropose (p : NFPoint) (gcdDegrees : Option (List Nat) := none) : NFCert :=
  let m := ofU p.m
  let li := match p.r.getLast? with
    | some lc => ((NF.invK m (ofU lc)).getD 0)
    | none => 0
  let d := p.data ⟨coeffs li, [], []⟩
  let n := p.vars.length
  let inv (g : Sparse) : List (List Rat) := ((NF.invR m li d.r (d.eval n g)).getD []).map coeffs
  ⟨coeffs li, p.guards.map inv, gcdDegrees.getD (p.guards.map fun _ => 0)⟩

end GPProfile.Real
