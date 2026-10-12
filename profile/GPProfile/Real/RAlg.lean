import HexPoly

/-!
Selected real roots of univariate rational polynomials (3b, "ℝ first"; port of the scratch
prototype `proto-ralg`). Polynomials are `Hex.DensePoly Rat`.

A selection `(m, lo, hi)` with `lo < hi` denotes the unique real root of `m` in the CLOSED
interval `[lo, hi]` (X353/X405 select endpoint roots; X404 checks `lo < hi` first). Isolation
counts roots with Descartes' rule on a bisection partition (count 1 is accepted only with an
explicit sign change) on the square-free part `s`, admitted by `s ∣ m ∧ m ∣ s^k` (gcd is
never trusted).

Trusted path (`replayAll`, what the binding proves sound over ℝ). It does not use isolation
or uniqueness: one shared `Anchor` fixes a root `θ` of `s`, and every sign certificate speaks
about that same `θ`:
  * `.exact r`: `s(r) = 0`; signs are evaluated at `r`;
  * `.bracket t c d`: `t ∣ s`, `t(c)·t(d) < 0`, so `t` (hence `s`) has a root `θ ∈ (c, d)`;
    a sign is `0` when `t ∣ g`, or `sign g(c)` when `g(c) ≠ 0` and the Möbius transform of `g`
    on `(c, d)` has all coefficients of one sign (Descartes count 0: no root of `g` there).
The searches (`isolate`, `certify`) are untrusted; fuel exhaustion refuses.
-/

namespace GPProfile.Real.RAlg
open Hex

abbrev D := DensePoly Rat

def sgn (x : Rat) : Int := if 0 < x then 1 else if x < 0 then -1 else 0

/-- From a coefficient list, lowest degree first. -/
def ofU (cs : List Rat) : D := DensePoly.ofList cs

def C (c : Rat) : D := DensePoly.C c
def X : D := DensePoly.monomial 1 1

def evalQ (p : D) (x : Rat) : Rat := p.eval x

def coeffs (p : D) : List Rat := (List.range p.size).map p.coeff

/-- `t ∣ p`, by exact division. -/
def dvd (t p : D) : Bool := (p % t).isZero

def powD (p : D) : Nat → D
  | 0 => 1
  | k + 1 => powD p k * p

def monic (p : D) : D := if p.isZero then 0 else C p.leadingCoeff⁻¹ * p

/-- `x - c`. -/
def lin (c : Rat) : D := X - C c

/-- Monic gcd (search only: every use is re-checked by division). -/
def gcdM (a b : D) : D := monic (DensePoly.gcd a b)

/-- Monic square-free part `p / gcd(p, p')`. -/
def sqfree (p : D) : D := monic (p / gcdM p (DensePoly.derivative p))

/-! ## Descartes counting on an interval -/

def mobiusGo (g L O : D) (n : Nat) : Nat → D
  | 0 => 0
  | i + 1 => mobiusGo g L O n i + C (g.coeff i) * powD L i * powD O (n - i)

/-- `(1+t)^n · g((c + d·t)/(1+t))`, `n = size g - 1`. `t ↦ (c+dt)/(1+t)` maps `(0,∞)` onto
`(c,d)`, so positive roots of the transform are the roots of `g` in `(c,d)`. -/
def mobius (g : D) (c d : Rat) : D :=
  mobiusGo g (C c + C d * X) (C 1 + X) (g.size - 1) g.size

/-- Sign variations of a coefficient sequence, zeros ignored. -/
def signVar (cs : List Rat) : Nat :=
  let s := (cs.filter (· != 0)).map sgn
  (s.zip s.tail).countP fun (x, y) => x != y

/-- Descartes' bound on the roots of `p` in `(a,b)`, with multiplicity. -/
def descartes (p : D) (a b : Rat) : Nat := signVar (coeffs (mobius p a b))

/-- Trusted no-root test (Descartes count 0): the transform is nonzero and its coefficients
all have one sign, so `g` has no root in the open interval `(c, d)`. -/
def noRootOn (g : D) (c d : Rat) : Bool :=
  let cs := coeffs (mobius g c d)
  (cs.all (0 ≤ ·) || cs.all (· ≤ 0)) && cs.any (· != 0)

/-! ## Isolation (untrusted search; refusals and completeness only) -/

/-- Distinct roots of a square-free `s` in `(a,b)`, assuming `s(a) ≠ 0 ≠ s(b)`. -/
def openCount (s : D) (a b : Rat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    let v := descartes s a b
    if v == 0 then some 0
    else if v == 1 && sgn (evalQ s a) * sgn (evalQ s b) < 0 then some 1
    else
      let c := (a + b) / 2
      if evalQ s c == 0 then do
        let s' := s / lin c
        let l ← openCount s' a c fuel
        let r ← openCount s' c b fuel
        pure (l + 1 + r)
      else do
        let l ← openCount s a c fuel
        let r ← openCount s c b fuel
        pure (l + r)

def isolationFuel : Nat := 96

/-- Distinct roots of the square-free `s` in the closed interval `[a,b]`, `a < b`. -/
def closedCount (s : D) (a b : Rat) : Option Nat := do
  let za := evalQ s a == 0
  let zb := evalQ s b == 0
  let s1 := if za then s / lin a else s
  let s2 := if zb then s1 / lin b else s1
  let n ← openCount s2 a b isolationFuel
  pure (n + (if za then 1 else 0) + (if zb then 1 else 0))

/-- An admitted selection: `s` is the monic square-free part of the generator. Either the
root is the rational endpoint `exact`, or it is interior and `s(lo)·s(hi) < 0`. -/
structure Sel where
  s : D
  lo : Rat
  hi : Rat
  exact : Option Rat

/-- `s` and `m` have the same roots: `s ∣ m` and `m ∣ s^k` for some `k ≤ size m`. -/
def sameRoots (s m : D) : Bool :=
  dvd s m && go m.size s
where
  go : Nat → D → Bool
  | 0, _ => false
  | fuel + 1, sk => dvd m sk || go fuel (sk * s)

/-- Admit `(m, lo, hi)` as a selected real root, or say why not. -/
def isolate (m : D) (lo hi : Rat) : Except String Sel := do
  unless lo < hi do throw "interval admission: lo < hi required"
  if m.isZero then throw "zero generator: every point is a root"
  let s := sqfree m
  if s.size < 2 then throw "constant generator: no roots"
  unless sameRoots s m do throw "square-free part failed its division check"
  match closedCount s lo hi with
  | none => throw "isolation did not converge"
  | some 1 =>
    let ex := if evalQ s lo == 0 then some lo else if evalQ s hi == 0 then some hi else none
    pure { s, lo, hi, exact := ex }
  | some k => throw s!"interval holds {k} distinct roots, not 1"

/-! ## Anchors and sign certificates (trusted replay) -/

/-- Where the selected root is: shared by every sign certificate of one point. -/
inductive Anchor where
  | exact (r : Rat)
  | bracket (t : D) (c d : Rat)

inductive SignWhy where
  /-- Evaluate at the exact rational root. -/
  | atExact
  /-- The anchor's `t` divides `g`: sign `0`. -/
  | divides
  /-- `g(c) ≠ 0` and `g` has no root in `(c,d)`: sign of `g(c)`. -/
  | noRoot
  deriving Repr, BEq

def anchorOk (s : D) (lo hi : Rat) : Anchor → Bool
  | .exact r => lo ≤ r && r ≤ hi && evalQ s r == 0
  | .bracket t c d =>
    lo ≤ c && c < d && d ≤ hi && dvd t s && sgn (evalQ t c) * sgn (evalQ t d) < 0

def replaySign : Anchor → D → Int → SignWhy → Bool
  | .exact r, g, σ, .atExact => sgn (evalQ g r) == σ
  | .bracket t _ _, g, σ, .divides => σ == 0 && dvd t g
  | .bracket _ c d, g, σ, .noRoot => σ != 0 && sgn (evalQ g c) == σ && noRootOn g c d
  | _, _, _, _ => false

/-- Independent replay: `s ∣ m`, the anchor, and one certified sign per polynomial. -/
def replayAll (m s : D) (lo hi : Rat) (a : Anchor) (gs : List D)
    (ws : List (Int × SignWhy)) : Bool :=
  dvd s m && anchorOk s lo hi a && gs.length == ws.length &&
    (gs.zip ws).all fun (g, w) => replaySign a g w.1 w.2

/-! ## Certificate search (untrusted) -/

def refineFuel : Nat := 256

def decideAt (t : D) (c d : Rat) (g : D) : Option (Int × SignWhy) :=
  if dvd t g then some (0, .divides)
  else if evalQ g c != 0 && noRootOn g c d then some (sgn (evalQ g c), .noRoot)
  else none

def atExact (r : Rat) (gs : List D) : Anchor × List (Int × SignWhy) :=
  (.exact r, gs.map fun g => (sgn (evalQ g r), .atExact))

/-- Bisect `[c,d]` on the sign change of `t` until every `g` is decided. -/
def refine (t : D) (gs : List D) : Rat → Rat → Nat → Option (Anchor × List (Int × SignWhy))
  | _, _, 0 => none
  | c, d, fuel + 1 =>
    match gs.mapM (decideAt t c d) with
    | some ws => some (.bracket t c d, ws)
    | none =>
      let mid := (c + d) / 2
      let tm := evalQ t mid
      if tm == 0 then some (atExact mid gs)
      else if sgn (evalQ t c) * sgn tm < 0 then refine t gs c mid fuel
      else refine t gs mid d fuel

/-- Certify the signs of `gs` at the selected root. `t` is `s` cut down by every `gcd(t, g)`
that still changes sign on `[lo, hi]` (by isolation, exactly those `g` vanishing there). -/
def certify (sel : Sel) (gs : List D) : Option (Anchor × List (Int × SignWhy)) :=
  match sel.exact with
  | some r => some (atExact r gs)
  | none =>
    let t := gs.foldl (fun t g =>
      let h := gcdM t g
      if 2 ≤ h.size && sgn (evalQ h sel.lo) * sgn (evalQ h sel.hi) < 0 then h else t) sel.s
    refine t gs sel.lo sel.hi refineFuel

/-- Certificate for one sign: the anchor, the sign and why. -/
def signAt (g : D) (sel : Sel) : Option (Anchor × Int × SignWhy) :=
  match certify sel [g] with
  | some (a, [w]) => some (a, w)
  | _ => none

/-- A claimed sign of `g` at the root of `m` selected by `[lo, hi]`: search, then replay. -/
def signClaim (m : D) (lo hi : Rat) (g : D) (σ : Int) : Bool :=
  match isolate m lo hi with
  | .error _ => false
  | .ok sel =>
    match signAt g sel with
    | some (a, w) => w.1 == σ && replayAll m sel.s lo hi a [g] [w]
    | none => false

end GPProfile.Real.RAlg
