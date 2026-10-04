import GPProfile.Poly

/-!
Dense univariate arithmetic over ℚ for the untrusted frontend (post-G2 §1.8): division with
remainder and the extended Euclidean algorithm, used to propose certificates for points over
`ℚ[a]/(m)`. Nothing here is trusted; every certificate it proposes is replayed by a checker.
A polynomial is its coefficient list, lowest degree first.
-/

namespace GPProfile.Uni

abbrev U := List Rat

def trim (p : U) : U := (p.reverse.dropWhile (· == 0)).reverse
def add (p q : U) : U := trim ((List.range (max p.length q.length)).map fun i => p.getD i 0 + q.getD i 0)
def scale (c : Rat) (p : U) : U := trim (p.map (c * ·))
def sub (p q : U) : U := add p (scale (-1) q)
def shift (k : Nat) (p : U) : U := List.replicate k 0 ++ p
def mul (p q : U) : U := p.zipIdx.foldl (fun acc (c, i) => add acc (shift i (scale c q))) []
def eval (p : U) (x : Rat) : Rat := p.foldr (fun c acc => c + x * acc) 0

/-- Quotient and remainder by a nonzero `m`. -/
def divMod (p m : U) : U × U :=
  go (p.length + 1) [] (trim p)
where
  go : Nat → U → U → U × U
  | 0, q, r => (q, r)
  | fuel + 1, q, r =>
    let m' := trim m
    if r.isEmpty || m'.isEmpty || r.length < m'.length then (q, r) else
    let t := shift (r.length - m'.length) [r.getLast! / m'.getLast!]
    go fuel (add q t) (trim (sub r (mul t m')))

/-- `(g, s, t)` with `s·a + t·b = g`, a greatest common divisor. -/
def xgcd (a b : U) : U × U × U :=
  go (a.length + b.length + 2) (trim a) [1] [] (trim b) [] [1]
where
  go : Nat → U → U → U → U → U → U → U × U × U
  | 0, r₀, s₀, t₀, _, _, _ => (r₀, s₀, t₀)
  | fuel + 1, r₀, s₀, t₀, r₁, s₁, t₁ =>
    if r₁.isEmpty then (r₀, s₀, t₀) else
    let (q, r₂) := divMod r₀ r₁
    go fuel r₁ s₁ t₁ r₂ (sub s₀ (mul q s₁)) (sub t₀ (mul q t₁))

def ofSparse (p : Sparse) : U := p.foldl (fun acc (e, c) => add acc (shift (e.headD 0) [c])) []

def toSparse (p : U) : Sparse :=
  let terms := (trim p).zipIdx.filterMap fun (c, i) => if c == 0 then none else some ([i], c)
  (canonical 1 terms).getD terms

end GPProfile.Uni
