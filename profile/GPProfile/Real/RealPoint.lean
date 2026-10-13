import GPProfile.Poly
import GPProfile.Real.RAlg

/-!
Point replay for a real system (equations, nonzero guards, sign conditions) at a real
algebraic point in field form: one selected root `θ = (m, lo, hi)` and every coordinate a
rational polynomial in `θ`. Each obligation `f` becomes the univariate `f(p₁(θ), …, pₙ(θ))`,
reduced exactly modulo the square-free part `s` of `m`, and its sign is certified against one
shared anchor (`RAlg.certify`) and replayed independently (`RAlg.replayAll`). Every sign is
exact; an undecided sign refuses.
-/

namespace GPProfile.Real
open Hex RAlg

/-- A real system: `signs` pairs a polynomial with its required sign `-1`, `0` or `1`. -/
structure RealSys where
  vars : List String
  eqs : List Sparse
  guards : List Sparse
  signs : List (Sparse × Int)

/-- A field-form point: `θ` is the root of `m` selected by `[lo, hi]`; coordinate `i` is
`coords[i](θ)`. Polynomials are coefficient lists, lowest degree first. -/
structure RealWitness where
  m : List Rat
  lo : Rat
  hi : Rat
  coords : List (List Rat)

/-- What an obligation requires of its certified sign. -/
inductive Req where
  | zero
  | nonzero
  | sign (σ : Int)

def Req.ok : Req → Int → Bool
  | .zero, σ => σ == 0
  | .nonzero, σ => σ != 0
  | .sign τ, σ => σ == τ

def RealSys.obligations (s : RealSys) : List (Sparse × Req) :=
  s.eqs.map (·, .zero) ++ s.guards.map (·, .nonzero) ++ s.signs.map fun (p, σ) => (p, .sign σ)

def signWord (σ : Int) : String :=
  if σ > 0 then "positive" else if σ < 0 then "negative" else "zero"

/-- Obligation `i` in the system file's own terms: `equations[i]`, `nonzero[j]` or `signs[k]`. -/
def RealSys.obligationName (s : RealSys) (i : Nat) : String :=
  let e := s.eqs.length
  let g := s.guards.length
  if i < e then s!"equations[{i}]" else if i < e + g then s!"nonzero[{i - e}]" else s!"signs[{i - e - g}]"

/-- Why a certified sign fails its obligation, for the refusal message. -/
def failureText (s : RealSys) (i : Nat) (r : Req) (σ : Int) : String :=
  let need := match r with
    | .zero => "zero" | .nonzero => "nonzero" | .sign τ => signWord τ
  s!"{s.obligationName i} is {signWord σ} at the point; it must be {need}"

/-- Every exponent vector has the system's arity. -/
def sparseArity (n : Nat) (p : Sparse) : Bool := p.all fun t => t.1.length == n

/-! ## Evaluation in `ℚ[θ]/(s)` -/

def powMod (b s : D) : Nat → D
  | 0 => 1
  | k + 1 => (powMod b s k * b) % s

/-- `∏_{i < k} coords[i]^e[i]` modulo `s`. -/
def monoAt (cs : List D) (s : D) (e : List Nat) : Nat → D
  | 0 => 1
  | i + 1 => (monoAt cs s e i * powMod (cs.getD i 0) s (e.getD i 0)) % s

/-- `f(cs₁, …, csₙ)` modulo `s`. -/
def fieldEval (n : Nat) (cs : List D) (s : D) (f : Sparse) : D :=
  (f.foldl (fun acc t => acc + C t.2 * monoAt cs s t.1 n) 0) % s

/-! ## Search and replay -/

/-- Untrusted: admit the selection, reduce every obligation and certify its sign. -/
def pointCertify (sys : RealSys) (w : RealWitness) :
    Except String (D × Anchor × List (Int × SignWhy)) := do
  let n := sys.vars.length
  unless w.coords.length == n do throw "arity mismatch: one coordinate per variable"
  unless sys.obligations.all (sparseArity n ·.1) do throw "polynomial arity mismatch"
  let sel ← isolate (ofU w.m) w.lo w.hi
  let gs := sys.obligations.map fun o => fieldEval n (w.coords.map ofU) sel.s o.1
  match certify sel gs with
  | none => throw "sign refinement did not converge"
  | some (a, ws) =>
    match ((sys.obligations.zip ws).zipIdx).find? (fun ((o, w), _) => !o.2.ok w.1) with
    | some ((o, w), i) => throw (failureText sys i o.2 w.1)
    | none => pure (sel.s, a, ws)

/-- Trusted replay of a point certificate (what `pointCheck_sound` is about). -/
def pointReplay (sys : RealSys) (w : RealWitness) (s : D) (a : Anchor)
    (ws : List (Int × SignWhy)) : Bool :=
  let n := sys.vars.length
  let obs := sys.obligations
  w.coords.length == n && obs.all (sparseArity n ·.1) && obs.length == ws.length &&
    (obs.zip ws).all (fun (o, w) => o.2.ok w.1) &&
    replayAll (ofU w.m) s w.lo w.hi a (obs.map fun o => fieldEval n (w.coords.map ofU) s o.1) ws

/-- Search, then independent replay. -/
def pointExplain (sys : RealSys) (w : RealWitness) : Except String Unit := do
  let (s, a, ws) ← pointCertify sys w
  unless pointReplay sys w s a ws do throw "point certificate failed replay"

def pointCheck (sys : RealSys) (w : RealWitness) : Bool :=
  match pointCertify sys w with
  | .ok (s, a, ws) => pointReplay sys w s a ws
  | .error _ => false

end GPProfile.Real
