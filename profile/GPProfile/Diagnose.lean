import GPProfile.Algebra

/-!
Refusal diagnostics for the campaign CLI (3P friction: "the exact-replay message never names what
failed"). Reporting only: `check` alone decides, and nothing here is consulted by admission. Each
function re-computes the failing quantity of one certificate and names it: the equation or guard
at a point, the first residual term of an identity, or the coefficient at a monomial.
-/

namespace GPProfile
open Hex

def diagRat (c : Rat) : String := if c.den == 1 then s!"{c.num}" else s!"{c.num}/{c.den}"

def monoText (vars : List String) (e : List Nat) : String :=
  let parts := (vars.zip e).filterMap fun (v, k) =>
    if k == 0 then none else if k == 1 then some v else some s!"{v}^{k}"
  if parts.isEmpty then "1" else "*".intercalate parts

def termText (vars : List String) (t : List Nat × Rat) : String :=
  s!"{diagRat t.2}*{monoText vars t.1}"

def fieldText : Field → String
  | .rat => "over Q"
  | .prime p => s!"mod {p}"

def pointDiagnosis (s : Stmt) (field : Field) (vs : List Rat) : String :=
  let n := s.vars.length
  if s.kind != .nonempty then "a point certifies NONEMPTY only" else
  if vs.length != n then s!"the point has {vs.length} coordinates for {n} variables" else
  match pointValues n s vs with
  | none => "the statement does not parse at this arity"
  | some (ev, gv) =>
    let zero (c : Rat) := match field with | .rat => c == 0 | .prime p => zeroMod p c
    let unit (c : Rat) := match field with | .rat => c != 0 | .prime p => unitMod p c
    match (ev.zipIdx.find? fun (v, _) => !zero v), (gv.zipIdx.find? fun (v, _) => !unit v) with
    | some (v, i), _ => s!"equation {i} is {diagRat v} at the point, not 0 {fieldText field}"
    | none, some (v, j) => s!"guard {j} is {diagRat v} at the point, which vanishes {fieldText field}"
    | none, none => "the point checks; its reach does not cover the requested scope"

def identityDiagnosis (s : Stmt) (field : Field) (qs : List Sparse) (m k : Nat) (selected : String) : String :=
  let n := s.vars.length
  match idealTarget s m with
  | none => s!"this kind takes no identity with m = {m} (EMPTY uses m = 0, IN_IDEAL m = 1, VANISHES_ON m ≥ 1)"
  | some h =>
    if qs.length != s.eqs.length then s!"{qs.length} cofactors for {s.eqs.length} equations" else
    if m > maxExponent || k > maxExponent then s!"exponents above {maxExponent} are not expanded" else
    if rhsDegree s h m k > maxRhsDegree then s!"the right-hand side's degree exceeds {maxRhsDegree}{selected}" else
    match residual n s qs h m k with
    | none => "a cofactor does not parse at this arity"
    | some r =>
      let terms := (ofHex r)
      match field with
      | .rat =>
        match terms.head? with
        | some t => s!"Σ qᵢ·eqᵢ − h^{m}·(∏ guards{selected})^{k} ≠ 0 over Q: {terms.length} residual terms, e.g. {termText s.vars t}"
        | none => "the identity holds; its reach does not cover the requested scope"
      | .prime p =>
        match terms.find? fun t => t.2.den % p == 0 with
        | some t => s!"a residual coefficient is not {p}-integral ({termText s.vars t}): divide out {p} or certify over Q"
        | none =>
          match terms.find? fun t => !zeroMod p t.2 with
          | some t => s!"Σ qᵢ·eqᵢ − h^{m}·(∏ guards{selected})^{k} is not 0 mod {p}: e.g. {termText s.vars t}"
          | none => "the identity holds mod p; its reach does not cover the requested scope"

def properCoeffDiagnosis (s : Stmt) (field : Field) (mono : List Nat) : String :=
  let n := s.vars.length
  if s.kind != .notInIdeal (oneP n) then "proper_coefficient certifies NOT_IN_IDEAL(1) only" else
  if !s.guards.isEmpty then "proper_coefficient takes a system with no guards" else
  if mono.length != n then s!"the monomial has {mono.length} exponents for {n} variables" else
  if mono.all (· == 0) then "the monomial must be non-constant" else
  match s.eqs with
  | [e] =>
    match toHexQ n e with
    | none => "the equation does not parse at this arity"
    | some E =>
      let c := coeffAt n E mono
      match field with
      | .rat => s!"the coefficient of {monoText s.vars mono} is {diagRat c}" ++
          (if c == 0 then ", so it says nothing about the equation's degree" else "")
      | .prime p => s!"the coefficient of {monoText s.vars mono} is {diagRat c}, which is " ++
          (if unitMod p c then s!"a unit mod {p}" else s!"0 or not a unit mod {p}") ++
          (if c == 0 then "; pick a monomial that occurs in the equation" else "")
  | _ => "proper_coefficient takes a single equation"

/-- What a refused receipt's check found, in words. -/
def diagnose (s : Stmt) : Cert → String
  | .point field vs => pointDiagnosis s field vs
  | .ideal field qs m k => identityDiagnosis s field qs m k ""
  | .idealSel mask field qs m k =>
    let sel := ((mask.zipIdx.filter (·.1)).map (·.2))
    identityDiagnosis (s.selectGuards mask) field qs m k s!" {sel}"
  | .properCoeff field mono => properCoeffDiagnosis s field mono
  | .proper .. => "the two points give the equation equal values (or the system is not a single unguarded equation)"
  | .cover .. => "a split-tree obligation fails"

end GPProfile
