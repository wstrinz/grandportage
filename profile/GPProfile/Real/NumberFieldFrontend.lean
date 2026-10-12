import GPProfile.Families.Base
import GPProfile.Real.Plan
import GPProfile.Real.Fixture

/-!
3b corpus frontend for number-field points (C4). Adapters build profile inputs only: a `nf`
statement (`NFPoint`) at the characteristic-0 `alg` scope and a proposed certificate; the Kernel
fold with `admission3` decides through `nfCheck`.

- **Extension-valued points** (GP-X347–X350): a simple field `ℚ[a]/(m)` named by its minimal
  polynomial, a model over ℚ in the algebraic closure, and the point's coordinate in the field
  (a polynomial in `a`, or a quotient `n/d`, which the frontend writes as `n · d⁻¹ mod m`; the
  inverse is searched, and the statement records the representative the checker replays).
- **Point-universe change** (GP-X48): the closure witness is held as a `nf` claim; the claim after
  the change to `BASE` is 3a's NONEMPTY at characteristic 0 (a rational point, the R7 reading), and
  it is offered the same receipt, still bound to the closure statement: the Kernel's binding check
  refuses it, and no number-field certificate supports an `alg` statement in any case.

And for finite-quotient unit witnesses (C5, GP-X319, X320, X332–X336), built from the pinned
fixture the runner attaches (`attachFixture`):
- **The claim.** Over `K = ℚ[t]/(15t³ + 1)` (the certificates' coefficient field) and the finite
  algebra `R = K[Z]/(r_final)`, the witness point (slice values, `X̄`, `Ȳ`, `Z`, `t`) satisfies the
  sliced equations `A`, `OB`, `Φ`, and `det5` and `Ω₈` are units: at every root of `m` and of
  `r_final` in a field of characteristic 0, the equations vanish and `det5`, `Ω₈` do not. That is
  the historical joint witness check (W3–W5); `Ω₈` keeps the fixture's full polynomial, with the
  slice as coordinates. The receipt reports a gcd degree with `r_final` per guard, which must be 0.
- **Binding.** A claim binds the fixture digest and, for a mutation case, the mutation. The receipt
  replayed on the pinned fixture is bound to the pinned statement and digest only, so a claim about
  a mutated fixture never reuses it (the Kernel's exact binding check).
-/

namespace GPProfile.Real
open Lean GP50 GPProfile GPProfile.Families

/-- A univariate text in `sym` as coefficients, lowest degree first. -/
def uniOf (sym t : String) : Except String (List Rat) := do
  pure (Uni.trim (Uni.ofSparse (← parse [sym] t)))

/-- The coordinate in `ℚ[sym]/(m)`: a polynomial text, or `{numerator, denominator}`. -/
def nfCoordinate (sym : String) (m : List Rat) (j : Json) : Except String (List Rat) := do
  let red (p : List Rat) : List Rat := (Uni.divMod p m).2
  match j with
  | .str t => pure (red (← uniOf sym t))
  | _ =>
    let n ← red <$> uniOf sym (← text ((obj? j "numerator").getD .null))
    let d ← red <$> uniOf sym (← text ((obj? j "denominator").getD .null))
    match bezoutFor m d with
    | some (inv, _) => pure (red (Uni.mul n inv))
    | none => throw "the coordinate's denominator is not invertible modulo m"

def nfItem (key : Nat) (p : NFPoint) : Item3 :=
  { key, stmt := .nf p, scope := .alg Scope.char0Only, support := .receipt (.nf (nfPropose p)) }

/-- GP-X347–X350: `control`, `field` (`base`, `symbol`, `minimal_polynomial`), `model`
(`characteristic` 0, `coefficient_domain` Q, `point_universe` ALGEBRAIC_CLOSURE, `ring_vars`,
`generators`, `open_conditions`) and `coordinate`. -/
def nfPointFamily (inputs : Json) : Except String Plan3 := do
  let field ← need (obj? inputs "field") "missing field"
  let model ← need (obj? inputs "model") "missing model"
  unless str? field "base" == some "Q" && onlyKeys field ["base", "symbol", "minimal_polynomial"] do
    throw "only simple extensions of Q are decoded"
  unless onlyKeys model ["characteristic", "coefficient_domain", "point_universe", "ring_vars", "generators",
      "open_conditions"] && (obj? model "characteristic").any (·.getNat?.toOption == some 0) &&
      str? model "coefficient_domain" == some "Q" && str? model "point_universe" == some "ALGEBRAIC_CLOSURE" do
    throw "only characteristic-0 models over Q in the algebraic closure are decoded"
  let sym ← need (str? field "symbol") "missing field symbol"
  let m ← uniOf sym (← need (str? field "minimal_polynomial") "missing minimal polynomial")
  let vars ← strs model "ring_vars"
  let coordJ ← need (obj? inputs "coordinate") "missing coordinate"
  let coords ← match coordJ with
    | .arr cs => cs.toList.mapM (nfCoordinate sym m)
    | c => do pure [← nfCoordinate sym m c]
  let p : NFPoint := ⟨m, [], vars, ← (← strs model "generators").mapM (parse vars),
    ← (← strs model "open_conditions").mapM (parse vars), coords.map ([·])⟩
  pure { items := [nfItem 1 p], requested := [1] }

/-- GP-X48: `variables`, `generators`, `guards`, `point_universe` ALGEBRAIC_CLOSURE, `field_polynomial`,
`coordinate`, and `proposed_change` to the `BASE` universe. -/
def nfUniverseFamily (inputs : Json) : Except String Plan3 := do
  unless str? inputs "point_universe" == some "ALGEBRAIC_CLOSURE" do throw "the witness must be in the closure"
  let change ← need (obj? inputs "proposed_change") "missing proposed change"
  unless onlyKeys change ["point_universe"] && str? change "point_universe" == some "BASE" do
    throw "only a change to the BASE universe is decoded"
  let fieldT ← need (str? inputs "field_polynomial") "missing field polynomial"
  let [sym] := identifiers fieldT | throw "the field polynomial needs one symbol"
  let m ← uniOf sym fieldT
  let vars ← strs inputs "variables"
  let eqs ← (← strs inputs "generators").mapM (parse vars)
  let guards ← (← strs inputs "guards").mapM (parse vars)
  let coord ← nfCoordinate sym m (← need (obj? inputs "coordinate") "missing coordinate")
  let p : NFPoint := ⟨m, [], vars, eqs, guards, [[coord]]⟩
  let base : Stmt := ⟨vars, eqs, guards, .nonempty⟩
  let changed : Item3 :=
    { key := 2, stmt := .alg base, scope := .alg Scope.char0Only,
      support := .receipt (.nf (nfPropose p)) (some (.nf p)) }
  pure { items := [nfItem 1 p, changed], requested := [2] }

/-! ## Finite-quotient unit witnesses (C5) -/

/-- A rational in the fixture's canonical text: `n` or `n/d`. -/
def ratOfStr (t : String) : Except String Rat :=
  match t.splitOn "/" with
  | [a] => match a.toInt? with
    | some n => pure n
    | none => throw s!"not a rational: '{t}'"
  | [a, b] => match a.toInt?, b.toNat? with
    | some n, some d => if d == 0 then throw "zero denominator" else pure ((n : Rat) / (d : Rat))
    | _, _ => throw s!"not a rational: '{t}'"
  | _ => throw s!"not a rational: '{t}'"

/-- A flattened `K`-polynomial: consecutive triples `a₀ + a₁t + a₂t²`. -/
def triplesOf (j : Json) : Except String (List (List Rat)) := do
  let cs ← (← strList j).mapM ratOfStr
  unless cs.length % 3 == 0 do throw "a flattened K polynomial needs triples"
  pure ((List.range (cs.length / 3)).map fun i => Uni.trim ((cs.drop (3 * i)).take 3))

/-- A fixture sparse polynomial `{symbols, terms}` in the statement's variables. -/
def sparseOf (vars : List String) (j : Json) : Except String Sparse := do
  let syms ← strList (← j.getObjVal? "symbols")
  let idx ← syms.mapM fun s => need (vars.idxOf? s) s!"symbol '{s}' is not a statement variable"
  let terms ← (← j.getObjVal? "terms").getArr?
  let ts ← terms.toList.mapM fun t => do
    let [pw, c] := (← t.getArr?).toList | throw "malformed sparse term"
    let e ← (← pw.getArr?).toList.foldlM (init := List.replicate vars.length 0) fun e q => do
      let [i, k] := (← q.getArr?).toList | throw "malformed sparse power"
      let v ← need (idx[← i.getNat?]?) "power index out of range"
      pure (e.set v (← k.getNat?))
    pure (e, ← ratOfStr (← c.getStr?))
  need (canonical vars.length ts) "noncanonical sparse polynomial"

/-- `"K = QQ[t]/(m)"` or `"Q[t]/(m)"`, with `**` or `^`. -/
def quotientField (t : String) : Except String (List Rat) := do
  let t := (t.replace "**" "^").replace " " ""
  let inner ← match (t.splitOn "[t]/(").drop 1 with
    | [rest] => pure (String.ofList (rest.toList.dropLast))
    | _ => throw s!"not a simple field over Q: '{t}'"
  uniOf "t" inner

/-- The finite witness of the fixture as a `nf` statement (module doc). -/
def finiteWitness (f : Json) : Except String NFPoint := do
  let pc ← f.getObjVal? "pullback_certificate"
  let m ← quotientField (← (← pc.getObjVal? "ring").getObjValAs? String "coefficient_field")
  let w ← pc.getObjVal? "witness"
  unless (w.getObjValAs? String "ring").toOption == some "R = K[Z]/(r_final)" &&
      (strList ((w.getObjVal? "free_on_slice").toOption.getD .null)).toOption ==
        some ["c7_8 (X)", "c8_10 (Y)", "c8_11 (Z)"] do
    throw "only the R = K[Z]/(r_final) witness with free coordinates X, Y, Z is decoded"
  let omega ← (← pc.getObjVal? "Omega8").getObjVal? "sparse"
  let vars ← strList (← omega.getObjVal? "symbols")
  let slice ← w.getObjVal? "slice"
  let xbar ← triplesOf (← w.getObjVal? "Xbar")
  let ybar ← triplesOf (← w.getObjVal? "Ybar")
  let coords ← vars.mapM fun v =>
    if v == "c7_8" then pure xbar else if v == "c8_10" then pure ybar
    else if v == "c8_11" then pure [[], [1]] else if v == "t" then pure [[0, 1]]
    else match slice.getObjValAs? String v with
      | .ok c => do pure [Uni.trim [← ratOfStr c]]
      | .error _ => throw s!"coordinate '{v}' is neither free nor on the slice"
  let eqs ← ["sliced_A", "sliced_OB", "sliced_Phi"].mapM fun k => do sparseOf vars (← w.getObjVal? k)
  let det5 ← sparseOf vars (← w.getObjVal? "sliced_det5")
  pure ⟨m, ← triplesOf (← w.getObjVal? "r_final"), vars, eqs, [det5, ← sparseOf vars omega], coords⟩

/-- GP-X319, X320 (`quotient`, `base_field`, `unit_element`, `claimed_gcd_degree`) and the mutation
controls GP-X332–X336 (`mutation`), against the attached pinned fixture. -/
def finiteUnitFamily (fixture inputs : Json) : Except String Plan3 := do
  let sha ← need (str? inputs "fixture_sha256") "missing fixture digest"
  let pin := s!"fixture:{sha}"
  let p0 ← finiteWitness fixture
  let scope := Scope3.alg Scope.char0Only
  match obj? inputs "mutation" with
  | none =>
    unless onlyKeys inputs ["control", "fixture_sha256", "quotient", "base_field", "unit_element",
        "claimed_gcd_degree"] && str? inputs "quotient" == some "K[Z]/(r_final)" &&
        str? inputs "unit_element" == some "Omega8" do
      throw "only the Omega8 unit claim on K[Z]/(r_final) is decoded"
    unless (← quotientField (← need (str? inputs "base_field") "missing base field")) == p0.m do
      throw "the case's base field is not the fixture's coefficient field"
    let claimed ← need ((obj? inputs "claimed_gcd_degree").bind (·.getNat?.toOption)) "missing gcd degree"
    pure { items := [{ key := 1, stmt := .nf p0, scope, extra := [pin],
                       support := .receipt (.nf (nfPropose p0 (some [0, claimed]))) }],
           requested := [1] }
  | some mu =>
    unless onlyKeys inputs ["control", "fixture_sha256", "mutation"] do throw "unexpected mutation inputs"
    let p1 ← finiteWitness (← applyMutation fixture mu)
    pure { items := [{ key := 1, stmt := .nf p1, scope, extra := [pin, s!"mutation:{mu.compress}"],
                       receiptExtra := some [pin],
                       support := .receipt (.nf (nfPropose p0)) (some (.nf p0)) }],
           requested := [1] }

end GPProfile.Real
