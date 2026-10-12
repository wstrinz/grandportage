import GPProfile.Families.Core

/-! Family adapters: points over number fields, search, and the try-as-3a pass. -/

namespace GPProfile.Families
open Lean GPProfile

/-! ## Points over `ℚ[a]/(m)` (G3a review §6) -/

/-- A certificate every checker rejects: the adapter's honest "none found". -/
def noCert : Cert := .ideal .rat [] 0 0

/-- A point with coordinates in `ℚ[a]/(m)`: geometric nonemptiness of the source `(a; {m})` by a
`proper` receipt, carried to the target by R3 along the coordinates. The adapter proposes the
obligation certificates by univariate division (equations) and the extended Euclidean algorithm
(guards); where none exists it proposes `noCert`, so every refusal is a checker's. -/
def extensionPoint (sym : String) (m : Sparse) (vars : List String) (eqs guards : List Sparse)
    (phi : List Sparse) (kind : Kind) (staleVerifier : Option String := none) : Except String Plan := do
  let mu := Uni.ofSparse m
  if mu.length < 2 then throw "the field polynomial must be nonconstant"
  let n := vars.length
  let v₀ := Uni.eval mu 0
  let b ← need ((List.range mu.length).find? fun i => Uni.eval mu ((i + 1 : Nat) : Rat) != v₀)
    "the field polynomial is constant on the sample points"
  let eqCert (e : Sparse) : Cert := match compose 1 phi n e with
    | some ce =>
      let (q, r) := Uni.divMod (Uni.ofSparse ce) mu
      if r.isEmpty then .ideal .rat [Uni.toSparse q] 1 0 else noCert
    | none => noCert
  let guardCert (g : Sparse) : Cert := match compose 1 phi n g with
    | some cg =>
      let (d, s, t) := Uni.xgcd mu (Uni.ofSparse cg)
      match d with
      | [c] => .ideal .rat [Uni.toSparse (Uni.scale c⁻¹ s), Uni.toSparse (Uni.scale c⁻¹ t)] 0 0
      | _ => noCert
    | none => noCert
  let source : Stmt := ⟨[sym], [m], [], .notInIdeal (oneP 1)⟩
  let cert : Cert := .proper .rat [0] [((b + 1 : Nat) : Rat)]
  -- A receipt issued under another verifier is bound to that verifier: custody makes it stale.
  let receipt : Support := match staleVerifier with
    | some v => .receipt cert (some (source, [s!"verifier:{v}"]))
    | none => .receipt cert
  let items := [mkItem 1 source .char0Only receipt,
    mkItem 2 ⟨vars, eqs, guards, kind⟩ .char0Only (.rule (.map phi (eqs.map eqCert) (guards.map guardCert)) [1])]
  pure { items, requested := if staleVerifier.isSome then [1, 2] else [2] }

/-- A coordinate in `ℚ[a]/(m)`: a polynomial in the symbol, or a quotient whose denominator must be
invertible modulo `m` (otherwise the map is undefined, an elaboration refusal). -/
def coordPoly (sym : String) (m : Sparse) (j : Json) : Except String Sparse := do
  match obj? j "numerator", obj? j "denominator" with
  | some nj, some dj =>
    let num ← P [sym] (← text nj)
    let den ← P [sym] (← text dj)
    let mu := Uni.ofSparse m
    match Uni.xgcd mu (Uni.ofSparse den) with
    | ([c], _, t) => pure (Uni.toSparse (Uni.divMod (Uni.mul (Uni.ofSparse num) (Uni.scale c⁻¹ t)) mu).2)
    | _ => throw "undefined map: a coordinate's denominator is not invertible modulo the field polynomial"
  | _, _ => P [sym] (← text j)

/-- The single symbol of a field polynomial. -/
def fieldSymbol (mText : String) : Except String String :=
  match identifiers mText with
  | [s] => pure s
  | _ => throw "the field polynomial must have exactly one symbol"

/-- Receipt currency of a point over `ℚ[a]/(m)` under a proposed change: new equations or open
conditions, a base-field point universe (NONEMPTY, which this witness cannot give), or forged
coordinates. With no change proposed there is nothing to check, and the case decodes to nothing. -/
def extensionWitnessFamily (inputs : Json) : Except String Plan := do
  let vars ← strs inputs "variables"
  let mText ← need (str? inputs "field_polynomial") "no field polynomial"
  let sym ← fieldSymbol mText
  let m ← P [sym] mText
  let coord ← need (obj? inputs "coordinate") "no coordinate"
  let change := match (obj? inputs "proposed_change").getD .null with
    | .null => Json.mkObj []
    | c => c
  -- A list replaces the coordinates; an object replaces equations, open conditions or universe.
  let coords ← match change with
    | .arr cs => pure cs.toList
    | _ => pure [coord]
  let pick (key fallback : String) : Except String (List String) :=
    if has change key then strs change key else strs inputs fallback
  let gens ← pick "generators" "generators"
  let opens ← pick "open_conditions" "guards"
  let pointUniverse := (str? change "point_universe").getD ((str? inputs "point_universe").getD "")
  let kind := if pointUniverse == "BASE" then Kind.nonempty else .notInIdeal (oneP vars.length)
  extensionPoint sym m vars (← gens.mapM (P vars)) (← opens.mapM (P vars))
    (← coords.mapM (coordPoly sym m)) kind (str? change "verifier_version")

/-- A displayed point over a simple extension `ℚ[s]/(m)` for a system with nonzero guards. -/
def extensionPointFamily (inputs : Json) : Except String Plan := do
  let vars ← strs inputs "variables"
  let wf ← need (obj? inputs "witness_field") "no witness field"
  let sym ← need (str? wf "symbol") "no symbol"
  let mText ← need (str? wf "minimal_polynomial") "no minimal polynomial"
  if (← fieldSymbol mText) != sym then throw "the minimal polynomial is not in the field symbol"
  let m ← P [sym] mText
  let pt ← need (obj? inputs "point") "no point"
  let phi ← vars.mapM fun v => do coordPoly sym m (← need (obj? pt v) s!"point lacks {v}")
  extensionPoint sym m vars (← (← strs inputs "equations").mapM (P vars))
    (← (← strs inputs "nonzero_guards").mapM (P vars)) phi (.notInIdeal (oneP vars.length))

/-- A bounded saturation search (G3a review §7): the attempted claim, that the built generator lies
outside the saturation of the source by the variables of the monomial quotient, is filed with the
search as typed non-evidence. Nothing admits it, so the refusal is "no certificate". -/
def searchFamily (inputs : Json) : Except String Plan := do
  let src ← strs inputs "source_generators"
  let built ← strs inputs "built_generators"
  let vars := (src ++ built).flatMap identifiers |>.eraseDups
  let srcP ← src.mapM (P vars)
  let builtP ← built.mapM (P vars)
  let bound := (← nats inputs "searched_exponents").length
  match srcP, builtP with
  | [[(es, _)]], [[(eb, cb)]] =>
    if es.length != eb.length || (es.zip eb).any fun (a, c) => a < c then
      throw "the built generator does not divide the source generator"
    -- Saturating by a monomial is localizing at its variables.
    let g : Sparse := [((es.zip eb).map fun (a, c) => if a > c then 1 else 0, 1)]
    pure (single ⟨vars, srcP, [g], .notInIdeal [(eb, cb)]⟩ .char0Only (.searched bound))
  | _, _ => throw "a saturation search is decoded only for monomial generators"

/-! ## The try-as-3a pass (G3a review §1) -/

/-- An offered rational point on a system with no guards: NONEMPTY by a C2 receipt. -/
def displayedPointFamily (inputs : Json) : Except String Plan := do
  let vars ← strs inputs "variables"
  let eqs ← (← strs inputs "equations").mapM (P vars)
  let pt ← ratPoint vars (← need (obj? inputs "point") "no point")
  pure (single ⟨vars, eqs, [], .nonempty⟩ .char0Only (.receipt (.point .rat pt)))

/-- The 3a statement of a point universe: BASE is a rational point (NONEMPTY), ALGEBRAIC_CLOSURE
is geometric nonemptiness (NOT_IN_IDEAL(1)). -/
def universeKind (n : Nat) (u : Json) : Except String Kind :=
  match u with
  | .str "BASE" => pure .nonempty
  | .str "ALGEBRAIC_CLOSURE" => pure (.notInIdeal (oneP n))
  | _ => throw "incomplete map: no point universe on one side of the identity substitution"

/-- One system, two point universes, and the identity substitution offered as a point equivalence:
the target universe's claim by R3 along the identity from the source universe's claim. The
direction table decides; a missing universe is an incomplete map. -/
def universesFamily (inputs : Json) : Except String Plan := do
  let vars ← strs inputs "variables"
  let n := vars.length
  let eqs ← (← strs inputs "generators").mapM (canonP vars)
  let sk ← universeKind n (← need (obj? inputs "source_universe") "no source universe")
  let tk ← universeKind n (← need (obj? inputs "target_universe") "no target universe")
  -- Geometric nonemptiness of a single univariate equation has a `proper` receipt.
  let sourceSupport : Support := match sk, vars, eqs with
    | .notInIdeal _, [_], [m] =>
      let mu := Uni.ofSparse m
      match (List.range mu.length).find? fun i => Uni.eval mu ((i + 1 : Nat) : Rat) != Uni.eval mu 0 with
      | some b => .receipt (.proper .rat [0] [((b + 1 : Nat) : Rat)])
      | none => .none
    | _, _, _ => .none
  let identity := (List.range n).map fun i => [((List.range n).map fun j => if i == j then 1 else 0, (1 : Rat))]
  let selfCert (i : Nat) : Cert := .ideal .rat (eqs.mapIdx fun j _ => if i == j then oneP n else []) 1 0
  let items := [mkItem 1 ⟨vars, eqs, [], sk⟩ .char0Only sourceSupport,
    mkItem 2 ⟨vars, eqs, [], tk⟩ .char0Only
      (.rule (.map identity ((List.range eqs.length).map selfCert) []) [1])]
  pure { items, requested := [2] }

/-- A point `(a₁, …)` in a set literal `{(a₁, …)}`. -/
def regionPoint (vars : List String) (region : String) : Except String (List Rat) := do
  if (region.toList.filter (· == '(')).length != 1 then throw "only a single-point region is decoded"
  let body := String.ofList (region.toList.filter fun c => !"{}() ".toList.contains c)
  let coords := body.splitOn ","
  if coords.length != vars.length then throw "region point has the wrong arity"
  coords.mapM fun c => do
    match ← parse [] c with
    | [] => pure (0 : Rat)
    | [([], q)] => pure q
    | _ => throw "region coordinate is not a constant"

/-- A predicate known on a region, offered for the whole system: VANISHES_ON(h) on the region
(the system plus the point's coordinate equations) holds for an affine `h` vanishing there; the
attempt carries it loose-ward by R2, against the direction table. -/
def regionalFamily (inputs : Json) : Except String Plan := do
  let vars ← strs inputs "variables"
  let n := vars.length
  let eqs ← (← strs inputs "equations").mapM (canonP vars)
  let pt ← regionPoint vars (← need (str? inputs "region") "no region")
  let (l, r) ← splitEq (← need (str? inputs "predicate") "no predicate")
  let h ← canonP vars s!"({l})-({r})"
  if h.any (fun (e, _) => e.foldl (· + ·) 0 > 1) then throw "only affine predicates are decoded"
  -- h = Σ cᵢ (xᵢ − aᵢ) when h(a) = 0: cofactor cᵢ at the i-th coordinate equation.
  let coeffOf (i : Nat) : Rat := (h.filter fun (e, _) => e.getD i 0 == 1).foldl (fun s (_, c) => s + c) 0
  let constant := (h.filter fun (e, _) => e.all (· == 0)).foldl (fun s (_, c) => s + c) 0
  let atPoint := constant + (List.range n).foldl (fun s i => s + coeffOf i * pt.getD i 0) 0
  if atPoint != 0 then throw "the predicate does not hold at the region point"
  let coordEqs ← (List.range n).mapM fun i => canonP vars s!"{vars.getD i ""}-({pt.getD i 0})"
  let region : Stmt := ⟨vars, eqs ++ coordEqs, [], .vanishesOn h⟩
  let cofs := eqs.map (fun _ => ([] : Sparse)) ++ (List.range n).map fun i =>
    if coeffOf i == 0 then [] else [(List.replicate n 0, coeffOf i)]
  let items := [mkItem 1 region .char0Only (.receipt (.ideal .rat cofs 1 0)),
    mkItem 2 ⟨vars, eqs, [], .vanishesOn h⟩ .char0Only
      (.rule (.inclusion (region.eqs.map fun _ => noCert) []) [1])]
  pure { items, requested := [2] }

/-- Rewriting a point predicate through a translation: the case's control names the map used. -/
def translationFamily (inputs : Json) : Except String Plan := do
  let ctrl ← need (str? inputs "control") "no control"
  let pred ← need (str? inputs "source_predicate") "no predicate"
  let (l, r) ← splitEq pred
  let p ← P ["x"] s!"({l})-({r})"
  let mapText ← need (if ctrl == "backward_rewrite" then str? inputs "backward" else str? inputs "forward")
    "no map"
  let map ← P ["y"] (if ctrl == "backward_rewrite" then mapText else mapText.replace "x" "y")
  let rewritten ← need (compose 1 [map] 1 p) "composition failed"
  let tp ← need ((obj? inputs "target_point").bind (·.getNat?.toOption)) "no target point"
  pure (single ⟨["y"], [rewritten], [], .nonempty⟩ .char0Only (.receipt (.point .rat [(tp : Rat)])))

/-- A false emptiness claim next to a witness point: the witness supports NONEMPTY only. -/
def attemptFamily (inputs : Json) (case : Json) : Except String Plan := do
  let attempt ← need (str? inputs "attempt") "no attempt"
  let i ← frontend case []
  if attempt == "empty" then
    let items := [mkItem 1 i.stmt i.scope (.receipt i.cert), mkItem 2 { i.stmt with kind := .empty } i.scope .none]
    pure { items, requested := [2] }
  else pure (single i.stmt i.scope (.receipt i.cert))

/-- Ring-element properties refuted by witness points: NOT_IN_IDEAL (a locus point where the
element is nonzero) and NONUNIT (a locus point where it vanishes). Non-zerodivisor claims have no
3a kind and stay expressiveness losses. -/
def elementFamily (case inputs : Json) : Except String Plan := do
  let claim := (str? case "attempted_conclusion").getD ""
  if (claim.splitOn "nonzerodivisor").length > 1 then throw "non-zerodivisor claims have no 3a statement kind"
  let vars ← strs inputs "variables"
  let eqs ← (← strs inputs "generators").mapM (P vars)
  let el ← P vars (← need (str? inputs "element") "no element")
  let ptOf (k : String) : Except String (List Rat) := do ratPoint vars (← need (obj? inputs k) s!"no {k}")
  -- The points certify the stronger NONEMPTY claims; NOT_IN_IDEAL comes by the bridge rule, and
  -- "not a unit" is canonically NOT_IN_IDEAL(1) with the element added as an equation.
  let items := [
    mkItem 1 ⟨vars, eqs, [el], .nonempty⟩ .char0Only (.receipt (.point .rat (← ptOf "nonzero_point"))),
    mkItem 2 ⟨vars, eqs, [], .notInIdeal el⟩ .char0Only (.rule .witness [1]),
    mkItem 3 ⟨vars, eqs ++ [el], [], .nonempty⟩ .char0Only (.receipt (.point .rat (← ptOf "zero_point"))),
    mkItem 4 ⟨vars, eqs ++ [el], [], .notInIdeal (oneP vars.length)⟩ .char0Only (.rule .witness [3])]
  pure { items, requested := [2, 4] }

/-- An object cover. The proposer looks for a branch whose equations and guards occur literally
in the parent's and supplies the canonical inclusion certificates (no search); with no such
branch the cover claim is unsupported. -/
def coverFamily (inputs : Json) : Except String Plan := do
  let parent ← need (obj? inputs "parent") "no parent"
  let vars ← strs parent "variables"
  let n := vars.length
  let eqs ← (← strs parent "equations").mapM (P vars)
  let guards ← (← strs parent "nonzero").mapM (P vars)
  let branches ← match obj? inputs "branches" with
    | some (.arr bs) => bs.toList.mapM fun b => do
        pure ((← (← strs b "equations").mapM (P vars)), (← (← strs b "nonzero").mapM (P vars)))
    | _ => throw "no branches"
  let stmt : Stmt := ⟨vars, eqs, guards, .cover branches⟩
  let zero : Sparse := []
  -- Loose equation `e` equal to parent equation `j`: VANISHES_ON e with cofactor 1 at `j`.
  let eqCert (e : Sparse) : Option IdealCert := do
    let j ← eqs.idxOf? e
    pure ⟨.rat, eqs.mapIdx fun i _ => if i == j then one n else zero, 1, 0⟩
  -- Loose guard `g` equal to parent guard `j`: {eqs, g = 0, guards} is empty, since
  -- ∏ guards = (∏ other guards) · g; cofactor ∏ other guards at the new equation.
  let guardCert (g : Sparse) : Option IdealCert := do
    let j ← guards.idxOf? g
    let others ← (guards.eraseIdx j).foldlM (fun acc h => mulS n acc h) (one n)
    pure ⟨.rat, eqs.map (fun _ => zero) ++ [others], 0, 1⟩
  let found := branches.zipIdx.findSome? fun ((be, bg), i) => do
    let ec ← be.mapM eqCert
    let gc ← bg.mapM guardCert
    pure (Cert.cover (.leaf i ec gc))
  pure (single stmt .char0Only (match found with | some c => .receipt c | none => .none))

end GPProfile.Families
