import GPProfile.Frontend
import GPProfile.Plan
import GPProfile.Univariate

/-!
Family adapters of the shared case-to-profile frontend (post-G2 §1.8). Each adapter reads one
input family of the v0.37-derived corpus and builds a `Plan` of profile inputs only. Families
are recognized by their input keys; none is keyed to a case id. A case no family recognizes is
an expressiveness loss.
-/

namespace GPProfile.Families
open Lean GPProfile

/-! ## JSON helpers -/

def obj? (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption
def has (j : Json) (k : String) : Bool := (obj? j k).isSome
def str? (j : Json) (k : String) : Option String := (obj? j k).bind (·.getStr?.toOption)
def strList (j : Json) : Except String (List String) := do (← j.getArr?).toList.mapM Json.getStr?
def strs (j : Json) (k : String) : Except String (List String) :=
  match obj? j k with | some v => strList v | none => pure []
def nats (j : Json) (k : String) : Except String (List Nat) :=
  match obj? j k with | some v => do (← v.getArr?).toList.mapM Json.getNat? | none => pure []
def text (j : Json) : Except String String :=
  match j with
  | .str s => pure s
  | .num n => pure (toString n)
  | _ => throw "expected a polynomial string or number"

/-- The requested scope and replay field from the case's characteristic fields. -/
def scopeField (inputs : Json) : Except String (Scope × Field) := do
  let p ← characteristic inputs []
  pure (if p == 0 then (.char0Only, .rat) else (.only p, .prime p))

def P (vars : List String) (t : String) : Except String Sparse := parse vars t

/-- A parsed polynomial in canonical form. -/
def canonP (vars : List String) (t : String) : Except String Sparse := do
  let p ← P vars t
  pure ((canonical vars.length p).getD p)

def one (n : Nat) : Sparse := oneP n

def mkItem (key : Nat) (stmt : Stmt) (scope : Scope) (support : Support) (extra : List String := []) : Item :=
  { key, stmt, scope, extra, support }

def single (stmt : Stmt) (scope : Scope) (support : Support) : Plan :=
  { items := [{ key := 1, stmt, scope, support }], requested := [1] }

def splitEq (t : String) : Except String (String × String) :=
  match t.splitOn "=" with
  | [l, r] => pure (l, r)
  | [l] => pure (l, "0")
  | _ => throw "identity must have at most one '='"

/-- `p * q` in canonical sparse form. -/
def mulS (n : Nat) (p q : Sparse) : Option Sparse := do
  let a ← toHexQ n p
  let b ← toHexQ n q
  pure (ofHex (a * b))

def subS (n : Nat) (p q : Sparse) : Option Sparse := do
  let a ← toHexQ n p
  let b ← toHexQ n q
  pure (ofHex (a - b))

def powS (n : Nat) (p : Sparse) (k : Nat) : Option Sparse := do
  let a ← toHexQ n p
  pure (ofHex (a ^ k))

def need {α : Type} (o : Option α) (msg : String) : Except String α :=
  match o with | some a => pure a | none => throw msg

/-- A total map on `vars`, as source polynomials in the given order. -/
def totalMap (images : Json) (domain codomain : List String) : Except String (List Sparse) :=
  domain.mapM fun v => match obj? images v with
    | some t => do P codomain (← text t)
    | none => throw s!"incomplete map: no image for {v}"

/-! ## Families -/

/-- Localized membership: `numerator / ∏ guards^d = 0` in the declared localization, certified by
cofactors for `membership_target = numerator · ∏ guardᵢ^{locᵢ}`. The per-guard powers are
brought to a common exponent by scaling the cofactors (exact arithmetic on certificate data). -/
def localized (inputs : Json) : Except String (Stmt × Cert × Scope) := do
  let vars ← strs inputs "variables"
  let n := vars.length
  let gens ← (← strs inputs "generators").mapM (P vars)
  let guards ← (← strs inputs "guards").mapM (P vars)
  let num ← P vars (← need (str? inputs "numerator") "no numerator")
  let qs ← (← strs inputs "cofactors").mapM (P vars)
  let loc ← nats inputs "localization_powers"
  if loc.length != guards.length then throw "localization powers do not match the guards"
  let k := loc.foldl max 0
  let scale ← need ((guards.zip loc).foldlM (fun acc (g, l) => do mulS n acc (← powS n g (k - l)))
    (one n)) "scaling failed"
  let qs' ← need (qs.mapM (mulS n scale)) "scaling failed"
  let (scope, field) ← scopeField inputs
  pure (⟨vars, gens, guards, .inIdeal num⟩, .ideal field qs' 1 k, scope)

/-- Binding inputs of a receipt beyond its statement. -/
def extrasOf (inputs : Json) : List String :=
  [s!"chart:{(str? inputs "chart").getD ""}", s!"cite:{(str? inputs "cite").getD ""}",
    s!"universe:{(str? inputs "point_universe").getD ""}"]

def localizedFamily (inputs : Json) : Except String Plan := do
  let (stmt, cert, scope) ← localized inputs
  let extra := extrasOf inputs
  let base : Item := { key := 1, stmt, scope, extra, support := .receipt cert }
  match obj? inputs "parent_generators", obj? inputs "proposed_change" with
  | some pg, _ =>
    -- Promote local emptiness to a looser parent: an R2 inclusion with no certificate.
    let parent : Stmt := { stmt with eqs := ← (← strList pg).mapM (P stmt.vars), kind := .empty }
    let local' : Stmt := { stmt with kind := .empty }
    -- EMPTY uses the same identity with m = 0 (the target is 1).
    let localCert := match cert with | .ideal f qs _ k => Cert.ideal f qs 0 k | c => c
    let items := [mkItem 1 local' scope (.receipt localCert) extra, mkItem 2 parent scope (.rule (.inclusion [] []) [1])]
    pure { items, requested := [2] }
  | _, some (.obj change) =>
    -- Custody: the receipt stays bound to the original statement and binding inputs.
    let ch := Json.obj change
    let eqs ← match obj? ch "generators" with
      | some v => (← strList v).mapM (P stmt.vars) | none => pure stmt.eqs
    let guards ← match obj? ch "open_conditions" with
      | some v => (← strList v).mapM (P stmt.vars) | none => pure stmt.guards
    let merged := Json.mergeObj inputs ch
    let changed := mkItem 2 { stmt with eqs, guards } scope (.receipt cert (some (stmt, extra))) (extrasOf merged)
    pure { items := [base, changed], requested := [2] }
  | _, _ => pure { items := [base], requested := [1] }

/-- An identity checked against a model's ideal: `left - right` in the ideal of the equations. -/
def modelIdentity (inputs : Json) : Except String Plan := do
  let model ← need (obj? inputs "model") "no model"
  let vars ← strs model "variables"
  let eqs ← (← strs model "equations").mapM (P vars)
  let idn ← need (obj? inputs "identity") "no identity"
  let lhs ← text (← need (obj? idn "left") "no left")
  let rhs ← text (← need (obj? idn "right") "no right")
  let h ← P vars s!"({lhs})-({rhs})"
  let qs ← (← strs inputs "cofactors").mapM (P vars)
  let (scope, field) ← scopeField model
  pure (single ⟨vars, eqs, [], .inIdeal h⟩ scope (.receipt (.ideal field qs 1 0)))

/-- An ambient identity `lhs = rhs`: membership of the difference in the zero ideal. -/
def ambient (vars : List String) (lhs rhs : String) (scope : Scope) (field : Field) : Except String Plan := do
  let h ← P vars s!"({lhs})-({rhs})"
  pure (single ⟨vars, [], [], .inIdeal h⟩ scope (.receipt (.ideal field [] 1 0)))

def ambientFamily (inputs : Json) : Except String Plan := do
  let (scope, field) ← scopeField inputs
  let vars ← strs inputs "variables"
  if let (some l, some r) := (str? inputs "lhs", str? inputs "rhs") then
    return ← ambient vars l r scope field
  if let some pi := obj? inputs "power_identity" then
    let eq ← text (← need (obj? pi "equation") "no equation")
    let sc ← text (← need (obj? pi "scalar") "no scalar")
    let b ← text (← need (obj? pi "base") "no base")
    let e ← need ((obj? pi "exponent").bind (·.getNat?.toOption)) "no exponent"
    return ← ambient vars eq s!"({sc})*({b})^{e}" scope field
  let idn ← need (obj? inputs "identity") "no identity"
  let eq ← text (← need (obj? idn "equation") "no equation")
  let sc ← text (← need (obj? idn "scalar") "no scalar")
  let l ← text (← need (obj? idn "left") "no left")
  let r ← text (← need (obj? idn "right") "no right")
  ambient vars eq s!"({sc})*({l})*({r})" scope field

/-- A proposed result of a simultaneous substitution: GP composes and checks the identity. -/
def substitution (inputs : Json) : Except String Plan := do
  let vars ← strs inputs "variables"
  let images ← need (obj? inputs "images") "no images"
  let phi ← totalMap images vars vars
  let e ← P vars (← need (str? inputs "expression") "no expression")
  let composed ← need (compose vars.length phi vars.length e) "composition failed"
  let proposed ← P vars (← need (str? inputs "proposed") "no proposed result")
  let h ← need (subS vars.length proposed composed) "difference failed"
  pure (single ⟨vars, [], [], .inIdeal h⟩ .char0Only (.receipt (.ideal .rat [] 1 0)))

/-- A ring-isomorphism certificate between quotient rings, as the bundle of its obligations:
pullback memberships in both directions and both inverse laws. Every one must be held. -/
def isoBundle (vS : List String) (eS : List Sparse) (vT : List String) (eT : List Sparse)
    (fwd : List Sparse) (inv : List Sparse) (fwdRows invRows : List (List Sparse)) : Except String Plan := do
  let nS := vS.length
  let nT := vT.length
  -- forward: target variable images in source coordinates; inverse: source images in target.
  let pullT ← need (eT.mapM (compose nS fwd nT)) "forward pullback failed"
  let pullS ← need (eS.mapM (compose nT inv nS)) "inverse pullback failed"
  let backS ← need (inv.mapM (compose nS fwd nT)) "inverse law failed"
  let backT ← need (fwd.mapM (compose nT inv nS)) "inverse law failed"
  let xS := (List.range nS).map fun i => [((List.range nS).map fun j => if i == j then 1 else 0, (1 : Rat))]
  let xT := (List.range nT).map fun i => [((List.range nT).map fun j => if i == j then 1 else 0, (1 : Rat))]
  let lawS ← need ((backS.zip xS).mapM fun (b, x) => subS nS b x) "inverse law failed"
  let lawT ← need ((backT.zip xT).mapM fun (b, x) => subS nT b x) "inverse law failed"
  let mk (vars : List String) (eqs : List Sparse) (h : Sparse) (qs : List Sparse) : Stmt × Cert :=
    (⟨vars, eqs, [], .inIdeal h⟩, .ideal .rat qs 1 0)
  let rows (rs : List (List Sparse)) (i : Nat) (len : Nat) : List Sparse :=
    (rs.getD i []) ++ List.replicate (len - (rs.getD i []).length) []
  let obligations :=
    (pullT.zipIdx.map fun (h, i) => mk vS eS h (rows fwdRows i eS.length)) ++
    (pullS.zipIdx.map fun (h, i) => mk vT eT h (rows invRows i eT.length)) ++
    (lawS.map fun h => mk vS eS h (List.replicate eS.length [])) ++
    (lawT.map fun h => mk vT eT h (List.replicate eT.length []))
  let items := obligations.zipIdx.map fun ((s, c), i) => mkItem (i + 1) s .char0Only (.receipt c)
  pure { items, requested := items.map (·.key) }

def ringMapFamily (inputs : Json) : Except String Plan := do
  if let (some src, some tgt) := (obj? inputs "source", obj? inputs "target") then
    let vS ← strs src "variables"; let vT ← strs tgt "variables"
    let eS ← (← strs src "equations").mapM (P vS)
    let eT ← (← strs tgt "equations").mapM (P vT)
    let fwd ← totalMap (← need (obj? inputs "point_forward") "no forward map") vT vS
    let inv ← totalMap (← need (obj? inputs "point_inverse") "no inverse map") vS vT
    let rowsOf (k : String) (vars : List String) : Except String (List (List Sparse)) := do
      match obj? inputs k with
      | some (.arr rs) => rs.toList.mapM fun r => do (← strList r).mapM (P vars)
      | _ => pure []
    return ← isoBundle vS eS vT eT fwd inv (← rowsOf "target_pullback_rows" vS) (← rowsOf "source_pullback_rows" vT)
  let vars ← strs inputs "variables"
  let eqs ← (← strs inputs "generators").mapM (P vars)
  let fwd ← totalMap (← need (obj? inputs "forward") "no forward map") vars vars
  let inv ← totalMap (← need (obj? inputs "inverse") "no inverse map") vars vars
  let rowsOf (k : String) : Except String (List (List Sparse)) := do
    match obj? inputs k with
    | some (.arr rs) => rs.toList.mapM fun r => do (← strList r).mapM (P vars)
    | _ => pure []
  isoBundle vars eqs vars eqs fwd inv (← rowsOf "forward_cofactors") (← rowsOf "inverse_cofactors")

/-- Transport of an identity between ideals (relaxation, quotient pullback, witnesses). -/
def idealsFamily (inputs : Json) : Except String Plan := do
  let srcT ← strs inputs "source_ideal"
  let tgtT ← strs inputs "target_ideal"
  let texts := srcT ++ tgtT ++ ((str? inputs "identity").toList) ++ ((str? inputs "identity_difference").toList)
  let vars ← match obj? inputs "variables" with
    | some v => strList v
    | none => pure (texts.flatMap identifiers).eraseDups
  let src ← srcT.mapM (P vars)
  let tgt ← tgtT.mapM (P vars)
  if let some pt := obj? inputs "point" then
    let values ← vars.mapM fun v => do
      match ← parse [] (← text (← need (obj? pt v) s!"point lacks {v}")) with
      | [] => pure (0 : Rat)
      | [([], c)] => pure c
      | _ => throw "point coordinate is not a constant"
    return single ⟨vars, tgt, [], .nonempty⟩ .char0Only (.receipt (.point .rat values))
  if let some d := str? inputs "identity_difference" then
    let qs ← (← strs inputs "target_cofactors").mapM (P vars)
    return single ⟨vars, tgt, [], .inIdeal (← P vars d)⟩ .char0Only (.receipt (.ideal .rat qs 1 0))
  let (l, r) ← splitEq (← need (str? inputs "identity") "no identity")
  let h ← P vars s!"({l})-({r})"
  if has inputs "point_containment_proof" then
    -- Only point-level evidence is offered: VANISHES_ON(h) on the source cannot become ideal
    -- membership there (R1 runs the other way). The attempted step is an R1 instance in reverse.
    let items := [mkItem 1 ⟨vars, src, [], .vanishesOn h⟩ .char0Only .none,
      mkItem 2 ⟨vars, src, [], .inIdeal h⟩ .char0Only (.rule .r1 [1])]
    return { items, requested := [2] }
  -- Carry the identity to the target ideal, replayed there with no cofactors.
  pure (single ⟨vars, tgt, [], .inIdeal h⟩ .char0Only (.receipt (.ideal .rat (tgt.map fun _ => []) 1 0)))

/-- An offered point at an exact open model. -/
def pointFamily (inputs : Json) : Except String Plan := do
  let vars ← strs inputs "variables"
  let eqs ← (← strs inputs "equations").mapM (P vars)
  let guards ← (← strs inputs "nonzero_guards").mapM (P vars)
  let pt ← need (obj? inputs "point") "no point"
  let values ← vars.mapM fun v => do
    match ← parse [] (← text (← need (obj? pt v) s!"point lacks {v}")) with
    | [] => pure (0 : Rat)
    | [([], c)] => pure c
    | _ => throw "point coordinate is not a constant"
  let (scope, field) ← scopeField inputs
  pure (single ⟨vars, eqs, guards, .nonempty⟩ scope (.receipt (.point field values)))

/-- Elimination targets: statements over the retained coordinates only (signature check). -/
def eliminationFamily (inputs : Json) : Except String Plan := do
  if let (some tv, some idn) := (obj? inputs "target_variables", str? inputs "identity") then
    let vars ← strList tv
    let (l, r) ← splitEq idn
    let h ← P vars s!"({l})-({r})"
    return single ⟨vars, [], [], .inIdeal h⟩ .char0Only .none
  let built ← strs inputs "built_generators"
  let elim ← strs inputs "eliminated"
  let vars := ((built.flatMap identifiers).eraseDups).filter fun v => !elim.contains v
  let gens ← built.mapM (P vars)
  pure (single ⟨vars, gens, [], .nonempty⟩ .char0Only .none)

/-- Excluding one fiber does not exclude the parent: R4 needs both branches. -/
def fiberFamily (inputs : Json) : Except String Plan := do
  let vars ← strs inputs "variables"
  let parentEqs ← (← strs inputs "parent_equations").mapM (P vars)
  let base ← need (obj? inputs "excluded_base") "no excluded base"
  let fiberEqs ← vars.filterMapM fun v => match obj? base v with
    | some t => do pure (some (← P vars s!"{v}-({← text t})"))
    | none => pure none
  let parent : Stmt := ⟨vars, parentEqs, [], .empty⟩
  let h ← need fiberEqs.head? "empty excluded base"
  let items := [mkItem 1 { parent with eqs := parentEqs ++ [h] } .char0Only .none,
    mkItem 2 parent .char0Only (.rule (.split h) [1])]
  pure { items, requested := [2] }

/-- A rational point given as `{variable: constant}`, in variable order. -/
def ratPoint (vars : List String) (pt : Json) : Except String (List Rat) :=
  vars.mapM fun v => do
    match ← parse [] (← text (← need (obj? pt v) s!"point lacks {v}")) with
    | [] => pure (0 : Rat)
    | [([], c)] => pure c
    | _ => throw "point coordinate is not a constant"

/-- Cancelling a factor that is not proved invertible: VANISHES_ON(x) on `{z·x = 0}`. A supplied
point is filed as the counterexample (NONEMPTY with the conclusion as a guard), so the refusal is
`contra`'s, not mere lack of support (G3a review §4). -/
def cancelFamily (inputs : Json) : Except String Plan := do
  let vars ← strs inputs "variables"
  let prod ← P vars (← need (str? inputs "product") "no product")
  let conc ← P vars (← need (str? inputs "cancelled_conclusion") "no conclusion")
  let claim := mkItem 1 ⟨vars, [prod], [], .vanishesOn conc⟩ .char0Only .none
  match obj? inputs "point" with
  | none => pure { items := [claim], requested := [1] }
  | some pt =>
    let witness := mkItem 2 ⟨vars, [prod], [conc], .nonempty⟩ .char0Only
      (.receipt (.point .rat (← ratPoint vars pt)))
    pure { items := [claim, witness], requested := [1] }

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

/-- A family applies only when every input key is one it reads (or ignores as provenance) and
the fixed fields it requires have the stated values. Anything else is an expressiveness loss:
the frontend never guesses past a key it does not understand. -/
def onlyKeys (inputs : Json) (allowed : List String) : Bool :=
  match inputs with
  -- `meta` is the explicit ignored namespace for provenance notes (G3a review §4).
  | .obj kvs => kvs.toList.all fun (k, _) => k == "meta" || allowed.contains k
  | _ => false

/-- A nested model object: only these keys, and a rational field when one is named. -/
def modelOk (j : Json) : Bool :=
  onlyKeys j ["field", "variables", "equations", "nonzero"] &&
    (str? j "field").all fun f => (fieldChar? f).isSome && f != "R" && f != "RR"

def nestedOk (inputs : Json) (key : String) (allowed : List String) : Bool :=
  (obj? inputs key).all fun j => onlyKeys j allowed

def questionIs (inputs : Json) (qs : List String) : Bool :=
  match str? inputs "question" with
  | some q => qs.contains q
  | none => true

/-- A scalar factor is a constant or a declared unit. -/
def scalarOk (inputs : Json) (scalar : Option String) : Except String Bool := do
  let some sc := scalar | return true
  let units ← strs inputs "declared_units"
  let ids := identifiers sc
  pure (ids.all units.contains)

def legacyKeys : List String :=
  ["variables", "generators", "cofactors", "target", "characteristic", "target_characteristic",
    "guards", "exponent", "point", "reduced_point", "identity", "source_ideal", "cofactor",
    "source_context", "target_context"]

/-! ## The explicit statement surface (instantiation fixtures, G3a review §7)

Claims written as systems, kinds, certificates and rule instances, with nothing inferred. -/

def natField (j : Json) (k : String) : Nat := ((obj? j k).bind (·.getNat?.toOption)).getD 0

def surfaceKind (vars : List String) (c : Json) : Except String Kind := do
  let tgt : Except String Sparse := do canonP vars (← need (str? c "target") "no target")
  match ← need (str? c "kind") "no kind" with
  | "EMPTY" => pure .empty
  | "NONEMPTY" => pure .nonempty
  | "IN_IDEAL" => pure (.inIdeal (← tgt))
  | "VANISHES_ON" => pure (.vanishesOn (← tgt))
  | "NOT_IN_IDEAL" => pure (.notInIdeal (← tgt))
  | k => throw s!"unknown kind {k}"

def surfaceIdealCert (vars : List String) (c : Json) : Except String IdealCert := do
  if !onlyKeys c ["type", "cofactors", "m", "k", "characteristic"] then throw "unknown certificate key"
  let field := match (obj? c "characteristic").bind (·.getNat?.toOption) with
    | some p => Field.prime p
    | none => .rat
  pure ⟨field, ← (← strs c "cofactors").mapM (canonP vars), natField c "m", natField c "k"⟩

def surfaceCerts (vars : List String) (rule : Json) (k : String) : Except String (List Cert) := do
  match obj? rule k with
  | some (.arr cs) => cs.toList.mapM fun c => do pure (← surfaceIdealCert vars c).toCert
  | none => pure []
  | _ => throw s!"{k} must be a list"

def surfaceFamily (inputs : Json) : Except String Plan := do
  let claims ← match obj? inputs "claims" with
    | some (.arr cs) => pure cs.toList
    | _ => throw "no claims"
  let requested ← nats inputs "requested"
  let items ← claims.foldlM (fun (acc : List Item) c => do
    if !onlyKeys c ["key", "variables", "equations", "nonzero", "kind", "target", "characteristic",
        "certificate", "rule", "premises"] then throw "unknown claim key"
    let key ← need ((obj? c "key").bind (·.getNat?.toOption)) "claim without key"
    let vars ← strs c "variables"
    let stmt : Stmt := ⟨vars, ← (← strs c "equations").mapM (canonP vars),
      ← (← strs c "nonzero").mapM (canonP vars), ← surfaceKind vars c⟩
    let scope : Scope := match (obj? c "characteristic").bind (·.getNat?.toOption) with
      | some p => .only p
      | none => .char0Only
    let premises ← nats c "premises"
    let support ← match obj? c "certificate", obj? c "rule" with
      | some cert, none =>
        let ty := (str? cert "type").getD ""
        if ty == "ideal" then pure (Support.receipt (← surfaceIdealCert vars cert).toCert)
        else if ty == "point" then
          pure (.receipt (.point .rat (← ratPoint vars (← need (obj? cert "point") "no point"))))
        else throw "unknown certificate type"
      | none, some rule =>
        let prem ← need (premises.head?.bind fun k => (acc.find? (·.key == k)).map (·.stmt))
          "a rule needs its premises filed first"
        -- Map obligations live on the source: the premise for NONEMPTY / NOT_IN_IDEAL, else the
        -- conclusion.
        let forward := match stmt.kind with | .nonempty | .notInIdeal _ => true | _ => false
        let (srcVars, tgtVars) := if forward then (prem.vars, vars) else (vars, prem.vars)
        let data ← match (str? rule "type").getD "" with
          | "r1" => pure RuleData.r1
          | "bridge" => pure .witness
          | "cover" => pure .byCover
          | "split" => pure (.split (← canonP vars (← need (str? rule "on") "no split polynomial")))
          | "inclusion" =>
            pure (.inclusion (← surfaceCerts vars rule "eq_certificates") (← surfaceCerts vars rule "guard_certificates"))
          | "map" =>
            let m ← need (obj? rule "map") "no map"
            let phi ← tgtVars.mapM fun v => do
              canonP srcVars (← text (← need (obj? m v) s!"incomplete map: no image for {v}"))
            pure (.map phi (← surfaceCerts srcVars rule "eq_certificates") (← surfaceCerts srcVars rule "guard_certificates"))
          | _ => throw "unknown rule type"
        pure (.rule data premises)
      | none, none => pure .none
      | _, _ => throw "a claim has a certificate or a rule, not both"
    pure (acc ++ [mkItem key stmt scope support])) []
  pure { items, requested }

/-- Dispatch on input keys. -/
def plan (case : Json) (params : List (String × Nat)) : Except String Plan := do
  let inputs ← case.getObjVal? "inputs"
  let elabOr (r : Except String Plan) : Except String Plan :=
    match r with
    | .ok p => .ok p
    | .error e =>
      if e.startsWith "undeclared variable" || e.startsWith "incomplete map" ||
          e.startsWith "undefined map" then
        .ok { items := [], requested := [], elaboration := some e }
      else .error e
  let k := onlyKeys inputs
  if has inputs "membership_target" && k ["variables", "generators", "guards", "numerator",
      "denominator_powers", "localization_powers", "membership_target", "cofactors", "coefficient_field",
      "point_universe", "chart", "cite", "proposed_change", "parent_generators", "characteristic"] &&
      (str? inputs "point_universe" |>.all (· == "ALGEBRAIC_CLOSURE")) &&
      ((obj? inputs "proposed_change").all fun c => onlyKeys c ["generators", "open_conditions", "chart", "cite", "point_universe"] || c == .null) then
    return ← localizedFamily inputs
  if has inputs "model" && k ["model", "identity", "cofactors", "local_backend", "historical_identity",
      "raw_artifact", "question"] && questionIs inputs ["exact_identity_current"] &&
      (obj? inputs "model").all modelOk && nestedOk inputs "identity" ["left", "right"] then
    return ← modelIdentity inputs
  if k ["lhs", "rhs", "variables", "characteristic"] && has inputs "lhs" then
    return ← ambientFamily inputs
  if has inputs "power_identity" && k ["variables", "characteristic", "declared_units", "exponent_limit",
      "power_identity", "question"] && questionIs inputs ["check_power_identity"] &&
      nestedOk inputs "power_identity" ["equation", "scalar", "base", "exponent"] &&
      (← scalarOk inputs ((obj? inputs "power_identity").bind (str? · "scalar"))) then
    return ← ambientFamily inputs
  if (obj? inputs "identity").any (fun j => has j "equation") && k ["variables", "characteristic",
      "declared_units", "identity", "parent_equations", "open_guards", "question"] &&
      questionIs inputs ["check_identity"] && has inputs "question" &&
      nestedOk inputs "identity" ["equation", "scalar", "left", "right"] &&
      (← scalarOk inputs ((obj? inputs "identity").bind (str? · "scalar"))) then
    return ← ambientFamily inputs
  if has inputs "images" && k ["variables", "expression", "images", "proposed"] then
    return ← elabOr (substitution inputs)
  if has inputs "point_forward" && k ["source", "target", "point_forward", "point_inverse",
      "target_pullback_rows", "source_pullback_rows", "question"] &&
      (obj? inputs "source").all modelOk && (obj? inputs "target").all modelOk then
    return ← ringMapFamily inputs
  if has inputs "forward_cofactors" && k ["variables", "generators", "forward", "inverse",
      "forward_cofactors", "inverse_cofactors"] then
    return ← ringMapFamily inputs
  if has inputs "target_ideal" && k ["variables", "source_ideal", "target_ideal", "identity", "origin",
      "point", "point_containment_proof", "identity_difference", "target_cofactors"] then
    return ← elabOr (idealsFamily inputs)
  if has inputs "nonzero_guards" && k ["coefficient_domain", "point_universe", "variables", "equations",
      "nonzero_guards", "point"] && (str? inputs "point_universe").all (· == "rational points") then
    return ← pointFamily inputs
  if (has inputs "target_variables" && k ["source_variables", "target_variables", "identity"]) ||
      (has inputs "eliminated" && k ["built_generators", "eliminated"]) then
    return ← elabOr (eliminationFamily inputs)
  if has inputs "excluded_fiber_generators" && k ["variables", "parent_equations", "excluded_base",
      "excluded_fiber_generators", "parent_point"] then
    return ← fiberFamily inputs
  if k ["variables", "equations", "point"] && has inputs "point" && has inputs "equations" then
    return ← displayedPointFamily inputs
  if has inputs "source_universe" && k ["variables", "generators", "coefficient_domain", "source_universe",
      "target_universe"] && str? inputs "coefficient_domain" == some "Q" then
    return ← elabOr (universesFamily inputs)
  if has inputs "region" && k ["variables", "equations", "region", "predicate"] then
    return ← regionalFamily inputs
  if has inputs "claims" && k ["claims", "requested"] then
    return ← elabOr (surfaceFamily inputs)
  if has inputs "searched_exponents" && k ["built_generators", "source_generators", "searched_exponents"] then
    return ← searchFamily inputs
  if has inputs "field_polynomial" && k ["variables", "generators", "guards", "point_universe",
      "field_polynomial", "coordinate", "proposed_change"] &&
      (str? inputs "point_universe" |>.all (· == "ALGEBRAIC_CLOSURE")) &&
      ((obj? inputs "proposed_change").all fun c =>
        c == .null || (match c with | .arr _ => true | _ => false) ||
        onlyKeys c ["generators", "open_conditions", "point_universe", "verifier_version"]) then
    return ← elabOr (extensionWitnessFamily inputs)
  -- The combinatorial context keys (object, vertices, classes, edges) describe the system only.
  if has inputs "witness_field" && k ["object", "vertices", "classes", "edges", "coefficient_domain",
      "point_universe", "variables", "equations", "point", "witness_field", "nonzero_guards",
      "interpretation_limit"] &&
      str? inputs "coefficient_domain" == some "Q" && str? inputs "point_universe" == some "ALGEBRAIC_CLOSURE" &&
      nestedOk inputs "witness_field" ["kind", "base", "symbol", "minimal_polynomial"] &&
      (obj? inputs "witness_field").any (fun w => str? w "kind" == some "simple_number_field_v1" &&
        str? w "base" == some "Q") then
    return ← extensionPointFamily inputs
  if has inputs "cancelled_conclusion" && k ["variables", "product", "cancelled_conclusion", "point",
      "unit_witness"] then
    return ← cancelFamily inputs
  if has inputs "source_predicate" && k ["control", "source_point", "target_point", "forward", "backward",
      "source_predicate"] && (str? inputs "control").any (["backward_rewrite", "wrong_forward_rewrite"].contains ·) then
    return ← translationFamily inputs
  if has inputs "element" && k ["variables", "generators", "element", "annihilator", "cofactors",
      "nonzero_point", "zero_point"] then
    return ← elementFamily case inputs
  if has inputs "branches" && k ["parent", "branches"] && (obj? inputs "parent").all modelOk &&
      (match obj? inputs "branches" with | some (.arr bs) => bs.all modelOk | _ => false) then
    return ← coverFamily inputs
  if has inputs "attempt" && k ["variables", "generators", "characteristic", "point", "attempt"] then
    return ← attemptFamily inputs case
  if let some (.arr ids) := obj? inputs "identity" then
    if k ["identity", "source_context", "target_context"] then
      -- An identity written in one context and copied into another context's signature.
      let sides ← ids.toList.mapM text
      let vars := (sides.flatMap identifiers).eraseDups
      let (scope, field) ← scopeField inputs
      return ← ambient vars (sides.getD 0 "0") (sides.getD 1 "0") scope field
  if k legacyKeys then
    return ← elabOr (do let i ← frontend case params; pure (single i.stmt i.scope (.receipt i.cert)))
  throw "inputs fit no 3a frontend family"

end GPProfile.Families
