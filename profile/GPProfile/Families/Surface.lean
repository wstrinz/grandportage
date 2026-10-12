import GPProfile.Families.Core

/-! Family adapters: the explicit statement surface. -/

namespace GPProfile.Families
open Lean GPProfile

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

def surfaceField (c : Json) : Field :=
  match (obj? c "characteristic").bind (·.getNat?.toOption) with
  | some p => .prime p
  | none => .rat

/-- An ideal certificate; `guards` (indices) selects the guards its identity uses (3P). -/
def surfaceIdealCert (vars : List String) (c : Json) : Except String Cert := do
  if !onlyKeys c ["type", "cofactors", "m", "k", "characteristic", "guards"] then throw "unknown certificate key"
  let qs ← (← strs c "cofactors").mapM (canonP vars)
  match obj? c "guards" with
  | none => pure (.ideal (surfaceField c) qs (natField c "m") (natField c "k"))
  | some _ =>
    let sel ← nats c "guards"
    let mask := (List.range (sel.foldl max 0 + 1)).map sel.contains
    pure (.idealSel mask (surfaceField c) qs (natField c "m") (natField c "k"))

def surfaceCerts (vars : List String) (rule : Json) (k : String) : Except String (List Cert) := do
  match obj? rule k with
  | some (.arr cs) => cs.toList.mapM (surfaceIdealCert vars)
  | none => pure []
  | _ => throw s!"{k} must be a list"

/-- A monomial written as text (`a`, `x^2*y`): its exponent vector. -/
def surfaceMonomial (vars : List String) (t : String) : Except String (List Nat) := do
  match ← canonP vars t with
  | [(e, 1)] => pure e
  | _ => throw "monomial must be a single term with coefficient 1"

/-- What a surface claim files before its support. -/
structure SurfaceHead where
  key : Nat
  stmt : Stmt
  scope : Scope
  extra : List String
  premises : List Nat

/-- A claim's key, statement, scope, binding inputs and premises (independent of other claims). -/
def surfaceHead (c : Json) : Except String SurfaceHead := do
  if !onlyKeys c ["key", "variables", "equations", "nonzero", "kind", "target", "characteristic",
      "outside", "inputs", "certificate", "rule", "premises"] then throw "unknown claim key"
  let key ← need ((obj? c "key").bind (·.getNat?.toOption)) "claim without key"
  let vars ← strs c "variables"
  let stmt : Stmt := ⟨vars, ← (← strs c "equations").mapM (canonP vars),
    ← (← strs c "nonzero").mapM (canonP vars), ← surfaceKind vars c⟩
  let scope : Scope ← match (obj? c "characteristic").bind (·.getNat?.toOption), obj? c "outside" with
    | some p, none => pure (.only p)
    | none, some _ => pure (.outside (← nats c "outside"))
    | none, none => pure .char0Only
    | some _, some _ => throw "a claim has a characteristic or an outside list, not both"
  let extra ← match obj? c "inputs" with
    | some _ => strs c "inputs"
    | none => pure []
  let premises ← nats c "premises"
  pure { key, stmt, scope, extra, premises }

/-- A claim's item, given the statement filed earlier under its first premise (`prem?`). -/
def surfaceItem (prem? : Option Stmt) (c : Json) (h : SurfaceHead) : Except String Item := do
  let vars := h.stmt.vars
  let stmt := h.stmt
  let premises := h.premises
  let support ← match obj? c "certificate", obj? c "rule" with
      | some cert, none =>
        let ty := (str? cert "type").getD ""
        if ty == "ideal" then pure (Support.receipt (← surfaceIdealCert vars cert))
        else if ty == "point" then
          if !onlyKeys cert ["type", "point", "characteristic"] then throw "unknown certificate key" else
          pure (.receipt (.point (surfaceField cert) (← ratPoint vars (← need (obj? cert "point") "no point"))))
        else if ty == "proper_coefficient" then
          if !onlyKeys cert ["type", "monomial", "characteristic"] then throw "unknown certificate key" else
          pure (.receipt (.properCoeff (surfaceField cert)
            (← surfaceMonomial vars (← need (str? cert "monomial") "no monomial"))))
        else throw "unknown certificate type"
      | none, some rule =>
        let prem ← need prem? "a rule needs its premises filed first"
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
  pure (mkItem h.key stmt h.scope support h.extra)

/-- The first premise's statement among earlier filings (first filing wins, as `find?` would). -/
def surfacePrem (filed : Std.HashMap Nat Stmt) (h : SurfaceHead) : Option Stmt :=
  h.premises.head?.bind fun k => filed[k]?

/-- One sequential filing step: the specification of `surfaceFamily` (`surfaceFamily_eq`). -/
def surfaceStep (acc : List Item × Std.HashMap Nat Stmt) (c : Json) :
    Except String (List Item × Std.HashMap Nat Stmt) := do
  let h ← surfaceHead c
  let it ← surfaceItem (surfacePrem acc.2 h) c h
  pure (it :: acc.1, acc.2.insertIfNew h.key h.stmt)

/-- The surface plan, filing claims one by one: linear in claims. -/
def surfaceFamilySeq (inputs : Json) : Except String Plan := do
  let claims ← match obj? inputs "claims" with
    | some (.arr cs) => pure cs.toList
    | _ => throw "no claims"
  let requested ← nats inputs "requested"
  let (revItems, _) ← claims.foldlM surfaceStep ([], {})
  pure { items := revItems.reverse, requested }

/-- Each head's `surfacePrem` against the heads before it; a failed head files nothing. -/
def surfacePrems : Std.HashMap Nat Stmt → List (Except String SurfaceHead) → List (Option Stmt)
  | _, [] => []
  | filed, .ok h :: hs =>
    let p := surfacePrem filed h
    p :: surfacePrems (filed.insertIfNew h.key h.stmt) hs
  | filed, .error _ :: hs => none :: surfacePrems filed hs

/-- Collect items in reverse; the first failure (in claim order) wins. -/
def surfaceCollect (acc : List Item) (its : List (Except String Item)) : Except String (List Item) :=
  its.foldlM (fun acc it => do pure ((← it) :: acc)) acc

/-- The surface plan with heads and items elaborated in parallel (`parMap`); only the premise
lookups run in order. Equal to `surfaceFamilySeq` (`surfaceFamily_eq`). -/
def surfaceFamily (inputs : Json) : Except String Plan := do
  let claims ← match obj? inputs "claims" with
    | some (.arr cs) => pure cs.toList
    | _ => throw "no claims"
  let requested ← nats inputs "requested"
  let heads := parMap surfaceHead claims
  let its := parMap (fun ((c, h), p) => do surfaceItem p c (← h))
    ((claims.zip heads).zip (surfacePrems {} heads))
  let revItems ← surfaceCollect [] its
  pure { items := revItems.reverse, requested }

theorem surfaceCollect_eq (claims : List Json) (acc : List Item) (filed : Std.HashMap Nat Stmt) :
    surfaceCollect acc (((claims.zip (claims.map surfaceHead)).zip
        (surfacePrems filed (claims.map surfaceHead))).map fun ((c, h), p) => do surfaceItem p c (← h)) =
      Prod.fst <$> claims.foldlM surfaceStep (acc, filed) := by
  induction claims generalizing acc filed with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, surfaceCollect, List.foldlM_cons, surfaceStep]
    cases hh : surfaceHead c with
    | error e => rfl
    | ok h =>
      simp only [surfacePrems, List.zip_cons_cons, List.map_cons, List.foldlM_cons]
      cases hi : surfaceItem (surfacePrem filed h) c h with
      | error e => simp only [bind, Except.bind, hi]; rfl
      | ok it =>
        simp only [bind, Except.bind, hi, pure, Except.pure]
        exact ih (it :: acc) (filed.insertIfNew h.key h.stmt)

theorem surfaceFamily_eq (inputs : Json) : surfaceFamily inputs = surfaceFamilySeq inputs := by
  unfold surfaceFamily surfaceFamilySeq
  simp only [parMap_eq, surfaceCollect_eq]
  split
  · rename_i cs _
    cases nats inputs "requested" with
    | error e => rfl
    | ok rq =>
      simp only [bind, Except.bind, pure, Except.pure]
      cases cs.toList.foldlM surfaceStep ([], {}) with
      | error e => rfl
      | ok r => rfl
  · rfl

end GPProfile.Families
