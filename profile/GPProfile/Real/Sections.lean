import GPProfile.Families.Base
import GPProfile.Real.Plan

/-!
C6: section and output-membership receipts (post-G2 §5, "sections and map identities"). Both are
read as 3a IN_IDEAL claims with 3a C3 receipts (`h = Σ qᵢ·eqᵢ`, `m = 1`, `k = 0`), so admission and
soundness are 3a's, lifted unchanged (`certOk3` on `.alg`). No statement kind, checker or rule is new.

- **Section** `φ` from a target model `T` to a source model `S` (`φ` sends each eliminated source
  variable to its section polynomial and every other source variable to itself): one claim per source
  equation `e`, IN_IDEAL(`e ∘ φ`) on `T`. These are exactly R3's ideal-level map obligations
  (`idealMapObligations T S φ`), with `e ∘ φ` computed by the same `compose`. Together they say that
  `φ` maps the locus of `T` into the locus of `S`, in every field of characteristic 0.
- **Output membership** (no invention): one claim per output equation `o`, IN_IDEAL(`o`) on the
  source system. Output completeness is not claimed. The ideal of an empty output is the zero ideal
  `⟨0⟩`, so an empty output is the single claim IN_IDEAL(0), whose certificate is all zero cofactors:
  replayed like any other, and the only certificate the frontend writes itself.

Custody. A receipt replays the proof rows it carries. A previous binding (`previously_bound_rows`)
is never read as evidence: those rows are filed as separate, unrequested control claims, so an
altered proof cannot inherit their verdict (GP-X256, GP-X259). Producer metadata and execution
evidence are not inputs to admission (GP-X257, GP-X260, GP-X261). A stated substitution result that
differs from the computed composition binds its receipt to a different statement (detached). A source
or output equation with no row has no support.
-/

namespace GPProfile.Real
open Lean GP50 GPProfile GPProfile.Families

/-- A ℚ model `{field, variables, equations}` as a guard-free 3a system. -/
def c6Model (inputs : Json) (key : String) : Except String Stmt := do
  let some j := obj? inputs key | throw s!"missing input '{key}'"
  unless onlyKeys j ["field", "variables", "equations"] && has j "variables" && has j "equations" do
    throw s!"'{key}' must have exactly field, variables and equations"
  unless (str? j "field").all (fun f => f == "Q" || f == "QQ") do throw s!"'{key}': only Q is expressible"
  let vars ← strs j "variables"
  pure ⟨vars, ← (← strs j "equations").mapM (parse vars), [], .empty⟩

/-- `S.vars` with the eliminated variables removed must be `T.vars`, and every eliminated variable
must be a source variable. -/
def c6Vars (S T : Stmt) (elim : List String) : Except String Unit := do
  unless elim.all S.vars.contains && S.vars.filter (!elim.contains ·) == T.vars do
    throw "source variables must be the target variables plus the eliminated ones"

/-- A proof row's fields. -/
structure C6Row where
  equation : Sparse
  result : Option Sparse
  cofactors : List Sparse

/-- Rows: `equation` in `eqVars`, the optional `substitution_result` and `cofactors` in `cofVars`. -/
def c6Rows (j : Json) (eqVars cofVars : List String) : Except String (List C6Row) := do
  (← j.getArr?).toList.mapM fun r => do
    unless onlyKeys r ["equation", "substitution_result", "cofactors"] do throw "unexpected proof row key"
    let eq ← parse eqVars (← text ((obj? r "equation").getD .null))
    let res ← (obj? r "substitution_result").mapM fun t => do parse cofVars (← text t)
    pure ⟨eq, res, ← (← strs r "cofactors").mapM (parse cofVars)⟩

/-- The rows in `key` (an array), or none when the key is absent or null. -/
def c6RowsAt (inputs : Json) (key : String) (eqVars cofVars : List String) :
    Except String (Option (List C6Row)) :=
  match obj? inputs key with
  | none | some .null => pure none
  | some j => some <$> c6Rows j eqVars cofVars

/-- The IN_IDEAL claim on `base` for `h`. -/
def c6Claim (base : Stmt) (h : Sparse) : Stmt3 := .alg { base with kind := .inIdeal h }

/-- One claim's item: the first row for `eq` supplies a C3 receipt (`m = 1`, `k = 0`); a stated
result other than `h` binds it to that other statement; no row, no support. -/
def c6Item (key : Nat) (base : Stmt) (eq h : Sparse) (rows : List C6Row) : Item3 :=
  let support : Support3 := match rows.find? (·.equation == eq) with
    | none => .none
    | some r =>
      let other := r.result.bind fun h' => if h' == h then none else some (c6Claim base h')
      .receipt (.alg (.ideal .rat r.cofactors 1 0)) other
  { key, stmt := c6Claim base h, scope := .alg Scope.char0Only, support }

/-- Requested claims `1..n` from `rows`; the previously bound rows, if any, as unrequested
controls `n+1..2n` on the same statements. -/
def c6Plan (base : Stmt) (claims : List (Sparse × Sparse)) (rows : List C6Row)
    (previous : Option (List C6Row)) : Plan3 :=
  let n := claims.length
  let main := claims.zipIdx.map fun ((eq, h), i) => c6Item (i + 1) base eq h rows
  let controls := match previous with
    | none => []
    | some prev => claims.zipIdx.map fun ((eq, h), i) => c6Item (n + i + 1) base eq h prev
  { items := main ++ controls, requested := main.map (·.key) }

/-- GP-X255–X257: `source`, `target`, `eliminated`, `section`, `proof_rows`,
`previously_bound_rows`. -/
def sectionFamily (inputs : Json) : Except String Plan3 := do
  let S ← c6Model inputs "source"
  let T ← c6Model inputs "target"
  let elim ← strs inputs "eliminated"
  c6Vars S T elim
  let some sec := obj? inputs "section" | throw "missing section"
  unless onlyKeys sec elim && elim.all (has sec ·) do
    throw "the section must give exactly the eliminated variables"
  let phi ← S.vars.mapM fun v =>
    if elim.contains v then do parse T.vars (← text ((obj? sec v).getD .null)) else parse T.vars v
  let claims ← S.eqs.mapM fun e => do
    pure (e, ← need (compose T.vars.length phi S.vars.length e) "composition with the section failed")
  let some rows ← c6RowsAt inputs "proof_rows" S.vars T.vars | throw "missing proof_rows"
  pure (c6Plan T claims rows (← c6RowsAt inputs "previously_bound_rows" S.vars T.vars))

/-- GP-X258–X262: `source`, `output`, `eliminated`, `membership_rows`, `previously_bound_rows`,
`execution_evidence` (not an admission input). -/
def outputFamily (inputs : Json) : Except String Plan3 := do
  let S ← c6Model inputs "source"
  let O ← c6Model inputs "output"
  c6Vars S O (← strs inputs "eliminated")
  unless (obj? inputs "execution_evidence").all (·.getStr?.toOption.isSome) do
    throw "execution_evidence must be a string"
  -- Output equations as source polynomials (the embedding of the kept variables).
  let outs ← (← strs (← need (obj? inputs "output") "missing output") "equations").mapM (parse S.vars)
  let some rows ← c6RowsAt inputs "membership_rows" S.vars S.vars | throw "missing membership_rows"
  let prev ← c6RowsAt inputs "previously_bound_rows" S.vars S.vars
  if outs.isEmpty then
    -- The zero ideal `⟨0⟩`: IN_IDEAL(0) by zero cofactors.
    unless rows.isEmpty && prev.all (·.isEmpty) do throw "membership rows for an empty output"
    pure (c6Plan S [([], [])] [⟨[], none, S.eqs.map fun _ => []⟩] none)
  else
    pure (c6Plan S (outs.map fun o => (o, o)) rows prev)

end GPProfile.Real
