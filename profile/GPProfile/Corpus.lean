import GPProfile.Families

/-!
The 3a corpus run (post-G2 §3.7): every listed case through the shared frontend and the Kernel
fold. One aggregate receipt per run (§8). Expected verdicts are read for reporting only.
-/

namespace GPProfile.Corpus
open Lean GP50 GPProfile

def kindName : Kind → String
  | .empty => "EMPTY" | .nonempty => "NONEMPTY" | .inIdeal _ => "IN_IDEAL" | .vanishesOn _ => "VANISHES_ON"
  | .notInIdeal _ => "NOT_IN_IDEAL" | .cover _ => "COVER"

def supportName : Support → String
  | .none => "none"
  | .receipt _ none => "receipt"
  | .receipt _ (some _) => "receipt bound to original"
  | .searched n => s!"searched (non-evidence, {n} exponents)"
  | .rule d _ => match d with
    | .r1 => "rule R1" | .inclusion .. => "rule R2" | .map .. => "rule R3" | .split _ => "rule R4" | .witness => "rule bridge"
    | .byCover => "rule R4 (cover)"

def checkName : Check → String
  | .accepted _ => "accepted" | .notCanonical => "not canonical" | .illFormed _ => "ill-formed"
  | .replayFailed => "replay failed" | .outsideReach _ => "outside reach"

def itemJson (state : RuntimeState) (i : Item) : Json :=
  let base : List (String × Json) := [("key", toJson i.key), ("kind", toJson (kindName i.stmt.kind)),
    ("support", toJson (supportName i.support)), ("held", toJson (held state i.key))]
  Json.mkObj (base ++ match i.support with
    | .receipt cert none => [("check", toJson (checkName (check i.stmt i.scope cert)))]
    | _ => [])

/-- Instantiation fixtures (G3a review §7): a sidecar keyed by case id and the FNV-1a of the case
bytes, signed in corpus/CHANGES.md. A fixture replaces a schematic case's inputs; a fixture whose
hash no longer matches its case is an error, never silently skipped. -/
def loadCase (root : System.FilePath) (path : String) : IO Json := do
  let bytes ← IO.FS.readBinFile (root / path)
  let case ← IO.ofExcept (Json.parse (← IO.FS.readFile (root / path)))
  let id := (do (← case.getObjVal? "id").getStr?).toOption.getD ""
  let fx ← IO.ofExcept (Json.parse (← IO.FS.readFile (root / "corpus" / "INSTANTIATIONS.json")))
  let entries := ((fx.getObjVal? "fixtures") >>= Json.getArr?).toOption.getD #[]
  match entries.find? fun e => (e.getObjVal? "id").toOption == some (Json.str id) with
  | none => pure case
  | some e =>
    let h := (do (← e.getObjVal? "case_fnv1a").getStr?).toOption.getD ""
    if h != toString (fnv1a bytes) then
      throw (IO.userError s!"stale instantiation fixture for {id}: the case bytes changed")
    let inputs ← IO.ofExcept (e.getObjVal? "inputs")
    pure ((case.setObjVal! "inputs" inputs).setObjVal! "instantiated" (Json.bool true))

def runCase (label : String) (case : Json) (params : List (String × Nat))
    (records : List BinderRecord := []) : Json :=
  let expected := (do (← (← case.getObjVal? "expected").getObjVal? "verdict").getStr?).toOption
  let base : List (String × Json) := [("id", toJson label), ("expected", toJson expected)] ++
    (if (case.getObjVal? "instantiated").toOption == some (Json.bool true) then [("instantiated", Json.bool true)]
     else [])
  match Families.plan case params with
  | .error e => Json.mkObj (base ++ [("observed", Json.str "EXPRESSIVENESS_LOSS"), ("frontend_error", toJson e)])
  | .ok p =>
    match p.elaboration with
    | some e => Json.mkObj (base ++ [("observed", Json.str "REFUSE"), ("mechanism", toJson ["elaboration"]),
        ("elaboration", toJson e)])
    | none =>
      match p.run records with
      | .error e => Json.mkObj (base ++ [("observed", Json.str "MALFORMED"), ("error", toJson e)])
      | .ok o =>
        let refused := p.items.filter fun i => p.requested.contains i.key && !held o.state i.key
        let refuter (i : Item) : Option Nat := (p.items.find? fun j => held o.state j.key &&
          ops.contra i.stmt j.stmt && i.scope.overlaps j.scope).map (·.key)
        let mechanism := refused.map fun i => match refuter i, i.support with
          | some j, _ => s!"refuted (contra with held claim {j})"
          | none, .none => "unsupported"
          | none, .searched _ => "no certificate (a bounded search is not evidence)"
          | none, .receipt _ (some _) => "custody (stale binding)"
          | none, .receipt c none => s!"checker ({checkName (check i.stmt i.scope c)})"
          | none, .rule .. => "rule refused"
        let inputs := (case.getObjVal? "inputs").toOption.getD .null
        let named := (namedField? inputs).orElse fun _ =>
          (inputs.getObjVal? "model").toOption.bind namedField?
        let requestsPoint := p.items.any fun i => p.requested.contains i.key && i.stmt.kind == .nonempty
        let strengthened := named.filter fun f =>
          ["R", "RR"].contains f || (["C", "CC"].contains f && requestsPoint)
        Json.mkObj (base ++ (strengthened.map fun f => ("field_strengthened", toJson f)).toList ++
          [("mechanism", toJson mechanism.eraseDups),
          ("observed", Json.str (if o.accepted then "ACCEPT" else "REFUSE")),
          ("requested", toJson p.requested),
          ("items", toJson (p.items.map (itemJson o.state))),
          ("widened", toJson (o.widened.map (·.1))),
          ("earned", toJson o.earned),
          ("theorem_warrants", toJson (o.theorems.map fun (k, d) =>
            Json.mkObj [("key", toJson k), ("declaration", toJson d),
              ("supported", toJson (o.state.supports.contains (1000 + k)))]))])

/-! ## Lean literals of canonical inputs (for the binder's warrant generator) -/

def ratLit (c : Rat) : String := if c.den == 1 then s!"({c.num} : Rat)" else s!"({c.num}/{c.den} : Rat)"
def sparseLit (p : Sparse) : String :=
  "[" ++ ", ".intercalate (p.map fun (e, c) => s!"({e}, {ratLit c})") ++ "]"
def sparsesLit (ps : List Sparse) : String := "[" ++ ", ".intercalate (ps.map sparseLit) ++ "]"
def kindLit : Kind → String
  | .empty => ".empty" | .nonempty => ".nonempty"
  | .inIdeal h => s!"(.inIdeal {sparseLit h})" | .vanishesOn h => s!"(.vanishesOn {sparseLit h})"
  | .notInIdeal h => s!"(.notInIdeal {sparseLit h})"
  | .cover _ => ".cover []"
def stmtLit (s : Stmt) : String :=
  s!"⟨{repr s.vars}, {sparsesLit s.eqs}, {sparsesLit s.guards}, {kindLit s.kind}⟩"
def scopeLit (s : Scope) : String :=
  match s.primes with
  | .finite ps => s!"⟨{s.char0}, .finite {ps}⟩"
  | .cofinite e => s!"⟨{s.char0}, .cofinite {e}⟩"

/-- Held receipt items with their exact canonical inputs, as Lean literals. -/
def candidates (label : String) (case : Json) (params : List (String × Nat)) : List Json :=
  match Families.plan case params with
  | .error _ => []
  | .ok p =>
    match p.run with
    | .error _ => []
    | .ok o =>
      p.items.filterMap fun i => match i.support with
        | .receipt cert0 none =>
          if !held o.state i.key then none else
          -- Warrants are generated at the receipt's widest computed reach (G3a review §5).
          let (scope, cert) := (widenCert i.stmt i.scope cert0).getD (i.scope, cert0)
          let certJ := match cert with
            | .ideal f qs m k => Json.mkObj [("type", "ideal"), ("field", toJson (reprStr f)),
                ("cofactors", toJson (qs.map sparseLit)), ("m", toJson m), ("k", toJson k)]
            | .point f vs => Json.mkObj [("type", "point"), ("field", toJson (reprStr f)),
                ("values", toJson (vs.map ratLit))]
            | .proper f a b => Json.mkObj [("type", "proper"), ("field", toJson (reprStr f)),
                ("a", toJson (a.map ratLit)), ("b", toJson (b.map ratLit))]
            | .cover .. => Json.mkObj [("type", "cover")]
          some (Json.mkObj [("case", toJson label), ("key", toJson i.key), ("vars", toJson i.stmt.vars),
            ("stmt", toJson (stmtLit i.stmt)), ("scope", toJson (scopeLit scope)),
            ("kind", toJson (kindName i.stmt.kind)), ("eqs", toJson (i.stmt.eqs.map sparseLit)),
            ("guards", toJson (i.stmt.guards.map sparseLit)), ("cert", certJ),
            ("statementHash", toJson (stmtCanon i.stmt)), ("scopeHash", toJson (scopeCanon scope))])
        | _ => none

def run (root : System.FilePath) (manifest : Json) (records : List BinderRecord := []) :
    IO Json := do
  let entries ← IO.ofExcept ((← IO.ofExcept (manifest.getObjVal? "cases")).getArr?)
  let rows ← entries.toList.mapM fun entry => do
    let path : String ← IO.ofExcept (do (← entry.getObjVal? "path").getStr?)
    let case ← loadCase root path
    let id := (do (← case.getObjVal? "id").getStr?).toOption.getD path
    let label := (do (← entry.getObjVal? "label").getStr?).toOption.getD id
    let params := match entry.getObjVal? "parameters" with
      | .ok (.obj kvs) => kvs.toList.filterMap fun (k, v) => (v.getNat?.toOption).map (k, ·)
      | _ => []
    pure (runCase label case params records)
  let outcome (r : Json) := (r.getObjVal? "observed").toOption
  let agree := rows.filter fun r => (r.getObjVal? "expected").toOption == outcome r
  let losses := rows.filter fun r => outcome r == some (Json.str "EXPRESSIVENESS_LOSS")
  return Json.mkObj [("schema", "gp-3a-corpus/v1"), ("case_count", toJson rows.length),
    ("agree", toJson agree.length), ("losses", toJson losses.length), ("cases", toJson rows)]

end GPProfile.Corpus

def main (args : List String) : IO UInt32 := do
  match args with
  | [root, manifestPath, "--candidates"] =>
    let manifest ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile manifestPath))
    let entries ← IO.ofExcept ((← IO.ofExcept (manifest.getObjVal? "cases")).getArr?)
    let rows ← entries.toList.mapM fun entry => do
      let path : String ← IO.ofExcept (do (← entry.getObjVal? "path").getStr?)
      let case ← GPProfile.Corpus.loadCase (System.FilePath.mk root) path
      let id := (do (← case.getObjVal? "id").getStr?).toOption.getD path
      let label := (do (← entry.getObjVal? "label").getStr?).toOption.getD id
      let params := match entry.getObjVal? "parameters" with
        | .ok (.obj kvs) => kvs.toList.filterMap fun (k, v) => (v.getNat?.toOption).map (k, ·)
        | _ => []
      pure (GPProfile.Corpus.candidates label case params)
    IO.println (Lean.toJson rows.flatten).pretty
    return 0
  | [root, manifestPath] =>
    let manifest ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile manifestPath))
    IO.println (← GPProfile.Corpus.run root manifest).pretty
    return 0
  | [root, manifestPath, "--binder", recordsPath] =>
    let manifest ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile manifestPath))
    let recJson ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile recordsPath))
    let rows ← IO.ofExcept ((← IO.ofExcept (recJson.getObjVal? "records")).getArr?)
    let field (r : Lean.Json) (k : String) : Option String := (r.getObjVal? k >>= Lean.Json.getStr?).toOption
    -- The binder receipt must come from this environment (G3a review §5c).
    let recEnv := (recJson.getObjVal? "environment").toOption.getD Lean.Json.null
    let bindingDir := System.FilePath.mk root / "binding"
    let module ← IO.FS.readBinFile (bindingDir / "GPBinding" / "Warrants" / "Generated.lean")
    let bManifest ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (bindingDir / "lake-manifest.json")))
    let pkgs := ((bManifest.getObjVal? "packages") >>= Lean.Json.getArr?).toOption.getD #[]
    let mathlib := (pkgs.find? fun p => (p.getObjVal? "name").toOption == some (Lean.Json.str "mathlib")).bind
      fun m => (m.getObjVal? "rev" >>= Lean.Json.getStr?).toOption
    let mismatches := ([("toolchain", some Lean.versionString), ("mathlib", mathlib),
        ("warrantModuleFnv1a", some (toString (GPProfile.fnv1a module)))] : List (String × Option String)).filter
      fun (k, v) => field recEnv k != v
    let records : List GPProfile.BinderRecord := if !mismatches.isEmpty then [] else
      rows.toList.filterMap fun r => do
        if (r.getObjVal? "bound").toOption != some (Lean.Json.bool true) then none else
        pure ⟨← field r "declaration", ← field r "statementHash", ← field r "scopeHash"⟩
    let out ← GPProfile.Corpus.run root manifest records
    let out := if mismatches.isEmpty then out else
      out.setObjVal! "binder_refused" (Lean.toJson (mismatches.map (·.1)))
    IO.println out.pretty
    return 0
  | _ => IO.eprintln "usage: gp_corpus_run <repo-root> <manifest.json>"; return 2
