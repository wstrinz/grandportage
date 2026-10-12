import GPProfile.Corpus

/-! The `gp_corpus_run` executable: the 3a corpus run (post-G2 §3.7). -/

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
