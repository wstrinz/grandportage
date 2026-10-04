import GPBinding.Warrants.Generated
import GPProfile.Canonical

/-!
The binder (G1 decision 2, Addendum A4, G3a review §5). For the registry it checks
* the proofs themselves: the axioms of `registry`, whose definition contains every entry's proof
  term, must be standard (a clean name cannot hide a `sorry` proof);
* each entry's proof is literally the theorem it names, whose type is `Warranted stmt scope`;
* well-formedness: arity, and the scope avoids the statement's primes, so `means_of_warranted`
  gives the Kernel's meaning;
and writes binding records keyed on the canonical statement and scope text, stamped with the
environment of this run (toolchain, Mathlib pin, binding commit, warrant-module fingerprint).
The runtime refuses records whose environment differs from its own. Run via `tools/run-binder.py`.
-/

open Lean Elab Command Meta GPProfile GPBinding.Binder

def standardAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- The `Bound.mk` entries of a list literal, as (name literal, proof expression). -/
partial def registryEntries (e : Expr) : List (String × Expr) :=
  match e.consumeMData.getAppFnArgs with
  | (``List.cons, #[_, hd, tl]) =>
    let entry := match hd.consumeMData.getAppFnArgs with
      | (``GPBinding.Binder.Bound.mk, #[name, _, _, proof]) =>
        match name.consumeMData with
        | .lit (.strVal s) => [(s, proof.consumeMData)]
        | _ => []
      | _ => []
    entry ++ registryEntries tl
  | _ => []

def mathlibPin : IO String := do
  let manifest ← IO.ofExcept (Json.parse (← IO.FS.readFile "lake-manifest.json"))
  let pkgs ← IO.ofExcept ((← IO.ofExcept (manifest.getObjVal? "packages")).getArr?)
  let some m := pkgs.find? fun p => (p.getObjVal? "name").toOption == some (Json.str "mathlib")
    | throw (IO.userError "no mathlib in the manifest")
  IO.ofExcept (do (← m.getObjVal? "rev").getStr?)

#eval show CommandElabM Unit from do
  let env ← getEnv
  let regAxioms ← liftCoreM (Lean.collectAxioms ``GPBinding.Warrants.registry)
  let regOk := regAxioms.all standardAxioms.contains
  let some (.defnInfo info) := env.find? ``GPBinding.Warrants.registry
    | throwError "registry is not a definition"
  let entries := registryEntries info.value
  let mut rows : Array Json := #[]
  for b in GPBinding.Warrants.registry do
    let decl := `GPBinding.Warrants ++ b.name.toName
    let named := entries.any fun (n, proof) => n == b.name && proof.isConstOf decl
    let axs ← liftCoreM (Lean.collectAxioms decl)
    let axiomsOk := regOk && axs.all standardAxioms.contains
    let wf := stmtArityOk b.stmt && b.scope.avoids b.stmt.primes
    rows := rows.push (Json.mkObj [
      ("declaration", toJson decl.toString), ("statementHash", toJson (stmtCanon b.stmt)),
      ("scopeHash", toJson (scopeCanon b.scope)), ("axioms", toJson (axs.map toString)),
      ("proofIsNamedConstant", toJson named), ("axiomsOk", toJson axiomsOk), ("wellFormed", toJson wf),
      ("bound", toJson (named && axiomsOk && wf))])
  let module ← IO.FS.readBinFile "GPBinding/Warrants/Generated.lean"
  let commit := (← IO.getEnv "GP_BINDING_COMMIT").getD "unknown"
  IO.println (Json.mkObj [("schema", "gp-binder/v2"),
    ("environment", Json.mkObj [("toolchain", toJson Lean.versionString),
      ("mathlib", toJson (← mathlibPin)), ("bindingCommit", toJson commit),
      ("warrantModuleFnv1a", toJson (toString (fnv1a module)))]),
    ("registryAxioms", toJson (regAxioms.map toString)), ("records", toJson rows)]).pretty
