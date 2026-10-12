import GPProfile.Corpus
import GPProfile.Real.Frontend

/-!
The `gp_corpus_3b` executable: every case `corpus/GATE-OWNERS.json` assigns to 3b, through the 3b
frontend and the Kernel fold with `admission3`. One aggregate JSON receipt per run. Expected
verdicts are read for reporting only. A case whose checker does not exist yet is reported as
`PENDING:<checker>`, never as a verdict. A case that pins a fixture by its SHA-256 gets the parsed
fixture attached when `oracle/history/PIN.json` lists it and its bytes match (`attachFixture`).
-/

namespace GPProfile.Real.CorpusRun
open Lean GP50 GPProfile GPProfile.Real

/-- Case files live in these corpus directories; a case id must name exactly one file. -/
def caseDirs : List String := ["must", "incidents"]

def casePath (root : System.FilePath) (id : String) : IO String := do
  let hits ← caseDirs.filterM fun (d : String) => (root / "corpus" / d / s!"{id}.json").pathExists
  match hits with
  | [d] => pure s!"corpus/{d}/{id}.json"
  | [] => throw (IO.userError s!"no case file for {id}")
  | _ => throw (IO.userError s!"several case files for {id}")

def itemJson (state : RuntimeState) (i : Item3) : Json :=
  Json.mkObj [("key", toJson i.key), ("family", toJson (familyName i.stmt)), ("scope", toJson (scopeName i.scope)),
    ("support", toJson (supportName3 i.support)), ("held", toJson (held state i.key))]

def runCase (id : String) (case : Json) : Json :=
  let expected := (do (← (← case.getObjVal? "expected").getObjVal? "verdict").getStr?).toOption
  let base : List (String × Json) := [("id", toJson id), ("expected", toJson expected)] ++
    (if (case.getObjVal? "instantiated").toOption == some (Json.bool true) then [("instantiated", Json.bool true)]
     else [])
  match frontend3 case with
  | .error e => Json.mkObj (base ++ [("observed", Json.str "EXPRESSIVENESS_LOSS"), ("frontend_error", toJson e)])
  | .ok (.pending c why) =>
    Json.mkObj (base ++ [("observed", Json.str s!"PENDING:{c}"), ("mechanism", toJson [why])])
  | .ok (.plan p) =>
    match p.elaboration with
    | some e => Json.mkObj (base ++ [("observed", Json.str "REFUSE"), ("mechanism", toJson ["elaboration: " ++ e])])
    | none =>
      match p.run with
      | .error e => Json.mkObj (base ++ [("observed", Json.str "MALFORMED"), ("error", toJson e)])
      | .ok o =>
        let req := p.items.filter fun i => p.requested.contains i.key
        let mechanism := if o.accepted then req.map fun i => s!"held by {supportName3 i.support}"
          else (req.filter fun i => !held o.state i.key).map (refusal p o.state)
        Json.mkObj (base ++ [("observed", Json.str (if o.accepted then "ACCEPT" else "REFUSE")),
          ("mechanism", toJson mechanism.eraseDups), ("requested", toJson p.requested),
          ("items", toJson (p.items.map (itemJson o.state)))])

/-- 3b instantiation fixtures: the sidecar `corpus/INSTANTIATIONS-3B.json`, under the same policy
as `Corpus.loadCase` (keyed by case id and the FNV-1a of the case bytes; a stale fixture is an
error). Kept apart from `corpus/INSTANTIATIONS.json` so the 3a runner and its receipts never see
3b fixtures. -/
def loadCase3b (root : System.FilePath) (path : String) : IO Json := do
  let case ← GPProfile.Corpus.loadCase root path
  let bytes ← IO.FS.readBinFile (root / path)
  let id := (do (← case.getObjVal? "id").getStr?).toOption.getD ""
  let fx ← IO.ofExcept (Json.parse (← IO.FS.readFile (root / "corpus" / "INSTANTIATIONS-3B.json")))
  let entries := ((fx.getObjVal? "fixtures") >>= Json.getArr?).toOption.getD #[]
  match entries.find? fun e => (e.getObjVal? "id").toOption == some (Json.str id) with
  | none => pure case
  | some e =>
    let h := (do (← e.getObjVal? "case_fnv1a").getStr?).toOption.getD ""
    if h != toString (fnv1a bytes) then
      throw (IO.userError s!"stale 3b instantiation fixture for {id}: the case bytes changed")
    let inputs ← IO.ofExcept (e.getObjVal? "inputs")
    pure ((case.setObjVal! "inputs" inputs).setObjVal! "instantiated" (Json.bool true))

def run (root : System.FilePath) (owners : Json) : IO Json := do
  let entries ← IO.ofExcept ((← IO.ofExcept (owners.getObjVal? "cases")).getArr?)
  let ids := entries.toList.filterMap fun e =>
    if (e.getObjVal? "owner").toOption == some (Json.str "3b") then (do (← e.getObjVal? "id").getStr?).toOption
    else none
  let rows ← ids.mapM fun id => do
    let case ← attachFixture root (← loadCase3b root (← casePath root id))
    pure (runCase id case)
  let field (r : Json) (k : String) : Option String := (r.getObjVal? k >>= Json.getStr?).toOption
  let pending := rows.filter fun r => (field r "observed").any (·.startsWith "PENDING:")
  let decided := rows.filter fun r => !(field r "observed").any (·.startsWith "PENDING:")
  let agree := decided.filter fun r => field r "observed" == field r "expected"
  let falseAccept := rows.filter fun r => field r "observed" == some "ACCEPT" && field r "expected" != some "ACCEPT"
  return Json.mkObj [("schema", "gp-3b-corpus/v1"), ("case_count", toJson rows.length),
    ("decided", toJson decided.length), ("agree", toJson agree.length), ("pending", toJson pending.length),
    ("false_accept", toJson falseAccept.length), ("cases", toJson rows)]

end GPProfile.Real.CorpusRun

def main (args : List String) : IO UInt32 := do
  match args with
  | [root, ownersPath] =>
    let owners ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile ownersPath))
    IO.println (← GPProfile.Real.CorpusRun.run root owners).pretty
    return 0
  | _ => IO.eprintln "usage: gp_corpus_3b <repo-root> <GATE-OWNERS.json>"; return 2
