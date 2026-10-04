import GP50.Entry
import GP50.CoveredDecoder
import GP50.QueryDecoder
import GP50.Presentation
import GP50.Conflict
namespace GP50.ScopedSpan
open Lean
-- The witness code is the shared point itself; soundness exhibits it as a common context.
def overlap : Semantic.Overlap profile where
  Code := Nat
  witness a b := a.find? (b.contains)
  sound := by
    intro a b k found
    exact ⟨k, List.mem_of_find?_eq_some found, List.contains_iff_mem.mp (List.find?_some found)⟩
def releaseJson (review : Semantic.ReleaseReview profile overlap) : Json := Json.mkObj [
  ("allowed", toJson review.allowed),
  ("findings", toJson (review.findings.map fun f => Json.mkObj [
    ("supports", toJson [f.leftSupport,f.rightSupport]),
    ("claims", toJson [f.leftClaim,f.rightClaim]),
    ("overlap_witness", toJson (f.witness : Option Nat))]))]
def run (registry events queries : String) : Except String Json := do
  let json ← GP50.Decoder.parseUnique registry
  let version ← (← json.getObjVal? "schema_version").getNat?
  let (admitted, rows) ← if version == 3 then do
    let (rows, receipts, rules) ← CoveredSpan.decode registry
    pure (CoveredSpan.admission rows receipts rules, rows)
  else do
    let (rows, receipts) ← decode registry
    pure (admission rows receipts, rows)
  let request ← GP50.Queries.decodeRequest queries
  let state ← decodeFold admitted events
  return Json.mkObj [
    ("state", stateJson state),
    ("release", releaseJson (Semantic.reviewRelease profile overlap (rows.map semantic) state)),
    ("why_not", toJson ((canonicalIds request.whyNot).map fun key =>
      whyNotJson (GP50.Queries.whyNot admitted state key))),
    ("earned", toJson ((GP50.Queries.earned state request.claimed request.links request.openIds).map earnedJson))]
end GP50.ScopedSpan

def main (args : List String) : IO UInt32 := do
  match args with
  | [registryPath, eventsPath, queriesPath] =>
    let result := GP50.ScopedSpan.run (← IO.FS.readFile registryPath)
      (← IO.FS.readFile eventsPath) (← IO.FS.readFile queriesPath)
    IO.println (match result with
      | .ok output => output.compress
      | .error error => (Lean.Json.mkObj [
          ("status", Lean.toJson "MALFORMED"), ("error", Lean.toJson error)]).compress)
    return 0
  | _ =>
    IO.eprintln "usage: gp_scoped_runner <registry.json> <events.json> <queries.json>"
    return 2
