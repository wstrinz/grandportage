import GP50.Entry
namespace GP50.Lifecycle
open Lean

def bindingJson (b : Binding) : Json := Json.mkObj [
  ("statementHash", toJson b.statementHash), ("scopeHash", toJson b.scopeHash),
  ("modelHash", toJson b.modelHash), ("inputHashes", toJson b.inputHashes),
  ("authority", toJson b.authority), ("authorityVersion", toJson b.authorityVersion),
  ("kernelVersion", toJson b.kernelVersion)]

def evidenceJson : Evidence → Json
  | .receipt data => Json.mkObj [("kind", toJson "receipt"), ("data", toJson data)]
  | .theoremWarrant declaration => Json.mkObj [
      ("kind", toJson "theorem_warrant"), ("declaration", toJson declaration)]
  | .derived premises side => Json.mkObj [
      ("kind", toJson "derived"), ("premises", toJson premises), ("sideReceipt", toJson side)]
  | .narrow premise => Json.mkObj [("kind", toJson "narrow"), ("premise", toJson premise)]
  | .citation text => Json.mkObj [("kind", toJson "citation"), ("text", toJson text)]
  | .assertion => Json.mkObj [("kind", toJson "assertion")]
  | .attempt status => Json.mkObj [("kind", toJson "attempt"), ("status", toJson
      (match status with | .absent => "absent" | .failed => "failed" | .timeout => "timeout"))]

def currentJson (c : Current) : Json := Json.mkObj [
  ("claim", toJson c.claim), ("version", toJson c.version), ("binding", bindingJson c.binding)]

def warrantJson (w : Warrant) : Json := Json.mkObj [
  ("id", toJson w.id), ("claim", toJson w.claim), ("version", toJson w.version),
  ("binding", bindingJson w.binding), ("evidence", evidenceJson w.evidence)]

def snapshotJson (snapshot : Snapshot) : Json := Json.mkObj [
  ("domain", toJson snapshot.domain),
  ("currents", toJson (snapshot.currents.map currentJson)),
  ("warrants", toJson (snapshot.warrants.map warrantJson)),
  ("retracted", toJson snapshot.retracted), ("successors", toJson snapshot.successors)]

-- Operational custody only: no receipt, proof, rule or narrowing is admitted.
def run (text : String) : Except String Json := do
  let events ← Decoder.decode text
  let resolved ← resolve events
  let state ← fold Admission.refuseAll events
  return Json.mkObj [
    ("status", toJson "OK"),
    ("admission", toJson "refuseAll"),
    ("resolve_fold_snapshot_equal", toJson (resolved == state.snapshot)),
    ("snapshot", snapshotJson state.snapshot),
    ("supports", toJson state.supports), ("held", toJson state.claims),
    ("held_queries", toJson (state.snapshot.domain.map fun claim =>
      Json.mkObj [("claim", toJson claim), ("held", toJson (held state claim))])),
    ("live_warrants", toJson (eligibleIds state.snapshot))]
end GP50.Lifecycle

def main (args : List String) : IO UInt32 := do
  match args with
  | [eventsPath] =>
    let events ← IO.FS.readFile eventsPath
    let result := match GP50.Lifecycle.run events with
      | .ok output => output
      | .error error => Lean.Json.mkObj [
          ("status", Lean.toJson "MALFORMED"), ("error", Lean.toJson error)]
    IO.println result.compress
    return 0
  | _ =>
    IO.eprintln "usage: gp_lifecycle_runner <events.json>"
    return 2
