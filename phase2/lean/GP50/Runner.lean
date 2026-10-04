import GP50.Entry
import GP50.SpanDecoder
import GP50.Presentation
namespace GP50
open Lean

def runBoundSpan (registry events : String) : Except String RuntimeState := do
  let (clauses, receipts) ← Span.decodeRegistry registry
  decodeFold (Span.admission clauses receipts) events

end GP50

def main (args : List String) : IO UInt32 := do
  match args with
  | [registryPath, eventsPath] =>
    let registry ← IO.FS.readFile registryPath
    let events ← IO.FS.readFile eventsPath
    let result := match GP50.runBoundSpan registry events with
      | .ok state => GP50.stateJson state
      | .error error => Lean.Json.mkObj [
        ("status", Lean.toJson "MALFORMED"), ("error", Lean.toJson error)]
    IO.println result.compress
    return 0
  | _ =>
    IO.eprintln "usage: gp_span_runner <registry.json> <events.json>"
    return 2
