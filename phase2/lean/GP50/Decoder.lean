import GP50.Events
import Lean.Data.Json
namespace GP50.Decoder
open Lean

-- Strict typed objects: all and only listed fields are allowed at every level.
-- Parsed-AST entry points cannot recover lost duplicates or attest original
-- bytes or canonical encoding; duplicate rejection belongs to raw decode.
-- Natural fields use getNat?: no strings, booleans, fractions or negative values.
-- Lexical negative zero and some exponent spellings normalize to natural values.
-- Overlapping tool Lean.Json.parse validates JSON syntax but lacks duplicate-key
-- rejection: its object map keeps the last value. This narrow guard runs after
-- that parser succeeds; it only tracks object scopes and decoded key strings.
-- Installed Lean.Json.Parser.str handles escapes; value strings remain opaque.
private inductive KeyFrame where
  | object (keys : List String) (expectsKey : Bool)
  | array

private def scanKeys : Nat → List KeyFrame → Std.Internal.Parsec.String.Parser Unit
  | 0, _ => Std.Internal.Parsec.fail "duplicate-key scan exhausted input bound"
  | fuel+1, frames => do
    if ← Std.Internal.Parsec.isEof then return ()
    let char ← Std.Internal.Parsec.any
    match char with
    | '"' =>
      let value ← Lean.Json.Parser.str
      match frames with
      | .object keys true :: rest =>
        if keys.contains value then
          Std.Internal.Parsec.fail s!"duplicate object key: {value}"
        else
          scanKeys fuel (.object (value :: keys) false :: rest)
      | _ => scanKeys fuel frames
    | '{' => scanKeys fuel (.object [] true :: frames)
    | '[' => scanKeys fuel (.array :: frames)
    | '}' | ']' => scanKeys fuel frames.tail
    | ',' =>
      match frames with
      | .object keys _ :: rest => scanKeys fuel (.object keys true :: rest)
      | _ => scanKeys fuel frames
    | _ => scanKeys fuel frames

private def rejectDuplicateKeys (text : String) : Except String Unit :=
  Std.Internal.Parsec.String.Parser.run (scanKeys (text.utf8ByteSize + 1) []) text

def exactFields (json : Json) (names : List String) : Except String Unit := do
  let object ← json.getObj?
  for key in object.keys do
    if !names.contains key then throw s!"unexpected field: {key}"
  for key in names do
    let _ ← json.getObjVal? key
  return ()

private def strField (json : Json) (key : String) : Except String String := do
  (← json.getObjVal? key).getStr?
private def natField (json : Json) (key : String) : Except String Nat := do
  (← json.getObjVal? key).getNat?
private def listField (json : Json) (key : String)
    (decode : Json → Except String α) : Except String (List α) := do
  (← (← json.getObjVal? key).getArr?).toList.mapM decode

def decodeBinding (json : Json) : Except String Binding := do
  exactFields json ["statementHash", "scopeHash", "modelHash", "inputHashes",
    "authority", "authorityVersion", "kernelVersion"]
  return {
    statementHash := ← strField json "statementHash"
    scopeHash := ← strField json "scopeHash"
    modelHash := ← strField json "modelHash"
    inputHashes := ← listField json "inputHashes" Json.getStr?
    authority := ← strField json "authority"
    authorityVersion := ← natField json "authorityVersion"
    kernelVersion := ← natField json "kernelVersion" }

def decodeAttemptStatus (status : String) : Except String AttemptStatus :=
  match status with
  | "absent" => .ok .absent
  | "failed" => .ok .failed
  | "timeout" => .ok .timeout
  | _ => .error s!"unknown attempt status: {status}"

def decodeEvidence (json : Json) : Except String Evidence := do
  match ← strField json "kind" with
  | "receipt" =>
    exactFields json ["kind", "data"]
    return .receipt (← strField json "data")
  | "theorem_warrant" =>
    exactFields json ["kind", "declaration"]
    return .theoremWarrant (← strField json "declaration")
  | "derived" =>
    exactFields json ["kind", "premises", "sideReceipt"]
    return .derived (← listField json "premises" Json.getNat?) (← strField json "sideReceipt")
  | "narrow" =>
    exactFields json ["kind", "premise"]
    return .narrow (← natField json "premise")
  | "citation" =>
    exactFields json ["kind", "text"]
    return .citation (← strField json "text")
  | "assertion" =>
    exactFields json ["kind"]
    return .assertion
  | "attempt" =>
    exactFields json ["kind", "status"]
    return .attempt (← decodeAttemptStatus (← strField json "status"))
  | kind => throw s!"unknown evidence kind: {kind}"

def decodeCurrent (json : Json) : Except String Current := do
  exactFields json ["claim", "version", "binding"]
  return {
    claim := ← natField json "claim"
    version := ← natField json "version"
    binding := ← decodeBinding (← json.getObjVal? "binding") }

def decodeWarrant (json : Json) : Except String Warrant := do
  exactFields json ["id", "claim", "version", "binding", "evidence"]
  return {
    id := ← natField json "id"
    claim := ← natField json "claim"
    version := ← natField json "version"
    binding := ← decodeBinding (← json.getObjVal? "binding")
    evidence := ← decodeEvidence (← json.getObjVal? "evidence") }

def decodeEvent (json : Json) : Except String Event := do
  match ← strField json "kind" with
  | "declare_claim" =>
    exactFields json ["kind", "claim"]
    return .declareClaim (← natField json "claim")
  | "current" =>
    exactFields json ["kind", "value"]
    return .current (← decodeCurrent (← json.getObjVal? "value"))
  | "warrant" =>
    exactFields json ["kind", "value"]
    return .warrant (← decodeWarrant (← json.getObjVal? "value"))
  | "retract" =>
    exactFields json ["kind", "target"]
    return .retract (← natField json "target")
  | "supersede" =>
    exactFields json ["kind", "target", "successor"]
    return .supersede (← natField json "target") (← natField json "successor")
  | kind => throw s!"unknown event kind: {kind}"

def decodeEnvelope (json : Json) : Except String (List Event) := do
  exactFields json ["schema_version", "events"]
  let version ← natField json "schema_version"
  if version != 1 then throw s!"unsupported schema version: {version}"
  listField json "events" decodeEvent

-- String parsing is delegated unchanged to installed Lean.Json, not replaced.
def parseUnique (text : String) : Except String Json := do
  let json ← Json.parse text
  rejectDuplicateKeys text
  return json

def decode (text : String) : Except String (List Event) := do
  decodeEnvelope (← parseUnique text)
end GP50.Decoder

