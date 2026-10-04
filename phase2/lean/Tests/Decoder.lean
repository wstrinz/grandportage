import GP50.Decoder
open GP50 Lean
open GP50.Decoder

private def obj (fields : List (String × Json)) : Json := Json.mkObj fields
private def text (value : String) : Json := Json.str value
private def number (value : Nat) : Json := toJson value
private def binding : Binding :=
  { statementHash := "P", scopeHash := "S", modelHash := "M",
    inputHashes := ["x", "escaped\ninput"], authority := "fixture-authority",
    authorityVersion := 1, kernelVersion := 1 }
private def bindingJson (b : Binding) : Json := obj [
  ("statementHash", text b.statementHash), ("scopeHash", text b.scopeHash),
  ("modelHash", text b.modelHash), ("inputHashes", toJson b.inputHashes),
  ("authority", text b.authority), ("authorityVersion", number b.authorityVersion),
  ("kernelVersion", number b.kernelVersion)]
private def evidenceJson : Evidence → Json
  | .receipt data => obj [("kind", text "receipt"), ("data", text data)]
  | .theoremWarrant declaration =>
    obj [("kind", text "theorem_warrant"), ("declaration", text declaration)]
  | .derived premises sideReceipt => obj [
    ("kind", text "derived"), ("premises", toJson premises), ("sideReceipt", text sideReceipt)]
  | .narrow premise => obj [("kind", text "narrow"), ("premise", number premise)]
  | .citation value => obj [("kind", text "citation"), ("text", text value)]
  | .assertion => obj [("kind", text "assertion")]
  | .attempt status => obj [("kind", text "attempt"), ("status", text (match status with
    | .absent => "absent" | .failed => "failed" | .timeout => "timeout"))]
private def currentJson (value : Current) : Json := obj [
  ("claim", number value.claim), ("version", number value.version),
  ("binding", bindingJson value.binding)]
private def warrantJson (value : Warrant) : Json := obj [
  ("id", number value.id), ("claim", number value.claim), ("version", number value.version),
  ("binding", bindingJson value.binding), ("evidence", evidenceJson value.evidence)]
private def eventJson : Event → Json
  | .declareClaim claim => obj [("kind", text "declare_claim"), ("claim", number claim)]
  | .current value => obj [("kind", text "current"), ("value", currentJson value)]
  | .warrant value => obj [("kind", text "warrant"), ("value", warrantJson value)]
  | .retract target => obj [("kind", text "retract"), ("target", number target)]
  | .supersede target successor => obj [
    ("kind", text "supersede"), ("target", number target), ("successor", number successor)]
private def envelope (events : List Event) : Json := obj [
  ("schema_version", number 1), ("events", Json.arr (events.map eventJson).toArray)]
private def without (json : Json) (key : String) : Json :=
  match json with
  | .obj fields => obj (fields.toList.filter fun field => field.1 != key)
  | _ => json
private def objectKeys (json : Json) : List String :=
  match json with | .obj fields => fields.keys | _ => []
private def bad [BEq α] (result : Except String α) : Bool :=
  match result with | .error _ => true | .ok _ => false
private def equals [BEq α] (result : Except String α) (expected : α) : Bool :=
  match result with | .ok value => value == expected | .error _ => false
private def ensure (counter : IO.Ref Nat) (name : String) (condition : Bool) : IO Unit := do
  if !condition then throw (IO.userError s!"FAILED: {name}")
  counter.modify (· + 1)
  IO.println s!"PASS: {name}"
private def current (version : Nat := 1) (b : Binding := binding) : Event :=
  .current { claim := 1, version, binding := b }
private def warrant (id : Nat := 10) (version : Nat := 1)
    (b : Binding := binding) (evidence : Evidence := .receipt "unvalidated") : Event :=
  .warrant { id, claim := 1, version, binding := b, evidence }
private def candidates (json : Json) : Except String (List Nat) := do
  let snapshot ← resolve (← decode json.compress)
  return eligibleIds snapshot
private def permutations {α : Type} : List α → List (List α)
  | [] => [[]]
  | value :: values => (permutations values).flatMap fun xs =>
    (List.range (xs.length+1)).map fun n => xs.take n ++ [value] ++ xs.drop n

private def rawObject (fields : List String) : String :=
  "{" ++ String.intercalate "," fields ++ "}"
private def rawFields (json : Json) : List String :=
  match json with
  | .obj fields => fields.toList.map fun field => (text field.1).compress ++ ":" ++ field.2.compress
  | _ => []
private def duplicateBefore (json : Json) (key : String) (prior : Json) : String :=
  rawObject (((text key).compress ++ ":" ++ prior.compress) :: rawFields json)
private def duplicateSpelling (json : Json) (rawKey : String) (prior : Json) : String :=
  rawObject ((rawKey ++ ":" ++ prior.compress) :: rawFields json)
private def rawField (json : Json) (key value : String) : String :=
  match json with
  | .obj fields => rawObject (fields.toList.map fun field =>
      (text field.1).compress ++ ":" ++ (if field.1 == key then value else field.2.compress))
  | _ => ""
private def rawEnvelope (event : String) : String :=
  "{\"schema_version\":1,\"events\":[" ++ event ++ "]}"
private def rawWarrantValue (value : String) : String :=
  "{\"kind\":\"warrant\",\"value\":" ++ value ++ "}"
private def duplicateError (result : Except String (List Event)) : Bool :=
  match result with
  | .error message => (message.splitOn "duplicate object key:").length > 1
  | .ok _ => false

def main : IO Unit := do
  let counter ← IO.mkRef 0
  let check := ensure counter
  let evidences : List Evidence := [.receipt "unvalidated", .theoremWarrant "fixture.theorem",
    .derived [1,2,0] "side", .narrow 0, .citation "citation\ntext", .assertion,
    .attempt .absent, .attempt .failed, .attempt .timeout]
  for evidence in evidences do
    let event := warrant 10 1 binding evidence
    check s!"typed roundtrip evidence {repr evidence}" (equals (decodeEvent (eventJson event)) event)
    check s!"JSON text roundtrip evidence {repr evidence}" (equals (decode (envelope [event]).compress) [event])
  let events := [.declareClaim 0, current, warrant, .retract 10, .supersede 10 11]
  for event in events do
    check s!"event constructor {repr event}" (equals (decodeEvent (eventJson event)) event)
  check "complete envelope text roundtrip" (equals (decode (envelope events).compress) events)
  check "empty event list" (equals (decode (envelope []).compress) [])
  check "zero identities and versions preserved without semantic admission"
    (equals (decodeBinding (bindingJson {binding with authorityVersion := 0, kernelVersion := 0}))
      {binding with authorityVersion := 0, kernelVersion := 0})
  check "escaped string data retained"
    (equals (decodeEvidence (evidenceJson (.receipt "quote \" slash \\ newline\n"))) (.receipt "quote \" slash \\ newline\n"))
  for malformed in ["", "{", "{\"schema_version\":1,\"events\":[}",
      "{\"schema_version\":1,\"events\":[],}", "{\"schema_version\":1,\"events\":[]} trailing",
      "{\"schema_version\":1,\"events\":[]} {}"] do
    check s!"malformed/trailing JSON {malformed}" (bad (decode malformed))
  for wrong in [Json.null, Json.bool true, number 1, text "object", Json.arr #[]] do
    check s!"envelope wrong object type {wrong.compress}" (bad (decodeEnvelope wrong))
  for key in ["schema_version", "events"] do
    check s!"missing envelope field {key}" (bad (decodeEnvelope (without (envelope []) key)))
  for version in [number 0, number 2, text "1", Json.bool true, Json.null,
      Json.num ⟨-1,0⟩, Json.num ⟨15,1⟩, Json.num ⟨10,1⟩] do
    check s!"invalid exact schema {version.compress}"
      (bad (decodeEnvelope ((envelope []).setObjVal! "schema_version" version)))
  for value in [Json.null, obj [], text "[]", number 0, Json.bool false] do
    check s!"events array exact type {value.compress}"
      (bad (decodeEnvelope ((envelope []).setObjVal! "events" value)))
  check "extra envelope field" (bad (decodeEnvelope ((envelope []).setObjVal! "held" (Json.bool true))))
  for key in ["statementHash", "scopeHash", "modelHash", "inputHashes",
      "authority", "authorityVersion", "kernelVersion"] do
    check s!"missing binding identity {key}" (bad (decodeBinding (without (bindingJson binding) key)))
  for key in ["statementHash", "scopeHash", "modelHash", "authority"] do
    check s!"binding string cannot be number {key}"
      (bad (decodeBinding ((bindingJson binding).setObjVal! key (number 1))))
  for key in ["authorityVersion", "kernelVersion"] do
    for value in [text "1", Json.bool true, Json.num ⟨-1,0⟩, Json.num ⟨5,1⟩] do
      check s!"binding version exact type {key}/{value.compress}"
        (bad (decodeBinding ((bindingJson binding).setObjVal! key value)))
  for value in [text "x", Json.null, Json.arr #[number 1], Json.arr #[Json.bool true]] do
    check s!"inputHashes strict string array {value.compress}"
      (bad (decodeBinding ((bindingJson binding).setObjVal! "inputHashes" value)))
  check "extra binding field" (bad (decodeBinding ((bindingJson binding).setObjVal! "verified" (Json.bool true))))
  let objects := [currentJson {claim := 1, version := 1, binding},
    warrantJson {id := 10, claim := 1, version := 1, binding, evidence := .assertion}]
  for json in objects do
    let isWarrant := (json.getObjVal? "id").toOption.isSome
    let decodeValue := if isWarrant then (fun j => bad (decodeWarrant j)) else (fun j => bad (decodeCurrent j))
    let keys := if isWarrant then ["id","claim","version","binding","evidence"] else ["claim","version","binding"]
    for key in keys do
      check s!"missing typed value field {isWarrant}/{key}" (decodeValue (without json key))
    for key in (if isWarrant then ["id","claim","version"] else ["claim","version"]) do
      for value in [text "1", Json.bool false, Json.num ⟨-1,0⟩, Json.num ⟨5,1⟩] do
        check s!"typed value Nat strict {isWarrant}/{key}/{value.compress}"
          (decodeValue (json.setObjVal! key value))
    check s!"nested binding must be object {isWarrant}" (decodeValue (json.setObjVal! "binding" Json.null))
    check s!"typed value extra field {isWarrant}" (decodeValue (json.setObjVal! "held" (Json.bool true)))
  for event in events do
    let json := eventJson event
    for key in objectKeys json do
      check s!"missing event field {key}/{json.compress}" (bad (decodeEvent (without json key)))
    check s!"extra event field {json.compress}" (bad (decodeEvent (json.setObjVal! "verified" (Json.bool true))))
  for json in [obj [("kind", text "unknown")], obj [("kind", number 1)], Json.null,
      obj [("kind", text "current"), ("value", Json.arr #[])],
      obj [("kind", text "warrant"), ("value", text "warrant")],
      obj [("kind", text "retract"), ("target", Json.num ⟨-1,0⟩)],
      obj [("kind", text "supersede"), ("target", number 0), ("successor", text "1")]] do
    check s!"invalid event {json.compress}" (bad (decodeEvent json))
  for evidence in evidences do
    let json := evidenceJson evidence
    for key in objectKeys json do
      check s!"missing evidence field {key}/{json.compress}" (bad (decodeEvidence (without json key)))
    check s!"extra evidence field {json.compress}" (bad (decodeEvidence (json.setObjVal! "authority" (text "fake"))))
  for status in ["UNVERIFIED", "FAILED", "complete", "unknown", ""] do
    check s!"unknown native attempt status {status}"
      (bad (decodeEvidence (obj [("kind", text "attempt"), ("status", text status)])))
  for json in [Json.null, obj [("kind", text "unknown")], obj [("kind", Json.bool true)],
      obj [("kind", text "receipt"), ("data", number 1)],
      obj [("kind", text "theorem_warrant"), ("declaration", Json.null)],
      obj [("kind", text "derived"), ("premises", Json.arr #[text "1"]), ("sideReceipt", text "side")],
      obj [("kind", text "derived"), ("premises", Json.arr #[Json.num ⟨-1,0⟩]), ("sideReceipt", text "side")],
      obj [("kind", text "derived"), ("premises", obj []), ("sideReceipt", text "side")],
      obj [("kind", text "derived"), ("premises", Json.arr #[]), ("sideReceipt", Json.bool true)],
      obj [("kind", text "narrow"), ("premise", Json.bool true)],
      obj [("kind", text "citation"), ("text", Json.arr #[])],
      obj [("kind", text "attempt"), ("status", number 0)]] do
    check s!"invalid evidence {json.compress}" (bad (decodeEvidence json))
  for event in [.declareClaim 0, .retract 0, .supersede 0 1] do
    let json := eventJson event
    for key in (objectKeys json).filter (· != "kind") do
      for value in [text "1", Json.bool true, Json.num ⟨-1,0⟩, Json.num ⟨5,1⟩] do
        check s!"event Nat exact type {key}/{json.compress}/{value.compress}"
          (bad (decodeEvent (json.setObjVal! key value)))
  for value in [text "1", Json.num ⟨-1,0⟩, Json.num ⟨5,1⟩] do
    check s!"narrow premise exact Nat {value.compress}"
      (bad (decodeEvidence (obj [("kind", text "narrow"), ("premise", value)])))
  for value in [Json.bool true, Json.num ⟨5,1⟩] do
    check s!"derived premise exact Nat {value.compress}"
      (bad (decodeEvidence (obj [("kind", text "derived"),
        ("premises", Json.arr #[value]), ("sideReceipt", text "side")])))
  check "fractional lexical schema is rejected"
    (bad (decode "{\"schema_version\":1.0,\"events\":[]}"))
  check "one malformed event makes whole envelope fail"
    (bad (decodeEnvelope ((envelope [.declareClaim 0]).setObjVal! "events"
      (Json.arr #[eventJson (.declareClaim 0), Json.null]))))
  let large := 2^128 + 7
  check "arbitrary-size natural ID is preserved"
    (equals (decode (envelope [.declareClaim large]).compress) [.declareClaim large])
  let newer := {binding with inputHashes := ["x^2"]}
  let stale := [current 1, current 2 newer, warrant 10, warrant 11 2 newer]
  check "24 decoded stale/current permutations retain only current custody"
    ((permutations stale).all fun xs => equals (candidates (envelope xs)) [11])
  let targeted := [current, warrant 10, warrant 11, .retract 10]
  check "24 decoded targeted retraction permutations preserve neighbor"
    ((permutations targeted).all fun xs => equals (candidates (envelope xs)) [11])
  check "decoded supersession retires only predecessor"
    (equals (candidates (envelope [current, warrant 10, warrant 11, .supersede 10 11])) [11])
  check "decoder does not grant checker acceptance"
    (equals (decode (envelope [warrant 10 1 binding (.receipt "unvalidated")]).compress)
      [warrant 10 1 binding (.receipt "unvalidated")])
  check "duplicate schema keys reject the earlier invalid version"
    (duplicateError (decode "{\"schema_version\":2,\"schema_version\":1,\"events\":[]}"))
  check "identical duplicate schema keys also reject"
    (duplicateError (decode "{\"schema_version\":1,\"schema_version\":1,\"events\":[]}"))
  for event in events do
    check s!"duplicate discriminant for {repr event}"
      (duplicateError (decode (rawEnvelope (duplicateBefore (eventJson event) "kind" (text "unknown")))))
  for event in [.declareClaim 0, .retract 10, .supersede 10 11] do
    for key in (objectKeys (eventJson event)).filter (· != "kind") do
      check s!"duplicate event identity {key}"
        (duplicateError (decode (rawEnvelope (duplicateBefore (eventJson event) key (text "invalid")))))
  let baseWarrant : Warrant := {id := 10, claim := 1, version := 1, binding, evidence := .attempt .absent}
  for key in ["id", "claim", "version"] do
    check s!"duplicate warrant identity {key}"
      (duplicateError (decode (rawEnvelope (rawWarrantValue
        (duplicateBefore (warrantJson baseWarrant) key (text "invalid"))))))
  for key in objectKeys (bindingJson binding) do
    let value := rawField (warrantJson baseWarrant) "binding"
      (duplicateBefore (bindingJson binding) key (text "altered"))
    check s!"duplicate binding identity at nested depth {key}"
      (duplicateError (decode (rawEnvelope (rawWarrantValue value))))
  for evidence in evidences do
    let value := rawField (warrantJson {baseWarrant with evidence}) "evidence"
      (duplicateBefore (evidenceJson evidence) "kind" (text "unknown"))
    check s!"duplicate evidence constructor {repr evidence}"
      (duplicateError (decode (rawEnvelope (rawWarrantValue value))))
  let duplicateStatus := rawField (warrantJson baseWarrant) "evidence"
    (duplicateBefore (evidenceJson (.attempt .absent)) "status" (text "UNVERIFIED"))
  check "duplicate status cannot erase UNVERIFIED"
    (duplicateError (decode (rawEnvelope (rawWarrantValue duplicateStatus))))
  let escapedKind := duplicateSpelling (eventJson (.declareClaim 0))
    "\"\\u006b\\u0069\\u006e\\u0064\"" (text "unknown")
  check "escaped kind matches unescaped kind"
    (duplicateError (decode (rawEnvelope escapedKind)))
  let escapedSchema := duplicateSpelling (envelope []) "\"schema\\u005fversion\"" (number 2)
  check "escaped schema key matches literal schema key"
    (duplicateError (decode escapedSchema))
  let escapedIdentity := rawField (warrantJson baseWarrant) "binding"
    (duplicateSpelling (bindingJson binding) "\"statement\\u0048ash\"" (text "changed"))
  check "escaped nested identity matches unescaped identity"
    (duplicateError (decode (rawEnvelope (rawWarrantValue escapedIdentity))))
  check "duplicates in array-nested unknown objects are caught before typed decoding"
    (duplicateError (decode "{\"schema_version\":1,\"events\":[{\"wrapper\":[{\"nested\":{\"id\":0,\"id\":1}}]}]}"))
  check "duplicates at empty key are caught"
    (duplicateError (decode "{\"schema_version\":1,\"events\":[],\"\":0,\"\":1}"))
  check "escaped slash key compares after string decoding"
    (duplicateError (decode "{\"schema_version\":1,\"events\":[],\"a/b\":0,\"a\\/b\":1}"))
  check "surrogate-pair spelling matches decoded Unicode key"
    (duplicateError (decode "{\"schema_version\":1,\"events\":[],\"𝄞\":0,\"\\ud834\\udd1e\":1}"))
  check "same field names in separate typed objects remain legal"
    (equals (decode (envelope [current, warrant 10, warrant 11]).compress)
      [current, warrant 10, warrant 11])
  let opaqueReceipt := "{\"kind\":\"bad\",\"kind\":\"receipt\",\"nested\":{\"id\":0,\"id\":1}}"
  check "duplicate-looking receipt strings stay opaque"
    (equals (decode (envelope [warrant 10 1 binding (.receipt opaqueReceipt)]).compress)
      [warrant 10 1 binding (.receipt opaqueReceipt)])
  let punctuationReceipt := String.ofList ['"', '\\', '{', '[', ',', ']', '}', '"']
  check "escaped quotes slash braces and comma in receipt do not affect object scopes"
    (equals (decode (envelope [warrant 10 1 binding (.receipt punctuationReceipt)]).compress)
      [warrant 10 1 binding (.receipt punctuationReceipt)])
  check "parser normalizes negative zero; lexical sign is not retained"
    (equals (decode "{\"schema_version\":1,\"events\":[{\"kind\":\"declare_claim\",\"claim\":-0}]}") [.declareClaim 0])
  IO.println s!"Decoder: {← counter.get} controls passed; typed data and custody only."

