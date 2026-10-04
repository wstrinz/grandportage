import GP50.Decoder
namespace GP50.Queries
open Lean GP50.Decoder
structure Request where
  whyNot : List Nat
  claimed : List Nat
  links : List (Nat × List Nat)
  openIds : List Nat
private def ids (json : Json) (key : String) : Except String (List Nat) := do
  (← (← json.getObjVal? key).getArr?).toList.mapM Json.getNat?
def decodeRequest (text : String) : Except String Request := do
  let json ← parseUnique text
  exactFields json ["schema_version", "why_not", "claimed", "links", "open_obligations"]
  if (← (← json.getObjVal? "schema_version").getNat?) != 1 then throw "unsupported query schema"
  let links ← (← (← json.getObjVal? "links").getArr?).toList.mapM fun row => do
    exactFields row ["claim", "obligations"]
    return (← (← row.getObjVal? "claim").getNat?, ← ids row "obligations")
  return ⟨← ids json "why_not", ← ids json "claimed", links, ← ids json "open_obligations"⟩
end GP50.Queries
