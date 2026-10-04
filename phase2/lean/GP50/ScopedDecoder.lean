import GP50.ScopedSpan
import GP50.SpanDecoder
namespace GP50.ScopedSpan
open Lean GP50.Decoder
def decodeRow (json : Json) : Except String Row := do
  exactFields json ["algebra", "object", "scope"]
  return ⟨← Span.decodeClause (← json.getObjVal? "algebra"),
    ← (← json.getObjVal? "object").getStr?,
    ← (← (← json.getObjVal? "scope").getArr?).toList.mapM Json.getNat?⟩

def decode (text : String) : Except String (List Row × List Span.Receipt) := do
  let json ← parseUnique text
  exactFields json ["schema_version", "clauses", "receipts"]
  if (← (← json.getObjVal? "schema_version").getNat?) != 2 then
    throw "unsupported scoped registry schema"
  let rows ← (← (← json.getObjVal? "clauses").getArr?).toList.mapM decodeRow
  let receipts ← (← (← json.getObjVal? "receipts").getArr?).toList.mapM Span.decodeReceipt
  if !Span.wellFormed (rows.map (·.algebra)) receipts then throw "duplicate registry identity"
  return (rows, receipts)
end GP50.ScopedSpan
