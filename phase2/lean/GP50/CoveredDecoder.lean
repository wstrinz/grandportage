import GP50.CoveredSpan
import GP50.ScopedDecoder
namespace GP50.CoveredSpan
open Lean GP50.Decoder
def decodeRule (json : Json) : Except String Rule := do
  exactFields json ["name", "destination", "branches"]
  return ⟨← (← json.getObjVal? "name").getStr?,
    ← (← json.getObjVal? "destination").getNat?,
    ← (← (← json.getObjVal? "branches").getArr?).toList.mapM Json.getNat?⟩
def decode (text : String) : Except String (List ScopedSpan.Row × List Span.Receipt × List Rule) := do
  let json ← parseUnique text
  exactFields json ["schema_version", "clauses", "receipts", "rules"]
  if (← (← json.getObjVal? "schema_version").getNat?) != 3 then throw "unsupported cover registry schema"
  let rows ← (← (← json.getObjVal? "clauses").getArr?).toList.mapM ScopedSpan.decodeRow
  let receipts ← (← (← json.getObjVal? "receipts").getArr?).toList.mapM Span.decodeReceipt
  let rules ← (← (← json.getObjVal? "rules").getArr?).toList.mapM decodeRule
  if !Span.wellFormed (rows.map (·.algebra)) receipts ||
      (rules.map (·.name)).eraseDups.length != rules.length then throw "duplicate registry identity"
  return (rows, receipts, rules)
end GP50.CoveredSpan
