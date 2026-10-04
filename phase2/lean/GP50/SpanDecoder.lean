import GP50.Decoder
import GP50.BoundReplay
namespace GP50.Span
open Lean GP50.Decoder
private def nat (json : Json) (key : String) : Except String Nat := do
  (← json.getObjVal? key).getNat?
private def str (json : Json) (key : String) : Except String String := do
  (← json.getObjVal? key).getStr?
private def array (json : Json) (key : String) (decode : Json → Except String α) :
    Except String (List α) := do
  (← (← json.getObjVal? key).getArr?).toList.mapM decode

def decodePolynomial (json : Json) : Except String PolyStub.Polynomial := do
  (← json.getArr?).toList.mapM fun term => do
    exactFields term ["exp", "num", "den"]
    let exponent ← nat term "exp"
    let numerator ← (← term.getObjVal? "num").getInt?
    let denominator ← nat term "den"
    if denominator == 0 then throw "zero rational denominator"
    return (exponent, (numerator : Rat) / (denominator : Rat))

def decodeClause (json : Json) : Except String Clause := do
  exactFields json ["key", "version", "binding", "generators", "target"]
  return {
    key := ← nat json "key"
    version := ← nat json "version"
    binding := ← decodeBinding (← json.getObjVal? "binding")
    generators := ← array json "generators" decodePolynomial
    target := ← decodePolynomial (← json.getObjVal? "target") }

def decodeReceipt (json : Json) : Except String Receipt := do
  exactFields json ["name", "claim", "version", "binding", "cofactors"]
  return {
    name := ← str json "name"
    claim := ← nat json "claim"
    version := ← nat json "version"
    binding := ← decodeBinding (← json.getObjVal? "binding")
    cofactors := ← array json "cofactors" decodePolynomial }

def decodeRegistry (text : String) : Except String (List Clause × List Receipt) := do
  let json ← parseUnique text
  exactFields json ["schema_version", "clauses", "receipts"]
  if (← nat json "schema_version") != 1 then throw "unsupported registry schema"
  let clauses ← array json "clauses" decodeClause
  let receipts ← array json "receipts" decodeReceipt
  if !wellFormed clauses receipts then throw "duplicate registry identity"
  return (clauses, receipts)
end GP50.Span
