/- Executable, non-authoritative comparison with grandportage.field.
Run through scripts/check_atlas_parity.py after lake build. -/
import GrandPortage.Atlas

open GrandPortage.Atlas

def fields : List ConcreteField :=
  [.q, .r, .c, .primeField 2, .primeField 3, .primeField 5, .primeField 7]

def fieldName : ConcreteField → String
  | .q => "Q"
  | .r => "R"
  | .c => "C"
  | .primeField p => s!"F_{p}"

def aboutName : About → String
  | .concrete f => fieldName f
  | .anyOrdered => "ANY_ORDERED"
  | .anyChar0 => "ANY_CHAR_0"

def reachName : Reach → String
  | .none => "NONE"
  | .ordered => "ORDERED"
  | .char0 => "CHAR_0"
  | .fieldSpecific f => "FIELD_SPECIFIC:" ++ fieldName f

def main : IO Unit := do
  let reaches := [.none, .ordered, .char0] ++ fields.map Reach.fieldSpecific
  let targets := fields.map About.concrete ++ [.anyOrdered, .anyChar0]
  for reach in reaches do
    for target in targets do
      IO.println s!"reach\t{reachName reach}\t{aboutName target}\t{instantiate reach target}"
  for source in fields do
    for target in fields do
      IO.println s!"extension\t{fieldName source}\t{fieldName target}\t{concreteExtension source target}"
