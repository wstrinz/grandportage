/- Serialize the actual expressions appearing in sample_derivation.
The Python gate normalizes and compares them with the graph test fixture. -/
import Lean
import GrandPortage.CertificateInterpreter

open GrandPortage.CertificateInterpreter

def render : Expr → String
  | .zero => "0"
  | .one => "1"
  | .var i => if i == 0 then "x" else s!"x{i}"
  | .add a b => s!"({render a})+({render b})"
  | .mul a b => s!"({render a})*({render b})"
  | .neg a => s!"-({render a})"

def main : IO Unit := do
  let value := Lean.Json.mkObj [
    ("method", Lean.toJson "rational_sos_cofactor_v1"),
    ("ring_vars", Lean.toJson (["x"] : List String)),
    ("generators", Lean.toJson (sample.terms.map fun p => render p.2)),
    ("squares", Lean.toJson (sample.squares.map render)),
    ("cofactors", Lean.toJson (sample.terms.map fun p => render p.1))]
  IO.println value.compress
