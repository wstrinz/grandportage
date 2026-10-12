import GPProfile.Real.Sections

/-!
Build-time checks (`#guard`) of C6 section and output-membership receipts, with adversarial
controls: a wrong section, a wrong stated substitution result (detached), a missing row, a false
membership, an altered proof under a previous binding, and rows offered for an empty output.
-/

namespace GPProfile.Real.SectionsTests
open Lean GPProfile GPProfile.Real

/-- `some accepted`, or `none` when the inputs do not elaborate or the plan does not run. -/
private def verdict (fam : Json → Except String Plan3) (inputs : String) : Option Bool :=
  match Json.parse inputs >>= fam >>= Plan3.run with
  | .ok o => some o.accepted
  | .error _ => none

private def sec (section_ rows : String) (previous : String := "null") : String :=
  "{\"source\": {\"field\": \"Q\", \"variables\": [\"y\", \"x\"], \"equations\": [\"y*x-1\", \"y^2-x\"]}," ++
  "\"target\": {\"field\": \"Q\", \"variables\": [\"x\"], \"equations\": [\"x^3-1\"]}," ++
  s!"\"eliminated\": [\"y\"], \"section\": \{\"y\": \"{section_}\"}, \"proof_rows\": {rows}," ++
  s!"\"previously_bound_rows\": {previous}}"

private def row (eq res cof : String) : String :=
  s!"\{\"equation\": \"{eq}\", \"substitution_result\": \"{res}\", \"cofactors\": [\"{cof}\"]}"

private def goodRows : String := s!"[{row "y*x-1" "x^3-1" "1"}, {row "y^2-x" "x^4-x" "x"}]"

-- GP-X255: exact section identities.
#guard verdict sectionFamily (sec "x^2" goodRows) == some true
-- GP-X257: a false row; GP-X256: the same, with the valid rows as a previous binding.
private def badRows : String := s!"[{row "y*x-1" "x^3-1" "0"}, {row "y^2-x" "x^4-x" "x"}]"
#guard verdict sectionFamily (sec "x^2" badRows) == some false
#guard verdict sectionFamily (sec "x^2" badRows goodRows) == some false
-- A wrong section: y ↦ x sends y*x - 1 to x² - 1, outside (x³ - 1).
#guard verdict sectionFamily (sec "x" s!"[{row "y*x-1" "x^2-1" "1"}, {row "y^2-x" "x^2-x" "0"}]") == some false
-- A stated result other than the composition detaches its receipt, even with true arithmetic.
#guard verdict sectionFamily (sec "x^2" s!"[{row "y*x-1" "x^3-1" "1"}, {row "y^2-x" "x^4" "x"}]") ==
  some false
-- A source equation with no row has no support.
#guard verdict sectionFamily (sec "x^2" s!"[{row "y*x-1" "x^3-1" "1"}]") == some false

private def out (eqs rows : String) (previous : String := "null") : String :=
  "{\"source\": {\"field\": \"Q\", \"variables\": [\"y\", \"x\"], \"equations\": [\"x\"]}," ++
  s!"\"output\": \{\"field\": \"Q\", \"variables\": [\"x\"], \"equations\": {eqs}}, \"eliminated\": [\"y\"]," ++
  s!"\"membership_rows\": {rows}, \"previously_bound_rows\": {previous}, \"execution_evidence\": \"no_execution\"}"

-- GP-X258, GP-X260/X261, GP-X259, GP-X262.
#guard verdict outputFamily (out "[\"x\"]" "[{\"equation\": \"x\", \"cofactors\": [\"1\"]}]") == some true
#guard verdict outputFamily (out "[\"x\"]" "[{\"equation\": \"x\", \"cofactors\": [\"0\"]}]") == some false
#guard verdict outputFamily (out "[\"x\"]" "[{\"equation\": \"x\", \"cofactors\": [\"0\"]}]"
  "[{\"equation\": \"x\", \"cofactors\": [\"1\"]}]") == some false
#guard verdict outputFamily (out "[]" "[]") == some true
-- An invented output equation (x - 1 is not in (x)) and rows offered for an empty output.
#guard verdict outputFamily (out "[\"x-1\"]" "[{\"equation\": \"x-1\", \"cofactors\": [\"1\"]}]") == some false
#guard verdict outputFamily (out "[]" "[{\"equation\": \"x\", \"cofactors\": [\"1\"]}]") == none

end GPProfile.Real.SectionsTests
