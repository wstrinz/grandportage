import LRATCatcher.Reflect

/-!
  `lrat_decide`: the solver is invoked at elaboration time (cadical, or
  `LRATCATCHER_SOLVER`; `--no-factor` added for cadical ≥ 3 automatically —
  under `lake` the toolchain-bundled cadical shadows the system one).
  Instance: the R(3,3) ≤ 6 encoding (instant). Native mode carries the
  per-theorem `native_decide` axiom (kernel mode is not in the GP rc3 port).
-/

namespace LRATCatcher.Tests

lrat_decide r33Decide "examples/ramsey/r33_6.cnf"

#print axioms r33Decide

end LRATCatcher.Tests
