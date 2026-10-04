import GPBinding.Binder.Explicit

/-!
The binder's registry entry: a named theorem warrant for an exact canonical statement and scope.
Lean's typechecker enforces the declaration type `Warranted stmt scope`; the binder export checks
axioms and well-formedness and records the binding identities (G1 decision 2).
-/

namespace GPBinding.Binder
open GPProfile

structure Bound where
  name : String
  stmt : Stmt
  scope : Scope
  proof : Warranted stmt scope

end GPBinding.Binder
