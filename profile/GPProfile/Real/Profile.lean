import GPProfile.Algebra
import GPProfile.Real.RealPoint
import GPProfile.Real.NumberField

/-!
The 3b profile's executable operations ([3B-PROFILE-DESIGN.md](../../../docs/3B-PROFILE-DESIGN.md)).
One profile sums three statement families over field contexts:

- `alg s`: a 3a statement at a 3a scope, true in every field of the context's characteristic
  (3a's meaning, reused unchanged);
- `orderFree s`: a 3a statement read in the context field itself, at `semireal` or `real` scope;
- `real r e`: a real system with sign atoms, empty or nonempty, at `real` scope (the field ℝ);
- `nf p`: a point of a finite algebra over a number field `ℚ[t]/(m)` (post-G2 §5), at an `alg`
  scope inside characteristic 0; it quantifies over the roots of `m` (C4, C5).

A fourth form, `realCover r bs`, is 3a's cover kind for real systems, at `real` scope.

Scopes order within a family, plus `real ≤ semireal` and `ratField ≤ semireal` (ℝ and ℚ are
semireal). No scope relates the `alg`
family to the real ones, so a ℂ or characteristic-0 claim never narrows into them (GP-A10-C,
GP-X343, GP-X345).
-/

namespace GPProfile.Real

deriving instance DecidableEq for RealSys
deriving instance Repr for RealSys

/-- A real-family claim says its system has no point, or some point. -/
inductive Exist where
  | empty
  | nonempty
  deriving Repr, DecidableEq

/-- A branch of a real-family cover: equations, guards and sign atoms over the parent's
variables (3a's cover branches, with sign atoms). -/
structure RBranch where
  eqs : List Sparse
  guards : List Sparse
  signs : List (Sparse × Int)
  deriving Repr, DecidableEq

/-- A branch read as a system over the parent's variables. -/
def RealSys.branch (r : RealSys) (b : RBranch) : RealSys := ⟨r.vars, b.eqs, b.guards, b.signs⟩

inductive Stmt3 where
  | alg (s : Stmt)
  | orderFree (s : Stmt)
  | real (r : RealSys) (e : Exist)
  | nf (p : NFPoint)
  /-- Every point of `r` is a point of one of the branches (3a's `cover` kind, real family). -/
  | realCover (r : RealSys) (branches : List RBranch)
  deriving Repr, DecidableEq

inductive Scope3 where
  | alg (sc : Scope)
  | semireal
  | real
  /-- The field ℚ itself (a field isomorphic to ℚ). -/
  | ratField
  deriving Repr, DecidableEq

/-- Within the real family `real ≤ semireal` and `ratField ≤ semireal` (ℝ and ℚ are semireal).
`ratField` is unrelated to `real` and to every `alg` scope: an exclusion over ℚ never reaches a
characteristic-0 claim by narrowing (GP-X56). -/
def Scope3.le : Scope3 → Scope3 → Bool
  | .alg a, .alg b => a.le b
  | .semireal, .semireal => true
  | .real, .real => true
  | .real, .semireal => true
  | .ratField, .ratField => true
  | .ratField, .semireal => true
  | _, _ => false

/-- The same system, as `contra` compares it. -/
def sameSys (a b : Stmt) : Bool := a.vars == b.vars && a.eqs == b.eqs && a.guards == b.guards

/-- Contradictions. `alg` keeps 3a's table (sound for 3a's characteristic-closed meaning); the
real families are read in one field, where only EMPTY against NONEMPTY of one system is sound
(3a's table also pairs NOT_IN_IDEAL(1) with EMPTY, which over ℚ alone both hold for x² + 1). -/
def Stmt3.contra : Stmt3 → Stmt3 → Bool
  | .alg a, .alg b => GPProfile.contra a b
  | .orderFree a, .orderFree b =>
    sameSys a b && ((a.kind == .empty && b.kind == .nonempty) || (a.kind == .nonempty && b.kind == .empty))
  | .real a ea, .real b eb => decide (a = b) && ea != eb
  | _, _ => false

def ops3 : GP50.Semantic.ProfileOps where
  Stmt := Stmt3
  Scope := Scope3
  same a b := decide (a = b)
  same_sound := by intro a b h; exact of_decide_eq_true h
  le := Scope3.le
  contra := Stmt3.contra

/-! The refusing controls, as executable facts: nothing narrows from `alg` into the real family. -/
example : Scope3.le (.alg Scope.char0Only) .semireal = false := rfl
example : Scope3.le (.alg Scope.char0Only) .real = false := rfl
example : Scope3.le .semireal .real = false := rfl
example : Scope3.le .real .semireal = true := rfl
example : Scope3.le .ratField .semireal = true := rfl
example : Scope3.le .ratField (.alg Scope.char0Only) = false := rfl
example : Scope3.le .ratField .real = false := rfl

end GPProfile.Real
