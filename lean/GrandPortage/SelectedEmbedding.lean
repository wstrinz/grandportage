/-
# Selected structure is an independent predicate-transport premise

Kernel epoch 12 retains selected embedding identity for PREDICATE transport
while Python adds explicit field-context and checked-reach judgments.
It is not a fifth identity-rewriting gate: it says that a map preserving the
abstract carrier may still fail to preserve extra structure read by a claim.
-/

namespace GrandPortage

/-- The runtime kernel epoch modeled by this shadow. Python CI reads this exact
declaration so a future runtime epoch cannot advance silently. -/
def modeledKernelEpoch : Nat := 12

/-- A model-side validity context may select extra structure independently of
certificate scope. Keeping this separate prevents EMPTY-certificate stability
from being conflated with embedding-sensitive predicate meaning. -/
structure StructureContext (Structure : Type) where
  selected : Option Structure

/-- The epoch-11 gate: copied structure-sensitive syntax needs equal selected
payloads. Omission on both endpoints is the historical abstract case. -/
def SelectedStructureIdentity {Structure : Type}
    (source target : StructureContext Structure) : Prop :=
  source.selected = target.selected

theorem selectedStructureIdentity_refl {Structure : Type}
    (context : StructureContext Structure) :
    SelectedStructureIdentity context context := rfl

inductive QuadraticRoot where
  | plus
  | minus
deriving DecidableEq

def conjugate : QuadraticRoot -> QuadraticRoot
  | .plus => .minus
  | .minus => .plus

theorem conjugate_involutive (root : QuadraticRoot) :
    conjugate (conjugate root) = root := by
  cases root <;> rfl

/-- The two-point Q(sqrt 2) shadow: a ring automorphism may exchange the two
roots, while a predicate that reads the chosen root is not invariant. -/
def AtSelectedRoot (selected : QuadraticRoot) : QuadraticRoot -> Prop :=
  fun point => point = selected

theorem conjugation_breaks_selected_predicate :
    AtSelectedRoot .plus .plus ∧
    Not (AtSelectedRoot .plus (conjugate .plus)) := by
  constructor
  · rfl
  · intro impossible
    cases impossible

/-- When selected payloads are identical, copying an embedding-sensitive
predicate at the literal identity point map changes no proposition. -/
theorem identical_selection_copy_safe
    {Point : Type} (predicate : Point -> Prop) (point : Point) :
    predicate (id point) <-> predicate point := Iff.rfl

/-- With no selected payload at either endpoint the epoch-11 gate recovers the
historical abstract-model case. -/
theorem omitted_selection_is_identical {Structure : Type} :
    SelectedStructureIdentity
      (StructureContext.mk (Structure := Structure) none)
      (StructureContext.mk (Structure := Structure) none) := rfl

end GrandPortage
