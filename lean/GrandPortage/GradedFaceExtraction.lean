/-
# Graded face extraction

Selected coefficients of a vanishing source expression are necessary
conditions. They are not sufficient unless coverage is complete. This file
also packages the resulting operation as a total point map, making the two
licensed point transports—and only those transports—available to the runtime
contract.
-/

import GrandPortage.Points

namespace GrandPortage

universe u v w

/-- A coefficient family indexed by the source grading. -/
abbrev CoefficientFamily (Index : Type u) (A : Type v) := Index → A

def CoefficientsVanish {Index : Type u} {A : Type v} [Zero A]
    (coefficients : CoefficientFamily Index A) : Prop :=
  ∀ i, coefficients i = 0

/-- Restrict a coefficient family to the explicitly selected faces. -/
def extractFaces {SourceIndex : Type u} {Face : Type v} {A : Type w}
    (sourceIndex : Face → SourceIndex)
    (coefficients : CoefficientFamily SourceIndex A) :
    CoefficientFamily Face A :=
  fun face => coefficients (sourceIndex face)

/-- Vanishing of the source expression entails every selected face equation. -/
theorem coefficientsVanish_entails_extractedFacesVanish
    {SourceIndex : Type u} {Face : Type v} {A : Type w} [Zero A]
    (sourceIndex : Face → SourceIndex)
    (coefficients : CoefficientFamily SourceIndex A)
    (vanishes : CoefficientsVanish coefficients) :
    CoefficientsVanish (extractFaces sourceIndex coefficients) := by
  intro face
  exact vanishes (sourceIndex face)

inductive TwoCoefficient
  | selected
  | omitted

def selectedOnly : Unit → TwoCoefficient :=
  fun _ => TwoCoefficient.selected

def omittedNonzero : CoefficientFamily TwoCoefficient Nat
  | TwoCoefficient.selected => 0
  | TwoCoefficient.omitted => 1

/-- A proper selection cannot be reflected back to full source vanishing. -/
theorem extractedFacesVanish_do_not_imply_coefficientsVanish :
    CoefficientsVanish (extractFaces selectedOnly omittedNonzero) ∧
      ¬ CoefficientsVanish omittedNonzero := by
  constructor
  · intro face
    cases face
    rfl
  · intro allVanish
    have omitted := allVanish TwoCoefficient.omitted
    simp [omittedNonzero] at omitted

/--
An operation contract for a bounded graded extraction. The lower function
evaluates the declared source template at the retained coefficient faces;
sound is the semantic verification condition discharged by the checker.
-/
structure GradedFaceExtraction
    {Source : Type u} {Faces : Type v}
    (sourceModel : Model Source) (faceModel : Model Faces) where
  lower : Source → Faces
  sound : ∀ point, sourceModel point → faceModel (lower point)

/-- A source witness lowers to a witness of the selected face system. -/
theorem gradedFaceExtraction_hasPoint_along
    {Source : Type u} {Faces : Type v}
    {sourceModel : Model Source} {faceModel : Model Faces}
    (operation : GradedFaceExtraction sourceModel faceModel)
    (sourceHasPoint : HasPoint sourceModel) :
    HasPoint faceModel := by
  obtain ⟨point, valid⟩ := sourceHasPoint
  exact ⟨operation.lower point, operation.sound point valid⟩

/-- Emptiness of the selected face system refutes the source model. -/
theorem gradedFaceExtraction_isEmpty_against
    {Source : Type u} {Faces : Type v}
    {sourceModel : Model Source} {faceModel : Model Faces}
    (operation : GradedFaceExtraction sourceModel faceModel)
    (facesEmpty : IsEmpty faceModel) :
    IsEmpty sourceModel := by
  intro point valid
  exact facesEmpty (operation.lower point) (operation.sound point valid)

end GrandPortage