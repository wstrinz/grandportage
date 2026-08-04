/-
# Unit-coefficient affine coordinate normalization

A solved affine equation can be normalized to a zero pivot by a coordinate
translation. The runtime constructs concrete polynomial maps by subtracting
and adding a pivot-independent solution; its ring-isomorphism verifier checks
the two ideal pullbacks and both round trips. This file states the semantic
contract those checks must earn without importing an algebra library.
-/

import GrandPortage.MappedEquivalence

namespace GrandPortage

universe u v

structure AffineCoordinatePoint (R : Type u) (Tail : Type v) where
  pivot : R
  tail : Tail

/-- Semantic obligations for one affine coordinate translation. Runtime
`forwardPivot` is `x - solution(tail)` and `inversePivot` is
`x + solution(tail)`; keeping the laws explicit mirrors translation
validation of the concrete polynomial maps. -/
structure AffineTranslation (R : Type u) (Tail : Type v) where
  zero : R
  solution : Tail -> R
  forwardPivot : R -> Tail -> R
  inversePivot : R -> Tail -> R
  left_inv : forall pivot tail,
    inversePivot (forwardPivot pivot tail) tail = pivot
  right_inv : forall pivot tail,
    forwardPivot (inversePivot pivot tail) tail = pivot
  normalized : forall pivot tail,
    forwardPivot pivot tail = zero <-> pivot = solution tail


def affineForward
    (translation : AffineTranslation R Tail) :
    AffineCoordinatePoint R Tail -> AffineCoordinatePoint R Tail :=
  fun point => {
    pivot := translation.forwardPivot point.pivot point.tail
    tail := point.tail
  }


def affineInverse
    (translation : AffineTranslation R Tail) :
    AffineCoordinatePoint R Tail -> AffineCoordinatePoint R Tail :=
  fun point => {
    pivot := translation.inversePivot point.pivot point.tail
    tail := point.tail
  }


theorem affineInverse_forward
    (translation : AffineTranslation R Tail)
    (point : AffineCoordinatePoint R Tail) :
    affineInverse translation (affineForward translation point) = point := by
  cases point
  simp [affineForward, affineInverse, translation.left_inv]


theorem affineForward_inverse
    (translation : AffineTranslation R Tail)
    (point : AffineCoordinatePoint R Tail) :
    affineForward translation (affineInverse translation point) = point := by
  cases point
  simp [affineForward, affineInverse, translation.right_inv]


def affineTranslatedModel
    (source : Model (AffineCoordinatePoint R Tail))
    (translation : AffineTranslation R Tail) :
    Model (AffineCoordinatePoint R Tail) :=
  fun targetPoint => source (affineInverse translation targetPoint)


/-- A model is pivot-independent when changing only the distinguished affine
coordinate cannot change membership. This is the semantic condition needed
to distinguish a spent solved coordinate from a new compatibility equation. -/
def PivotIndependent
    (source : Model (AffineCoordinatePoint R Tail)) : Prop :=
  forall first second tail,
    source { pivot := first, tail := tail } <->
      source { pivot := second, tail := tail }


/-- Translating a coordinate ignored by the model leaves the model literally
unchanged. In the runtime assay this is used only after the downstream
equation alphabets have been checked to omit the solved pivot. -/
theorem affineTranslatedModel_eq_of_pivotIndependent
    (source : Model (AffineCoordinatePoint R Tail))
    (translation : AffineTranslation R Tail)
    (independent : PivotIndependent source) :
    affineTranslatedModel source translation = source := by
  funext point
  apply propext
  exact independent
    (translation.inversePivot point.pivot point.tail)
    point.pivot
    point.tail


/-- Pivot independence is itself stable under an affine translation of that
pivot. -/
theorem affineTranslation_preserves_pivotIndependent
    (source : Model (AffineCoordinatePoint R Tail))
    (translation : AffineTranslation R Tail)
    (independent : PivotIndependent source) :
    PivotIndependent (affineTranslatedModel source translation) := by
  rw [affineTranslatedModel_eq_of_pivotIndependent source translation
    independent]
  exact independent


def affineTranslationEquivalence
    (source : Model (AffineCoordinatePoint R Tail))
    (translation : AffineTranslation R Tail) :
    MappedEquivalence source (affineTranslatedModel source translation) where
  forward := affineForward translation
  backward := affineInverse translation
  left_inv := affineInverse_forward translation
  right_inv := affineForward_inverse translation
  forward_maps := by
    intro point sourcePoint
    simpa [affineTranslatedModel, affineInverse_forward] using sourcePoint
  backward_maps := by
    intro point translatedPoint
    exact translatedPoint


/-- The normalized pivot is zero exactly when the original point satisfies the
recorded affine equation. -/
theorem affineForward_pivot_eq_zero_iff
    (translation : AffineTranslation R Tail)
    (point : AffineCoordinatePoint R Tail) :
    (affineForward translation point).pivot = translation.zero <->
      point.pivot = translation.solution point.tail := by
  exact translation.normalized point.pivot point.tail

end GrandPortage
