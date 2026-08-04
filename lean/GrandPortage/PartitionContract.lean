/-
# First-class contracts for n-ary case splits

An operation contract relates one source to one target. A partition contract
instead produces an indexed family whose useful theorem mentions every branch
at once. This file makes that distinction structural rather than prose.
-/

import GrandPortage.Exhaustive

namespace GrandPortage

universe u v w

structure PartitionContract (Params : Type u) (Point : Type v) where
  Index : Type w
  branch : Params -> Model Point -> Index -> Model Point
  precondition : Params -> Model Point -> Prop
  sound :
    forall params parent,
      precondition params parent ->
      Covers parent (branch params parent)

inductive BinarySide where
  | left
  | right
  deriving DecidableEq

structure BinarySplitParams (Point : Type v) where
  leftZero : Point -> Prop
  rightZero : Point -> Prop

def binarySplitBranch
    (params : BinarySplitParams Point)
    (parent : Model Point) :
    BinarySide -> Model Point
  | .left => fun point => parent point ∧ params.leftZero point
  | .right => fun point => parent point ∧ params.rightZero point

def BinarySplitPrecondition
    (params : BinarySplitParams Point)
    (parent : Model Point) : Prop :=
  forall point, parent point ->
    params.leftZero point ∨ params.rightZero point

theorem binarySplit_covers
    (params : BinarySplitParams Point)
    (parent : Model Point)
    (split : BinarySplitPrecondition params parent) :
    Covers parent (binarySplitBranch params parent) := by
  intro point parentPoint
  cases split point parentPoint with
  | inl leftZero =>
      exact ⟨BinarySide.left, parentPoint, leftZero⟩
  | inr rightZero =>
      exact ⟨BinarySide.right, parentPoint, rightZero⟩

def binarySplitContract (Point : Type v) :
    PartitionContract (BinarySplitParams Point) Point where
  Index := BinarySide
  branch := binarySplitBranch
  precondition := BinarySplitPrecondition
  sound := binarySplit_covers

end GrandPortage
