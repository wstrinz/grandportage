/-
# Ring-element class evidence

The JC `b = 0` compatibility assay needs two elementary but importantly
different semantic rules.  A zero-preserving observation that sees a nonzero
value proves the source element is nonzero.  A multiplicative, zero/one-
preserving observation into a nontrivial target that sends the element to zero
proves the source element is not a unit.

The runtime is responsible for checking the concrete quotient-algebra maps.
These theorems state only the small authority earned by those checks; neither
one says that the element is a nonzerodivisor or that its zero locus has any
particular geometry.
-/

namespace GrandPortage

universe u v

/-- A deliberately foundation-light notion of a two-sided unit. -/
def IsTwoSidedUnit {R : Type u} [One R] [Mul R] (x : R) : Prop :=
  Exists fun inverse => x * inverse = 1 ∧ inverse * x = 1

/-- A zero-preserving observation with nonzero output reflects nonzeroness. -/
theorem nonzero_of_observed_nonzero
    {R : Type u} {S : Type v} [Zero R] [Zero S]
    (observe : R -> S) (preservesZero : observe 0 = 0)
    (x : R) (observedNonzero : Not (observe x = 0)) :
    Not (x = 0) := by
  intro sourceZero
  apply observedNonzero
  rw [sourceZero]
  exact preservesZero

/--
An element mapping to zero in a nontrivial multiplicative target cannot have a
two-sided inverse.  Only the right-inverse half is needed, but the symmetric
definition matches the usual unit concept and keeps the statement reusable.
-/
theorem notUnit_of_observed_zero
    {R : Type u} {S : Type v}
    [Zero R] [One R] [Mul R] [Zero S] [One S] [Mul S]
    (observe : R -> S)
    (preservesOne : observe 1 = 1)
    (preservesMul : forall left right,
      observe (left * right) = observe left * observe right)
    (zeroMul : forall value : S, 0 * value = 0)
    (targetNontrivial : Not ((0 : S) = 1))
    (x : R) (observedZero : observe x = 0) :
    Not (IsTwoSidedUnit x) := by
  intro sourceUnit
  rcases sourceUnit with ⟨inverse, rightInverse, _leftInverse⟩
  apply targetNontrivial
  calc
    (0 : S) = observe x * observe inverse := by
      rw [observedZero]
      symm
      exact zeroMul (observe inverse)
    _ = observe (x * inverse) := by
      symm
      exact preservesMul x inverse
    _ = observe 1 := by rw [rightInverse]
    _ = 1 := preservesOne

/-- The exact conjunction licensed by the two independent observations. -/
theorem neitherZeroNorUnit_of_observations
    {R : Type u} {SNonzero : Type v} {SZero : Type v}
    [Zero R] [One R] [Mul R]
    [Zero SNonzero]
    [Zero SZero] [One SZero] [Mul SZero]
    (nonzeroObservation : R -> SNonzero)
    (nonzeroPreservesZero : nonzeroObservation 0 = 0)
    (zeroObservation : R -> SZero)
    (zeroPreservesOne : zeroObservation 1 = 1)
    (zeroPreservesMul : forall left right,
      zeroObservation (left * right) =
        zeroObservation left * zeroObservation right)
    (zeroMul : forall value : SZero, 0 * value = 0)
    (zeroTargetNontrivial : Not ((0 : SZero) = 1))
    (x : R)
    (seenNonzero : Not (nonzeroObservation x = 0))
    (seenZero : zeroObservation x = 0) :
    Not (x = 0) ∧ Not (IsTwoSidedUnit x) := by
  constructor
  · exact nonzero_of_observed_nonzero nonzeroObservation
      nonzeroPreservesZero x seenNonzero
  · exact notUnit_of_observed_zero zeroObservation zeroPreservesOne
      zeroPreservesMul zeroMul zeroTargetNontrivial x seenZero

end GrandPortage
