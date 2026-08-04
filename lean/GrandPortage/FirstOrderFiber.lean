/-
# Scoped first-order fiber obstructions

The live JC depth-eight receipt supplies a scalar obstruction at one base
witness.  The scalar is independent of the remaining fiber coordinate, so a
nonzero value excludes every compatible first-order point in that one fiber.
It does not say anything about fibers over other base points.

The second theorem records the separate, conditional bridge from first-order
incompatibility to nonlinear nonextension.  A concrete campaign may use it
only after supplying a sound linearization map for the nonlinear model.
-/

namespace GrandPortage

universe u v w x

/-- No point in the fiber over `base` satisfies `predicate`. -/
def FiberEmpty {Base : Type u} {Fiber : Type v}
    (predicate : Base -> Fiber -> Prop) (base : Base) : Prop :=
  forall fiber, Not (predicate base fiber)

/-- A nonzero base-only necessary scalar excludes the entire named fiber. -/
theorem fiberEmpty_of_base_obstruction
    {Base : Type u} {Fiber : Type v} {Scalar : Type w}
    [Zero Scalar]
    (compatible : Base -> Fiber -> Prop) (obstruction : Base -> Scalar)
    (base : Base)
    (necessary : forall fiber, compatible base fiber -> obstruction base = 0)
    (nonzero : Not (obstruction base = 0)) :
    FiberEmpty compatible base := by
  intro fiber compatible_point
  exact nonzero (necessary fiber compatible_point)

/--
First-order fiber emptiness excludes nonlinear lifts through the same base
only when a supplied sound linearization maps every such lift into that fiber.
-/
theorem nonlinearFiberEmpty_of_sound_linearization
    {Base : Type u} {Nonlinear : Type v} {Jet : Type w}
    (nonlinear : Base -> Nonlinear -> Prop)
    (firstOrder : Base -> Jet -> Prop)
    (linearize : Nonlinear -> Jet) (base : Base)
    (sound : forall point, nonlinear base point ->
      firstOrder base (linearize point))
    (firstOrderEmpty : FiberEmpty firstOrder base) :
    FiberEmpty nonlinear base := by
  intro point nonlinear_point
  exact firstOrderEmpty (linearize point) (sound point nonlinear_point)

end GrandPortage
