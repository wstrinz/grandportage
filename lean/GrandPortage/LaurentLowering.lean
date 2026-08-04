/-
# Formal derivative semantics for the Laurent lowering boundary

The runtime checker evaluates finite Laurent straight-line programs. This file
formalizes the coefficient-level meaning of its derivative node and the chart
negative control that motivated the contract. It intentionally does not
formalize parsing, resource bounds, or the polynomial coefficient engine.
-/

namespace GrandPortage

universe u

/-- Extensional coefficient semantics of a Laurent expression. Runtime values
are finite maps; finiteness is an implementation/resource condition, not needed
for the derivative laws below. -/
abbrev LaurentCoefficients (R : Type u) := Int -> R

/-- The formal derivative coefficient at `y^n` is `(n+1) a_(n+1)`.

`integerScale` is explicit because this development is Mathlib-free. Runtime
instantiates it with exact multiplication by an integer in the coefficient
ring. -/
def formalLaurentDerivative
    (integerScale : Int -> R -> R)
    (f : LaurentCoefficients R) :
    LaurentCoefficients R :=
  fun n => integerScale (n + 1) (f (n + 1))

def addLaurent
    (add : R -> R -> R)
    (f g : LaurentCoefficients R) :
    LaurentCoefficients R :=
  fun n => add (f n) (g n)

def shiftLaurent (shift : Int) (f : LaurentCoefficients R) :
    LaurentCoefficients R :=
  fun n => f (n - shift)

def scaleLaurent
    (scale : R -> R)
    (f : LaurentCoefficients R) :
    LaurentCoefficients R :=
  fun n => scale (f n)

/-- Formal differentiation is additive when integer scaling distributes over
coefficient addition. This is the semantic contract behind an `add` followed
by a `derivative` node. -/
theorem formalLaurentDerivative_add
    (integerScale : Int -> R -> R)
    (add : R -> R -> R)
    (distributes :
      forall n a b, integerScale n (add a b) =
        add (integerScale n a) (integerScale n b))
    (f g : LaurentCoefficients R) :
    formalLaurentDerivative integerScale (addLaurent add f g) =
      addLaurent add
        (formalLaurentDerivative integerScale f)
        (formalLaurentDerivative integerScale g) := by
  funext n
  exact distributes (n + 1) (f (n + 1)) (g (n + 1))

def LaurentSupportedAtOrAbove
    (zero : R) (lower : Int) (f : LaurentCoefficients R) : Prop :=
  forall n, n < lower -> f n = zero

/-- Multiplying by `y^shift` clears every negative exponent exactly when the
input support starts at `-shift` or above. This is the semantic precondition
checked before a runtime Laurent value is exported as an ordinary polynomial. -/
theorem shiftLaurent_clears_negative_support
    (zero : R) (shift : Int) (f : LaurentCoefficients R)
    (supported : LaurentSupportedAtOrAbove zero (-shift) f) :
    LaurentSupportedAtOrAbove zero 0 (shiftLaurent shift f) := by
  intro n negative
  exact supported (n - shift) (by omega)

/-- One common clearing shift preserves a checked Laurent equality and makes its
left side polynomial-supported. Equality then gives the same support fact for
the right side. This is the semantic composition used by the runtime export. -/
theorem equalLaurent_clearing_export
    (zero : R) (shift : Int)
    {left right : LaurentCoefficients R}
    (supported : LaurentSupportedAtOrAbove zero (-shift) left)
    (equal : left = right) :
    LaurentSupportedAtOrAbove zero 0 (shiftLaurent shift left) ∧
      shiftLaurent shift left = shiftLaurent shift right := by
  constructor
  · exact shiftLaurent_clears_negative_support zero shift left supported
  · rw [equal]
/-- Equality of checked Laurent coefficient functions survives a declared
monomial shift and coefficient scaling. This is the small semantic fact used
when a later contract clears a declared monomial/guard. -/
theorem laurentEquality_survives_shift_and_scale
    (scale : R -> R) (shift : Int)
    {left right : LaurentCoefficients R}
    (equal : left = right) :
    scaleLaurent scale (shiftLaurent shift left) =
      scaleLaurent scale (shiftLaurent shift right) := by
  rw [equal]

/-! ## The rows 7--8 chart negative control

Take the legal symbolic datum `G = y^-5` (the `g5 = 1, g2 = 0` instance).
Then the depressed-chart x^1 right-hand side `6*y^2*G` has coefficient `6`
at `y^-3`, so it cannot be the covered-chart zero right-hand side.
-/

def chartControlG : LaurentCoefficients Int :=
  fun n => if n = -5 then 1 else 0

def chartControlDepressedRhs : LaurentCoefficients Int :=
  scaleLaurent (fun coefficient => 6 * coefficient)
    (shiftLaurent 2 chartControlG)

def chartControlCoveredRhs : LaurentCoefficients Int :=
  fun _ => 0

theorem depressed_chart_rhs_is_not_covered_chart_zero :
    Not (chartControlDepressedRhs = chartControlCoveredRhs) := by
  intro equal
  have coefficient := congrFun equal (-3)
  have impossible : (6 : Int) = 0 := by
    simpa [chartControlDepressedRhs, chartControlCoveredRhs,
      scaleLaurent, shiftLaurent, chartControlG] using coefficient
  omega

end GrandPortage