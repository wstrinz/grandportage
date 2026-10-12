import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.UnitDistance.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym

/-! Control (weaker) for `UDGRope.gadget0_embeds`: Comparator must refuse this solution. -/

/-!
Rope R1a (Highway 61 Revisited G-4): the statement vocabulary of the unit-distance lemmas. This
package imports Mathlib only; every Comparator challenge repeats this file verbatim, so a
statement means exactly what these definitions say.

- `ℝ²` is formal-conjectures' notation (`FormalConjecturesForMathlib/Geometry/2d.lean`):
  `EuclideanSpace ℝ (Fin 2)`, the Euclidean plane.
- `unitDistNum`, `unitDistanceCounts` and `maxUnitDistances` are copied verbatim, not imported,
  from formal-conjectures at `b3f26411f06b0b0ec1923da80b62585f23288d39`
  (`FormalConjecturesForMathlib/Geometry/Metric.lean` and `FormalConjectures/ErdosProblems/90.lean`,
  Apache-2.0): unordered pairs of the finite set (`s.sym2`) at distance 1, so only pairs of
  distinct points count, and `u(n)` is the supremum over `n`-point sets.
- The six gadgets are artwaste's `data/tu-gadgets.json` (`artwasteland/Maths` at `ba1c76fd`,
  `unit-distance-22/research/unit-distance-22/`), same vertex numbers.
-/

namespace UDGRope
open scoped Finset

/-- The Euclidean plane (formal-conjectures' `ℝ²`). -/
scoped notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The number of pairs of points of a finite set `s` in a metric space that are distance 1 apart.
-/
noncomputable def unitDistNum {X : Type*} [MetricSpace X] (s : Finset X) : ℕ :=
  #{p ∈ s.sym2 | dist p.out.1 p.out.2 = 1}

/--
The set of all possible numbers of unit distances for a configuration of $n$ points.
-/
noncomputable def unitDistanceCounts (n : ℕ) : Set ℕ :=
  {unitDistNum points | (points : Finset ℝ²) (_ : points.card = n)}

/--
The **maximum number of unit distances** determined by any set of $n$ points in the plane.
This function is often denoted as $u(n)$ in combinatorics.
-/
noncomputable def maxUnitDistances (n : ℕ) : ℕ :=
  sSup (unitDistanceCounts n)

/-- TU gadget 0; distinguished pair (1, 5). -/
def gadget0 : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet
  {s(0, 1), s(0, 3), s(0, 4), s(1, 2), s(2, 3), s(2, 5), s(3, 4), s(4, 5)}

/-- TU gadget 1; distinguished pair (4, 5). -/
def gadget1 : SimpleGraph (Fin 7) := SimpleGraph.fromEdgeSet
  {s(0, 2), s(0, 3), s(0, 4), s(1, 2), s(1, 3), s(1, 6), s(2, 3), s(2, 4), s(2, 5), s(2, 6), s(5, 6)}

/-- TU gadget 2; distinguished pair (2, 4). -/
def gadget2 : SimpleGraph (Fin 7) := SimpleGraph.fromEdgeSet
  {s(0, 2), s(0, 3), s(0, 4), s(1, 2), s(1, 3), s(1, 6), s(2, 3), s(2, 5), s(2, 6), s(4, 5), s(5, 6)}

/-- TU gadgets 3 and 4; distinguished pairs (3, 7) and (6, 7). -/
def gadget3 : SimpleGraph (Fin 8) := SimpleGraph.fromEdgeSet
  {s(0, 1), s(0, 2), s(0, 6), s(1, 3), s(1, 7), s(2, 3), s(2, 5), s(2, 6), s(3, 4), s(4, 5), s(4, 7),
    s(5, 6)}

/-- TU gadget 5 (gadget 3 without the edge 26); distinguished pair (6, 7). -/
def gadget5 : SimpleGraph (Fin 8) := SimpleGraph.fromEdgeSet
  {s(0, 1), s(0, 2), s(0, 6), s(1, 3), s(1, 7), s(2, 3), s(2, 5), s(3, 4), s(4, 5), s(4, 7), s(5, 6)}

end UDGRope

namespace UDGRope
open scoped Finset

/-- Weakened: an injective point map, with the unit-distance condition on edges dropped. -/
theorem gadget0_embeds : Nonempty (Fin 6 ↪ ℝ²) :=
  ⟨⟨fun i => EuclideanSpace.single 0 ((i : ℕ) : ℝ), fun i j h => by
    simpa [Fin.ext_iff] using congrArg (· 0) h⟩⟩

end UDGRope
