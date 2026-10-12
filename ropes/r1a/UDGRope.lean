import UDGRope.Defs
import UDGRope.Basic
import UDGRope.Rhombus
import UDGRope.Gadgets
import UDGRope.Schade

/-!
Rope R1a: the unit-distance lemmas of Highway 61 Revisited (P1 rhombus, P2 six TU gadgets,
P3 heredity, Schade averaging). Mathlib only: no GP code is imported, and every declaration
depends on at most `propext`, `Classical.choice` and `Quot.sound`. This is the library root of
the standalone Lake package `ropes/r1a` (rope R1a); the sources were developed in GP's binding
package (`binding/GPBinding/UDG/Rope`) and copied here unchanged apart from this docstring.
-/
