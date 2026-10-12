import UDGRope.Defs
import UDGRope.Basic
import UDGRope.Rhombus
import UDGRope.Gadgets
import UDGRope.Schade

/-!
Rope R1a: the unit-distance lemmas of Highway 61 Revisited (P1 rhombus, P2 six TU gadgets,
P3 heredity, Schade averaging). Mathlib only: no GP code is imported, and every declaration
depends on at most `propext`, `Classical.choice` and `Quot.sound`. The directory is laid out
as its own Lake library (`UDGRope`, source directory `GPBinding/UDG/Rope`) so it can move
unchanged into a separate package.
-/
