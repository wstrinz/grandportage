import UDGRope.Embeds

/-!
Control (wrong coordinate) for `UDGRope.gadget0_embeds`: this file must fail to elaborate.

It is `gadget0Emb` with one coordinate wrong: vertex 3 at `(-1/2, √3/2)` instead of `(1/2, √3/2)`.
The points stay distinct and the edge 0 3 stays unit, but the edges 2 3 and 3 4 have squared
lengths 2 and 3, so the edge proof must fail there, and only there: `REPRODUCE` expects exactly two
errors, both `linarith failed`. This file is not part of any Lake library.
-/

noncomputable section

namespace UDGRope.Fail
open UDGRope

def gadget0XBad : Fin 6 → ℝ := ![0, 0, 1 / 2, -1 / 2, 1, 1]

def gadget0EmbBad : gadget0.UnitDistEmbedding ℝ² :=
  embOf _ gadget0XBad gadget0Y (ptsOf_injective (by coords_inj gadget0XBad gadget0Y))
    (by unit_edges gadget0XBad gadget0Y)

end UDGRope.Fail
