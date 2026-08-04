# JC H3 depth-eight fiber scope assay

This experiment freezes the landed straggler/zero-block composition receipt and
checks one deliberately narrow conclusion:

> Conditional on P1..P5, S2, the pin, `c5_7 != 0`, and H8, no compatible
> first-order depth-eight point exists anywhere along the free `c8_5` fiber
> over the one exact landed L-valued base witness.

The native composition solves `c7_4` affinely, rotates the cokernel, and
computes an exact nonzero `Omega_comb` that does not depend on `c8_5`. The Lean
theorem `fiberEmpty_of_base_obstruction` supplies the generic inference from
that base-only nonzero necessary scalar to emptiness of the named fiber.

## Authority boundary

This is `first_order_fiber_obstruction_v1` standalone evidence with
`graph_effect: NONE`. It does **not** establish:

- nonlinear nonextension (the sound-linearization premise is not supplied);
- the unreplayed Galois conjugate;
- any other base direction or the full 12-dimensional survivor;
- component emptiness, source membership or exclusion, source sufficiency;
- H3, `(75,125)`, depth-nine authority, or any graph promotion.

This is the point of the assay: it preserves a result that is stronger than a
single pinned-point calculation and weaker than a component theorem.

## Replay

```powershell
python experiments\jc_h3_depth8_fiber\adapter.py
python experiments\jc_h3_depth8_fiber\adapter.py --check-native-bindings
python experiments\jc_h3_depth8_fiber\adapter.py --native-replay
```

The default replay uses only the frozen fixture. Native binding checks and the
24/24 producer replay are explicit opt-ins.
