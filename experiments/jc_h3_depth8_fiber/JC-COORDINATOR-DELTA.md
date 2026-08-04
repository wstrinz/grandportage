# JC coordinator delta: depth-eight first-order fiber

Grand Portage now independently freezes and scopes the landed
`f2_h3_straggler_zero_block_composition` result.

## Supported wording

Conditional on P1..P5, S2, the pin, `c5_7 != 0`, and H8, the rotated
`Omega_comb` obstruction is nonzero at the exact landed L-valued base witness.
Because it is independent of the free `c8_5` coordinate and `c7_4` is solved
affinely by the zero-block equation, the **entire `c8_5` fiber over that one
base witness has no compatible first-order depth-eight point**.

## Required open wording

- the Galois-conjugate witness has not been replayed;
- all other base directions and the rest of the 12-dimensional survivor are
  open;
- no sound nonlinear-linearization bridge has been supplied to GP;
- component exclusion, actual-source membership/exclusion, source
  sufficiency, H3, and `(75,125)` remain unauthorized;
- graph effect is `NONE`.

Do not shorten this to “the depth-eight component is empty” or “the landed
witness does not lift nonlinearly.” The checked claim is exactly first-order
fiber incompatibility at one base witness.

## Files

- `experiments/jc_h3_depth8_fiber/adapter.py`
- `fixtures/jc_depth8_fiber/v1.json`
- `review/jc-h3-depth8-fiber-v1.json`
- `lean/GrandPortage/FirstOrderFiber.lean`
