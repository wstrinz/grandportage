# JC H3 `b=0` transported depth-eight block

This assay composes the previously verified `c9_7` affine pivot with the
landed coefficient-only depth-eight receipt. It independently checks:

- all nine raw `c7_4`, `c8_5`, and `c9_7` coefficient commitments;
- the forced sign and exact native commitment for the transported derivative
  `D7=d/dc7_4-(3/2)c2_3*d/dc9_7`;
- the exact anti-diagonal `3x2` block on `X_b`;
- its three minors, constant rank two, and left syzygy `(c2_3,0,2)`;
- the symbolic identity
  `det[M8|r8]=-(25/16)c2_3^5*c3_5*t*(c2_3*r8_1+2*r8_3)`.

The native derivative-table chain-rule assembly includes earlier solved-
coordinate sensitivities and is recorded as consumed frozen semantics. GP does
not pretend the six raw direct coefficients alone reconstruct `M8`.

The first result is standalone `affine_fiber_block_v1` evidence with graph
effect `NONE`. It says that the two transported coordinates are determined in
the named **necessary** extension block and that one residual compatibility
remains.

The bounded follow-on receipt has now landed and is replayed by
`depth8_residual_adapter.py`. GP independently recomputes the two exported
residual bodies and the exact 709-term
`Psi8=c2_3*r8_1+2*r8_3`; the middle residual remains deliberately absent
because the checked syzygy has zero middle coordinate. It then replays the
constrained block substitution, retains the full exceptional-factor ledger,
and reproduces the 4,123-term base polynomial `Omega8`. Exact arithmetic in
the frozen degree-14 quotient proves `Omega8` is a unit there.

This excludes only that finite compatible witness. It does not establish
component-wide emptiness, decide the off-slice zero locus, prove complete-fiber
or source equivalence, reach depth nine, or change H8, H3, or `(75,125)`.
Graph effect remains `NONE`.

```powershell
python experiments\jc_h3_b0_free_plane\depth8_adapter.py
python experiments\jc_h3_b0_free_plane\depth8_adapter.py --check-native-bindings
python experiments\jc_h3_b0_free_plane\depth8_adapter.py --native-replay
python experiments\jc_h3_b0_free_plane\depth8_residual_adapter.py
python experiments\jc_h3_b0_free_plane\depth8_residual_adapter.py --check-native-bindings
python experiments\jc_h3_b0_free_plane\depth8_residual_adapter.py --native-replay
```

The original block fixture construction executes its native checker. The
follow-on constructor freezes the byte-bound certificates and embedded replay
inputs without executing a native checker:

```powershell
python experiments\jc_h3_b0_free_plane\depth8_adapter.py --write-fixture --force
python experiments\jc_h3_b0_free_plane\depth8_residual_adapter.py --write-fixture --force
```
