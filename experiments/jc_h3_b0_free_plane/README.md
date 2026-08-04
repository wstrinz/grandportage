# JC H3 `b=0` free-plane exceptional-factor assay

This isolated assay freezes the complete landed 35-object coefficient ledger
for the materialized free plane `(c7_4,c8_5)` on `X_b`. Routine GP replay:

- verifies the four and only four live coefficient rows;
- independently expands their exact `b` and `Delta` factorizations;
- checks that `c8_5` is revived on the wall when `b=0` is omitted;
- checks that `E321` is revived when the S2 relation `Delta=0` is omitted;
- checks the reversible `c9_7 <-> c9_7+(3/2)*c2_3*c7_4` normalization;
- preserves the native distinction between a solved rung value and a ninth
  compatibility equation.

The result is standalone `exceptional_factor_column_v1` evidence with
`graph_effect: NONE`. It does not establish a free-plane component,
irreducibility, all-orders lifting, source sufficiency or membership, H8, H3,
or a `(75,125)` status change.

The first open obligation is deliberately retained: compute only the six
`c8_5` and `c9_7` coefficients in the depth-eight boundary triple
`E[2,19], E[3,20], E[4,22]` on `X_b`.

```powershell
python experiments\jc_h3_b0_free_plane\adapter.py
python experiments\jc_h3_b0_free_plane\adapter.py --check-native-bindings
python experiments\jc_h3_b0_free_plane\adapter.py --native-replay
```

Fixture construction is the only path that imports and executes the native
checker:

```powershell
python experiments\jc_h3_b0_free_plane\adapter.py --write-fixture --force
```
