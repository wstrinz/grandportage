# JC H3 `b=0` compatibility class assay

This disposable assay freezes the bounded affine compatibility block for
`Phi_b0_compat` and independently replays it over
`K = QQ[t]/(15*t^3+1)`.

It verifies:

- the wall-wide five-by-five chart determinant is exactly `det5`;
- the Cramer pushforward reconstructs the committed 3,137-term
  `Phi_b0_compat`;
- clearing exponent two is sufficient and exponent one is not;
- the degree-26 resultant and first subresultant are reproduced exactly;
- a quadratic quotient observation sees `Phi_b0_compat` as a unit, hence
  nonzero;
- a nontrivial degree-14 quotient observation sends `Phi_b0_compat` to zero
  while every declared guard remains invertible, hence the source class is not
  a unit.

The resulting class is exactly **nonzero and nonunit**. It is not asserted to
be a nonzerodivisor. The quotient witness is not asserted `K`-rational. No
all-orders, source, H8, H3, `(75,125)`, model-emptiness, or graph authority is
minted.

The later native `compatibility_module/1` rendezvous is also bound by digest
and matches the identical `Phi_b0_compat` commitment. It supplies the semantic
reading that `Phi` generates the principal compatibility ideal of the exact
three-block materialized fiber. GP labels those fiber semantics as consumed
frozen premises; the Cramer transport and quotient observations remain the
parts independently rederived here.

`lean/GrandPortage/RingElementClass.lean` proves the reusable semantic rules
connecting the two checked observations to this exact conclusion.

## Replay

Routine replay uses only the frozen fixture:

```powershell
python experiments\jc_h3_b0_compatibility\adapter.py
```

Check the current sibling JC bindings or rerun the native checker:

```powershell
python experiments\jc_h3_b0_compatibility\adapter.py --check-native-bindings
python experiments\jc_h3_b0_compatibility\adapter.py --native-replay
```

Fixture construction is the only path that imports and executes the native JC
producer:

```powershell
python experiments\jc_h3_b0_compatibility\adapter.py --write-fixture --force
```

Routine exact replay is intentionally substantial (about one minute on the
current development machine) because it recomputes the Cramer and
subresultant determinants rather than trusting their summaries.
