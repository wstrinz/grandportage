# JC source-ladder ordered-chain pilot

`localized_triangular_solve_chain_v1.json` is the first bounded composition
fixture for the actual-source H3 ladder. It starts from the five exact native
top-face polynomials, preserves the landed row order `(2, 5, 1, 4, 3)`, and
checks the pivot coefficients and solved expressions after every prior
substitution. A final sentinel generator uses all five pivots so every
substitution materially changes the ordered state and its fingerprint. The
envelope also binds the SHA-256 of the native JC receipt it was translated
from.

Run it with:

```console
gp verify-localized-triangular-chain \
  --spec fixtures/jc_source_ladder/localized_triangular_solve_chain_v1.json
```

The fixture begins after native JC source extraction. It validates that the
five exact triangular substitutions form the recorded ordered state
transition in `Q[...,t^-1]`. It does not prove that the initial equations were
extracted from the actual source model, bind either endpoint to a GP graph
model, or mint point-equivalence, emptiness, source membership, or H3.

The v1 schema intentionally has no denominator-clearing or normalization
receipt fields. A native chain needing those operations must fail closed until
their exact contracts are added.

`localized_triangular_solve_chain_v2_second_face.json` consumes the landed
second-face receipt. The native polynomialized solutions are not literal
rewrites of the five face equations: their differences are exact multiples of
`15*t^3+1`, the scalar-gauge equation equivalent to `45*t^3=-3`. Version 2
records that persistent normalization generator and one checked cofactor per
step. Altering either the generator or any cofactor refuses replay.
