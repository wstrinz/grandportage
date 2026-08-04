# JC actual-source ordered-chain adapter

This isolated adapter reads the frozen native
`f2_h3_q_receipt_probe.json`, translates its exact five top-face polynomials,
and asks GP to replay the landed `(2, 5, 1, 4, 3)` substitution order.

```console
python experiments/jc_h3_source_ladder/adapter.py
```

The default run checks that the generated envelope is byte-identical to the
frozen GP fixture. `--write-fixture` is an explicit maintainer operation for a
reviewed native receipt update. The envelope binds the native file's SHA-256.

The adapter does not import the native Python producer, write `math-stuff`, or
promote any JC ledger. Native extraction and replay stay in JC; GP checks the
composition boundary and preserves its outstanding model-binding authority.

`second_face_adapter.py` is the first normalization-bearing consumer. Literal
v1 replay correctly refuses all five second-face solves: every discrepancy is
a multiple of the landed scalar-gauge equation `15*t^3+1=0`. The v2 envelope
retains that equation as a persistent normalization generator and supplies an
exact cofactor at every step. No generically nonzero expression is inverted.

`authority_adapter.py` is the graph-composition pilot for the top-face chain.
It algebraizes the declared `t` localization by adjoining `GP_INV_t` with
`t*GP_INV_t-1=0`, translates the five pivots to zero, and emits one mapped
`EQUIVALENCE` between the exact initial and normalized quotients. The existing
`verify.ring_iso` checker must still verify both ideal pullbacks and both map
round trips before coordinate-ring authority is current. This construction
does not bind native source extraction or license H3.

The adapter also consumes the v2 second-face fixture. Graph format 4 stores its
`mapped_ring_iso_v1` cofactor envelope, so `verify.ring_iso` can replay both
ideal pullbacks without an expensive Gröbner search. The top face uses an
adjoined inverse coordinate; the second face derives `t^-1=-15*t^2` from its
normalization equation and checks that relation exactly. Review campaigns live
under `review/v0.20/`.
