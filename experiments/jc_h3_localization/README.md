# JC H3 localization adapter spike

This disposable lane translates the frozen H3 graded-eliminator pivot controls
into GP's backend-neutral `localization_membership_v1` evidence. It does not
edit `math-stuff`, a campaign graph, or GP's semantic kernel.

Run from the GP repository root:

```console
python experiments/jc_h3_localization/adapter.py \
  experiments/jc_h3_localization/q-control.json
python experiments/jc_h3_localization/adapter.py \
  experiments/jc_h3_localization/p-control.json
python experiments/jc_h3_localization/adapter.py --self-test
python experiments/jc_h3_localization/q_live_replay.py
python experiments/jc_h3_localization/q_live_replay_all.py
python experiments/jc_h3_localization/rows78_bare_family.py
python experiments/jc_h3_localization/rows78_bare_family.py --graph-bound
```

The live q replay imports the frozen JC producer read-only from the sibling
`math-stuff` repository. It reconstructs exact `sparse_polynomial_v1` equations
without asking the JC publication to serialize its large display expressions.
The batch run checks all 12 pivots independently and never performs dense
back-substitution. At the 2026-07-30 integration head, all 12 return
`VERIFIED_LOCALIZATION_MEMBERSHIP`: equations range from 163 to 2,011 terms,
their pivots are `c9_0` through `c9_11`, and every coefficient is `10*t`.

Those verdicts license only the individual identities in `Q[...,q^-1,t^-1]`.
They do not license the ordered elimination chain, ambient identities,
actual-source membership, a p-chart result, or H3.

The rows 7--8 replay checks the two bare-family unit coefficients from the JC
source packet. The q certificate proves `q^3*t^2` lies in the ideal generated
by `-5*q^3*t^2`; the p certificate proves `p^4*t^2` lies in the ideal generated
by `5*p^4*t^2`. Because the corresponding chart variables and `t` are guards,
each report certifies `1=0` in its declared localized quotient. Lean theorem
`localized_unit_ideal_has_no_point` proves the point-level consequence. The
ordinary run retains the narrower standalone identity licence. With
`--graph-bound`, the script creates a disposable epoch-10 campaign for each
chart, runs real Singular through `verify.localized_unit_ideal`, reloads the
fingerprint-bound proof, and confirms local `EMPTY` authority with no parent
emptiness. The temporary campaigns and artifacts are removed on exit.

The bracket-receipt promotion remains a typed open interface, not a failed
calculation. Its source expressions involve Laurent supports, derivatives, and
monomial clearing before ordinary coefficient comparison. GP's current
`coefficient_expansion_v1` validates bounded polynomial substitution but does
not validate those derivative and localization steps. A future contract should
compose Laurent support/derivative lowering, declared guard clearing, and
coefficient expansion; encoding the already-computed scalar rows directly
would skip the load-bearing translation.

The adapter deliberately requires the exact post-restriction pivot polynomial
and current generator list. A native certificate containing only an equation id
cannot be independently replayed.

The current pilot begins after the JC independent replay has accepted the exact
normalized pivot polynomial. JC owns extraction, the ordered substitution
chain, pin reduction, and any clearing or stripping of chart units. GP checks
the resulting local solve in the declared localization. Consequently the GP
report explicitly grants no whole-chain authority. Promoting normalization
itself requires serialized normalization receipts and another certificate.

This pilot supports polynomial pivot equations whose coefficient is a rational
monomial in declared guards with nonnegative powers. If real elimination emits
rational residual equations or negative powers before the pivot, stop and
extend the replay envelope explicitly; do not normalize them away informally.

The default replay mints no graph authority. The opt-in graph-bound replay
mints only local `EMPTY` after exact proof replay; neither mode grants source,
parent, chain, or H3 authority.

The next bounded composition assay lives in
`fixtures/jc_source_ladder/localized_triangular_solve_chain_v1.json`. Unlike
this directory's twelve independent q pivots, it checks the actual five-step
source top-face order and recomputes every state transition. It remains
standalone translation validation until graph endpoint binding is designed.
