# JC H3 p-axis authority adapter

This isolated lane binds the frozen native `c9_11` p-axis receipt to an exact
Grand Portage model. It does not modify `math-stuff` or promote any JC truth
ledger.

The native source is
`../math-stuff/d2_plane_72_108/f2_h3_p_window_certificate.json`, pinned at

```text
sha256:77a110c9d5fc0ab47c67f86509f3d777d8d9602bad08a992244d3fd98d1b4dde
```

The adapter verifies the selected factor and affine consequence, freezes their
axis scope, and compiles the contradiction into the existing
`localization_membership_v1` certificate

```text
25*p^2*t^4
  = (5*p*t^2 - 10*t*(c9_11+p*t))*E[1,22]
    + 20*t^2*E[3,22].
```

Equivalently, after dividing cofactors by 25, the guard monomial `p^2*t^4`
belongs to the exact ideal. Because `p` and `t` are declared guards, the
existing localized-unit verifier may mint only local `EMPTY`.

Replay the frozen adapter output:

```powershell
python experiments/jc_h3_p_axis/adapter.py
```

Regenerate the fixtures after an explicit native-source review:

```powershell
python experiments/jc_h3_p_axis/adapter.py --write-fixtures
```

Build a new production campaign with real Singular provenance:

```powershell
python experiments/jc_h3_p_axis/adapter.py \
  --campaign-root review/v0.19/jc-p-axis --record
```

The canonical graph contains no intentionally invalid inference. The adapter
exercises the attempted local-to-parent emptiness transport in memory and
requires the kernel to refuse it.
