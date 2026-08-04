# v0.20 proof-carrying source-ladder review packet

This packet contains two independent live consumers of the graph-bound ordered
triangular-chain compilation pattern. Both use graph format 4 and verifier
version 3; neither changes kernel epoch 10 transport semantics.

## Artifacts

- `top-face/.portage/graph.jsonl`: top-face campaign with explicit `t` inverse;
- `second-face/.portage/graph.jsonl`: normalization-bearing second-face campaign;
- `*.projection.json`: deterministic derived read models;
- `*-explorer.html`: static Three.js explorers with embedded projections;
- `evidence-manifest.json`: current evidence and authority contract inventory;
- `SHA256SUMS`: integrity list for every other file in this packet.

There are no CAS execution artifacts in these two campaign directories. The
persisted `VERIFIED` verdicts come from backend-free expansion of authored
`mapped_ring_iso_v1` cofactors. The separate legacy Singular differential is a
test, not part of the authoritative proof envelope.

## Expected results

Each graph has two exact quotient models, one mapped `EQUIVALENCE`, no claims,
and no findings. `verify.ring_iso` checks every cofactor row in both pullback
directions and both polynomial-map round trips. The top face adjoins `GP_INV_t`
with `t*GP_INV_t-1=0`. The second face instead verifies that `15*t^3+1=0`
supplies `t^-1=-15*t^2`.

The authority is exact endpoint identity transport only. Neither graph binds
native source extraction or licenses parent coverage, actual-source membership,
emptiness, depths 2--6, or H3.

## Exercise it

From the repository root:

```powershell
python experiments/jc_h3_source_ladder/authority_adapter.py
python experiments/jc_h3_source_ladder/authority_adapter.py --spec fixtures/jc_source_ladder/localized_triangular_solve_chain_v2_second_face.json
python -m grandportage.cli --graph review/v0.20/top-face/.portage/graph.jsonl check
python -m grandportage.cli --graph review/v0.20/second-face/.portage/graph.jsonl check
python -m pytest -q tests/test_jc_source_ladder_authority.py --basetemp=.pytest-review-ladders
```

The tests mutate a cofactor and require `UNVERIFIED`, then remove the proof
envelope and use real Singular to crosscheck the smaller top face. Removing
the top-face inverse equation must return `NOT_AN_ISOMORPHISM`. Open either
explorer directly or serve this directory if the browser blocks CDN modules.
