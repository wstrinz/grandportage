# v0.21 depth-chain and applicability review packet

This release freezes two isolated consumers above the v0.20 graph-bound source
ladders. Neither adds graph authority or changes kernel epoch 10.

## JC depth-6 chain

The canonical review inputs live at:

- `fixtures/jc_source_depth6/boundary_v1.json`;
- `fixtures/jc_source_depth6/chain_v1.json.gz`;
- `experiments/jc_h3_source_depth6/adapter.py`;
- `experiments/jc_h3_source_depth6/chain_adapter.py`.

The fast adapter gate checks certificate identity, both byte digests, all
ordered prefix fingerprints, 23 affine solves and unit witnesses, ten exact
welds to the GP top/second-face solutions, and both boundary-output welds. The
optional full replay recomputes all 25 ambient face substitutions with exact
rational sparse arithmetic.

Expected authority: `graph_effect: NONE`. The certificate binds the 25 face
tables but does not derive them from the raw E-system. It licenses no
actual-source membership, chart cover, H3, or `(75,125)` verdict promotion.

```powershell
python experiments/jc_h3_source_depth6/chain_adapter.py
python experiments/jc_h3_source_depth6/chain_adapter.py --full-replay
python -m pytest -q tests/test_jc_source_depth6_authority.py tests/test_jc_source_depth6_chain.py
```

## Stacks applicability sidecar

`experiments/stacks_applicability/` pins three official Stacks statements and
keeps theorem discovery, source validation, and JC application-premise audits
separate. All three present applications are intentionally refused because
their bridge premises remain missing, open, or outside the exact-affine sort.

```powershell
python experiments/stacks_applicability/sidecar.py validate-shelf
python experiments/stacks_applicability/sidecar.py audit experiments/stacks_applicability/applications/jc_00IP.json
python -m pytest -q tests/test_stacks_applicability_spike.py
```

## Release checks

- Python collection: 1,308 checks;
- last full result: 1,267 passed, 41 skipped;
- Lean: 21 jobs built;
- independent full depth-6 replay: verified in approximately 78 seconds.

`SHA256SUMS` pins this packet and the principal external review inputs without
duplicating the multi-megabyte fixtures.
