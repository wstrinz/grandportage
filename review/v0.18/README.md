# Grand Portage v0.18 review packet

This directory freezes two derived artifacts from
`fixtures/jc2/graph.jsonl`:

- `jc2.projection.json` — the complete `grand-portage-projection/v1` read
  model;
- `jc2-explorer.html` — the Three.js explorer with that exact projection
  embedded.

Both say `DERIVED_READ_MODEL_ONLY`. They are review surfaces, never inputs to
the transport kernel.

## Open the explorer

From this repository root:

```console
python -m http.server 8765 --directory review/v0.18
```

Open `http://127.0.0.1:8765/jc2-explorer.html`. The default Three.js modules
are pinned to 0.185.1 on jsDelivr, so the browser needs network access unless a
reviewer regenerates with `--three-root` pointing at a local copy.

## Regenerate byte-for-byte

```console
python -m grandportage.cli --root fixtures/jc2 \
  --graph fixtures/jc2/graph.jsonl project \
  --output review/v0.18/jc2.projection.json --force
python -m grandportage.cli --root fixtures/jc2 \
  --graph fixtures/jc2/graph.jsonl visualize \
  --title "Grand Portage v0.18 JC2 review" \
  --output review/v0.18/jc2-explorer.html --force
git diff --exit-code -- review/v0.18/jc2.projection.json \
  review/v0.18/jc2-explorer.html
```

The projection records the relative source path and its SHA-256, avoiding a
reviewer's machine-specific absolute path.

## Exercise the new evidence contracts

```console
python -m grandportage.cli verify-localized-triangular-chain \
  --spec fixtures/jc_source_ladder/localized_triangular_solve_chain_v1.json
python -m grandportage.cli verify-localized-triangular-chain \
  --spec fixtures/jc_source_ladder/localized_triangular_solve_chain_v2_second_face.json
pytest -q tests/test_projection.py tests/test_triangular.py \
  tests/test_localization.py -m "not live"
cd lean
lake build
```

The v1 fixture starts from the five exact JC source top-face equations. The v2
fixture starts from the exact second faces and checks each normalization
cofactor against the persistent scalar-gauge equation `15*t^3+1=0`.

If the sibling `math-stuff` checkout is available, the isolated adapters also
verify that both frozen GP fixtures are exact translations of their current
native receipts:

```console
python experiments/jc_h3_source_ladder/adapter.py
python experiments/jc_h3_source_ladder/second_face_adapter.py
```

Expected native receipt gates are 41/41 and 31/31 respectively. Neither
verdict grants graph equivalence, emptiness, source membership, coverage, or
H3 authority.
