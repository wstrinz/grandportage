# v0.19 consolidation review packet

This packet exercises the first complete JC authority chain built without
adding a graph field, claim kind, edge type, or verifier authority.

## Artifacts

- `jc-p-axis/.portage/graph.jsonl`: authoritative folded campaign;
- `jc-p-axis/.portage/artifacts/`: real Singular execution artifacts;
- `jc-p-axis.projection.json`: deterministic derived read model;
- `jc-p-axis-explorer.html`: static Three.js explorer with embedded data;
- `SHA256SUMS`: integrity list for the principal review files.
- `merge-assay.json`: four real two-log fan-out outcomes;
- `differential-affine-internal.json` and
  `differential-affine-singular.json`: deterministic exact-polynomial checks;
- `evidence-manifest.json`: shared standalone/authority contract inventory.

## Expected result

The exact `c9_11` p-axis model has a current
`LOCALIZED_UNIT_IDEAL_CERT` verdict and therefore local `EMPTY`. The graph
has zero live findings. Its immediate same-ring ambient model is not empty by
transport: `NECESSARY_CONDITION/ALONG/EMPTY` is refused.

Nothing here licenses full p-chart emptiness, actual-source membership, an
infinite lift, or H3.

## Exercise it

From the repository root:

```powershell
python -m grandportage.cli --graph review/v0.19/jc-p-axis/.portage/graph.jsonl check
python -m grandportage.cli --graph review/v0.19/jc-p-axis/.portage/graph.jsonl show
python -m grandportage.cli --graph review/v0.19/jc-p-axis/.portage/graph.jsonl project
python -m pytest -q tests/test_jc_p_axis_authority.py --basetemp=.pytest-review-p-axis
```

If the sibling `math-stuff` repository is present, also replay the native
adapter:

```powershell
python experiments/jc_h3_p_axis/adapter.py
```

Open `jc-p-axis-explorer.html` directly or through a small local HTTP server.
The HTML uses pinned Three.js CDN modules; the projection data itself is
embedded.

Mutation controls cover source digest, chart, point universe, equations,
guards, cofactors, and attempted transport to the parent.

The consolidation assays also preserve one honest limitation: the same exact
affine object under two ids composes and is reported as unresolved alias debt;
GP does not infer mathematical identity from a signature. A projection regression
test ensures certificate verdicts point to their claim rather than a nonexistent
certificate node.
