# Phase 0a generator identity contrast (76.7)

Frozen source: GP v0.37.0 `ac4155787207e2847d248cffed7be871d5dcd577`. This is one bounded injected-runner observation using the existing CAS custody pattern. It does not invoke Singular.

## Controlled inputs

Both runs construct a `CASProgram` with the same dialect, ring, variables, declaration `ideal GP_I = x`, empty body, output `GP_I`, characteristic and ordering. Its rendered template is identical (SHA-256 `d08bc1ff48e227aecbdb2f10e66acac87f2a1ca2e6cbe530625239cda94d4a06`), and both mocked nonce-bound transcripts parse `GP_I[1]=x`. The only caller input changed is `generators`: the matching control uses `['x']`; the contrast uses `['1']`. Both isolated F: graphs begin with the same source model `SRC` and use the same declared `IMAGE_CLOSURE` transport to produce `DST`.

| Identity or result | Matching `['x']` | Changed `['1']` |
| --- | --- | --- |
| CASProgram semantic fingerprint | `sha256:800729dacbb6c24406fd04906660c53d7e6691f88ce8e83380c6b54fbfdefc83` | same |
| Execution semantic-input fingerprint | `sha256:800729dacbb6c24406fd04906660c53d7e6691f88ce8e83380c6b54fbfdefc83` | same |
| Parsed mock output | `GP_I[1]=x` | `GP_I[1]=x` |
| Persisted `DST.generators` | `['x']` | `['1']` |
| Persisted model-event SHA-256 | `2d1c0aa04858f4ae0a86947590fe8c5c549d69778ef281e7a78da78191d1c01d` | `9fc5730c0c07d680063d8ec2050c2ff729d24dcf0f0659eef01bd362e3b23832` |
| Nonce-bound program fingerprint | `sha256:c0de7078d9f21fcaa7a66283be41e86fe92d15568bb6f34374356ef78140440c` | `sha256:f58dfc1270a63a5784c4f99f80638ed1f25289634ca99de890c5db31253a2f0c` |
| Artifact fingerprint | `sha256:81575ff4e2ac59a515f9abd902f55c4560b6314da7eed526f5e90353ad0f5f8a` | `sha256:7fa0075efdec5e0ab60870120bc23c6ed714cd03e089ecffb4ec3e8ae7ef6556` |

The loaded graph models match the persisted events; those model events differ only in `generators`. The semantic program and execution-input fingerprints stay equal, so they do not bind that declaration field. The graph events themselves distinguish the declarations. Nonce-bound program and artifact fingerprints differ because each execution receives a fresh nonce; their difference does not establish generator binding.

## Source and evidence limits

`grandportage/cas.py:348` stores caller generators, `:396` renders the execution text, `:439` builds the semantic fingerprint without generators, and `:819` passes those generators into the resulting model event. `:1079` creates the per-run nonce. `grandportage/artifacts.py:195` decodes the persisted execution-note reference; `grandportage/store.py:3548` appends the graph events. Exact source hashes, anchors, graph hashes, input objects, and observed events are in the companion JSON. The earlier control is `reports/CAS-PROGRAM-CUSTODY.json#/observations/2`.

This used an injected runner and identical mock CAS output. It records a model declaration and provenance note, not a verified operation, contraction verdict, or held mathematical claim. It does not test a live CAS, an external-input path, or a proposed identity policy. No corpus or predecessor code changed.
