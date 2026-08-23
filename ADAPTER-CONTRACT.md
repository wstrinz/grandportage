# Out-of-tree evidence adapter contract

Campaign adapters may live outside the Grand Portage repository. They remain
evidence consumers, not theorem plugins: conformance says an adapter is
auditable and replayable; it grants no graph authority.

An adapter module provides:

- `GRAPH_EFFECT`, equal to the envelope's graph effect and normally `NONE`;
- `MUTATION_CONTROLS`, a nonempty tuple of named refusal mutations;
- `build_envelope()`, returning the shared `EvidenceEnvelope` dictionary;
- `replay(envelope)`, returning a deterministic report with `verified: true`
  only after digest binding and certificate replay succeed.

The envelope must contain exactly the shared evidence fields: schema, affine
context, source bindings, checked proposition, certificate payload, licenses,
outstanding premises, graph effect, and authority boundary. Every source
binding carries an identifier and `sha256:` digest. A standalone adapter may
describe a future compilation target, but its own graph effect remains the
declared value. It may not append graph events.

`MUTATION_CONTROLS` names concrete changes the adapter's tests refuse—for
example `source_digest`, `cofactor_sign`, `ring_variable`, and
`verification_status`. The conformance harness checks that the list exists;
the adapter's own test executes each mutation because only the adapter knows
how to make it semantically meaningful.

Run the shipped structural harness with:

```console
python -m grandportage.adapter_conformance package.module
```

Passing means only `CONFORMING`. The report always says
`authority: DESCRIPTIVE_ONLY` and `graph_effect` explicitly. Promotion still
requires the graph-bound verifier named by the evidence contract.
