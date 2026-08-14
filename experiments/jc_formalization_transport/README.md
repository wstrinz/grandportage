# JC formalization transport ledger v0

This experiment is the first Grand Portage pressure test against the
Lean-native JC summit push. It compiles one deterministic, read-only ledger of
the current semantic objects, formal declarations, theorem premises, artifact
bindings, and transports.

It is deliberately outside graph authority:

```text
authority: DERIVED_READ_MODEL_ONLY
graph_effect: NONE
```

The adapter delegates exact-affine transport decisions to the existing GP
kernel. Formal-power-series, degeneration, rank-credit, and other non-kernel
edges fail closed rather than acquiring a guessed relation. A Lean declaration
binding includes its source digest, fully qualified name, endpoint identities,
scope, coefficient domain, premise IDs, and replay command. Compilation does
not replay Lean mathematics.

Run the frozen assay:

```text
python experiments/jc_formalization_transport/adapter.py
```

Also check the sibling JC commit, exact source bytes, and declaration presence:

```text
python experiments/jc_formalization_transport/adapter.py --check-native-bindings
```

The A--H cases are part of the fixture and compilation fails if a mutation
changes an expected licence, refusal, or inexpressibility verdict. In
particular, the block-one theorem edge must retain the order-eight remainder,
slice-solution, and all-orders-gauge premises verbatim.

This is an assay, not a schema-freeze proposal. Promote the formal-declaration
binding only if it catches live drift or materially simplifies native-to-Lean
binding. Retire any ledger edge that Lean makes definitional.
