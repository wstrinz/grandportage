# Grand Portage v0.31.1 patch release record

Version: `0.31.1`

Graph format: `7`

Kernel epoch: `11`

Collected checks: `1637`

v0.31.1 closes one bounded authority escape hatch discovered by CFG23 after
the v0.31 field-scope grammar landed. A claim-level field name cannot turn an
untyped combinatorial model into a space of field-valued points.

## Checker correction

`FIELD-EMPTY-MODEL-SCOPE` now reports `UNSOUND_PREMISE` for every current,
field-relative `EMPTY` claim whose owner model lacks either a structured
coefficient domain or a point universe. The enforcement hook therefore blocks
the premise instead of presenting it as clean.

The rule is deliberately a finding rather than a fold refusal. Historical
graphs remain readable and migratable, while the missing model scope stays
visible as repairable debt. Properly typed field models and combinatorial
`SCHEME` emptiness remain legal.

CFG23 replay now catches the CT1-S1 real nonrealizability claim and the
`(22_4)` control's rational/geometric deletion-obstruction claim. The generic
retrodiction gate also records the newly exposed legacy findings rather than
silently accepting them as positive controls.

## Compatibility

This patch keeps graph format 7, kernel epoch 11, the transport table, and all
persisted schemas unchanged. It changes checker output for claims that were
already missing the structured model needed to support their declared scope.

## Validation

- Complete pre-release collection: `1587 passed, 50 skipped` (`1637` total).
- Focused empty-scope, migration, boundary, and retrodiction gate:
  `125 passed, 13 skipped`.
- The public snapshot and wheel are rebuilt from the immutable patch-release
  source commit and independently exercised before publication.

## Remaining boundary

This release does not decide whether a certificate kind supports geometric
rather than merely combinatorial emptiness. That requires a broader certificate
ontology and remains separate work.
