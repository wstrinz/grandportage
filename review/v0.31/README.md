# Grand Portage v0.31 public release record

Version: `0.31.0`

Graph format: `7`

Kernel epoch: `11`

Collected checks: `1627`

v0.31 is the first public release of the v0.30 evidence-layer work. It ships
retryable inconclusive verification, capability-specific native provenance,
bounded algebraic-extension-valued point witnesses, independently replayed
ordered-real receipts, and the Lean epoch-11 selected-embedding shadow. The
transport table remains unchanged.

## Overnight compatibility and scope repairs

The release also incorporates the CFG23 cold compatibility assay. Formats 5
and 6 introduced a portable implementation identity that formats 1--4 never
carried. Direct historical reads and migration now validate the header shape
appropriate to each generation, preserve historical identity without treating
it as the current binary, and keep old verdicts subject to normal freshness
rules. The real CFG23 format-6 graph reads and migrates to format 7 without
silent authority gain or loss.

Field-relative `EMPTY` claims no longer accept an arbitrary nonempty `scope`
string. The kernel recognizes atomic `Q`/`R`/`C`, canonical prime fields
`F_p` within the exact 32-bit arithmetic bound, and bounded nonblank
`Q(...)`/`R(...)` extension labels. Missing, composite, generic, case-drifted,
leading-zero, and oversized values fail at fold time. The same boundary covers
new declarations, historical reads, and migration.

## Native evidence delivered

- `UNVERIFIED` remains visible, current, and retryable without gaining
  mathematical authority.
- Solver-free decisions carry closed `grandportage-native` provenance; an
  injected CAS cannot impersonate a production Singular execution.
- `simple_number_field_v1` checks quadratic/cubic Q-extensions, quotient-field
  coordinates, denominators, equations, and guards exactly.
- `selected_real_interval_v2` retains its Sturm chain, variations, intervals,
  zero evidence, and endpoint mode for independent fold-time replay.
- The Lean shadow pins kernel epoch 11 and models selected embeddings as extra
  structure separate from certificate scope.

## Validation

- Complete collection: `1577 passed, 50 skipped` (`1627` total).
- Focused scope/format/kernel gate: `154 passed` before the version stamp.
- Lean: `SelectedEmbedding.lean` and the full Mathlib-free shadow build under
  the pinned toolchain.
- Public snapshot: generated only from the immutable v0.31 source commit and
  verified again in the public mirror before publication.

## Remaining boundary

This release still does not add multivariate real geometry, arbitrary ordered
ambient fields, topology/oriented-matroid semantics, a typed claim language,
or general number-field presentation equivalence. The CFG23 weak-orientability
pilot remains an external finite experiment with `graph-effect: NONE`.
