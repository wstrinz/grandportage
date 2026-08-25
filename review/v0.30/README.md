# Grand Portage v0.30 release record

Version: `0.30.0`

Graph format: `7`

Kernel epoch: `11`

Collected checks: `1536`

v0.30 is an evidence-layer release; the transport table is unchanged. It
repairs the lifecycle of inconclusive verifier attempts, separates native
verification from Singular execution provenance, adds bounded
algebraic-extension-valued point witnesses, independently checks ordered-real
receipts, and catches the Lean shadow up to kernel epoch 11.

## Inconclusive attempts and execution provenance

`UNVERIFIED` is visible and retryable for every verdict subject. It no longer
suppresses the obligation that motivated verification or prevents the next
`gp verify` batch from trying again. A solver-free verifier records a closed
`grandportage-native` execution manifest. Singular-backed authority still
requires the exact production adapter, binary identity, immutable trace, and
artifacts. An unavailable or injected CAS can record only inconclusive native
history, never a positive CAS verdict.

## Extension-valued point witnesses

`simple_number_field_v1` certifies a witness field Q[a]/(f) independently of
the model coefficient field. The bounded contract accepts monic irreducible
quadratic or cubic f, polynomial or numerator/denominator coordinates, and Q
models at `ALGEBRAIC_CLOSURE`. Exact quotient arithmetic checks irreducibility,
denominator invertibility, every model equation, and every open guard. BASE and
ordered extension witnesses fail closed.

CFG23 Q(i) and its conjugate are positive controls. Wrong quotient
coordinates are `NOT_A_POINT`; reducible minimal polynomials and denominators
that vanish modulo f are inconclusive certificate failures. Verdict input
fingerprints bind the model, witness field, coordinates, and replay receipt.

## Independent selected-real receipts

Ordered signs now emit `selected_real_interval_v2`. The receipt retains its
Sturm chain, selected/refined intervals, endpoint variation counts, value
interval, zero-gcd evidence, and endpoint-root mode. `ordered_receipt.py` is a
separately authored exact checker and does not import the producer. Fold-time
activation uses only this checker; mutations to the chain, variation count,
interval, or sign fail replay. The condition verifier advances to version 3.

## Lean shadow

`SelectedEmbedding.lean` pins `modeledKernelEpoch = 11`, gives the two-root
conjugation countermodel, proves the identical/omitted-selection safe cases,
and classifies selected embedding as extra-structure preservation rather than
a fifth identity gate. `StructureContext` remains separate from
`CertificateScope`. Python CI fails if the runtime kernel epoch advances
without the shadow.

## Validation

- Complete collection: `1486 passed, 50 skipped` (`1536` total).
- Lean: `SelectedEmbedding.lean` compiles under the pinned toolchain.
- Existing CFG23 `22_4`, `26_4`, Q(i), selected-embedding mutation, endpoint
  fingerprint, duplicate-ID, and ordered-sign fixtures remain green.
- New positive controls: Q(i), its conjugate, native ordered recording without
  Singular, and native extension-witness recording without Singular.
- New adversaries: hidden/retry-blocking `UNVERIFIED`, fake CAS authority,
  reducible witness fields, nonunit denominators, wrong quotient coordinates,
  tampered extension receipts, and tampered Sturm receipts.

## Remaining boundary

This release does not add multivariate real geometry, general ordered ambient
fields, topology/oriented-matroid semantics, normalized endpoint polynomial
quotients, or a typed claim language. The campaign-side orientability pilot is
an independent finite experiment and has no GP graph authority.

The v0.30 compatibility assay lane (below) deliberately kept this boundary
narrow a second time: matroid semantics and `GF(2)`/finite-field-of-order-2
coefficient support are explicitly **not** implemented here, even though the
CFG23 assay touches combinatorial/incidence structures that could invite them.
`coefficient_domain` still accepts only `Q` or a prime field `F_p` (§SCOPE.md
2/6); `GF(2)` needing distinct semantics from a generic `F_p` (characteristic-2
arithmetic identities, e.g. `-1 = 1`) is a live open question, not a settled
"add the case" job, and the ontology question of what a matroid model even
denotes here (an ideal? a set-system claim kind? something outside the exact
affine regime entirely, per `SCOPE.md` §1) has not been asked on a real
campaign yet. Recorded as a boundary, not built: the same discipline
`SCOPE.md` §7's `DEGENERATION` entry uses -- deferred until a live run forces
the design, not guessed at here.

## Compatibility repair and CFG23 assay

A follow-on lane repaired a P0 historical-format regression and exercised the
release against the real CFG23 campaign graph. See
`review/v0.30/COMPATIBILITY-ASSAY.md` for the full receipt: the
`validate_meta_for_read` fix (formats 5-6 require/preserve/validate a closed
implementation identity that formats 1-4 never had), the copied-graph
before/after authority ledger, the native `Q(i)` witness exercised on
`M-CT1-SAT-5GUARDS` without Singular, and the honest `UNVERIFIED` fix for
`M-CT1-CLOSED`'s non-executable descriptor-object/prose schema.
