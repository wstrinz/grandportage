# Compatibility epochs

Grand Portage separates **file readability** from **mathematical authority**.
An old graph may remain valuable history without retaining every licence that an
older kernel inferred from it.

## The year-zero boundary and first semantic transition

Version 0.5.0 established:

- `graph_format: 1` — the syntax and ownership of persisted fields;
- `kernel_epoch: 1` — the first frozen transport semantics;
- `created_with` — the Grand Portage version that wrote the graph.

Every native graph begins with one `meta` event. Native events have closed
schemas: unknown fields are rejected, licensing flags are JSON booleans, and
every edge declares `map_kind` explicitly. The exact pre-epoch implementation
is tagged `pre-epoch-0.4.2`.

Version 0.6.0 keeps graph format 1 and advances to **kernel epoch 2**. The
elimination OperationContract proved that the local output verifier establishes
only `J ⊆ ι⁻¹(I)`, while two forward `IMAGE_CLOSURE` transports require the
missing completeness direction. Constructed eliminations therefore no longer
receive exact-forward authority from a one-sided `VERIFIED` verdict.

That is a semantic change, so it is an epoch change rather than an unannounced
checker tweak. Format-1/kernel-epoch-1 graphs migrate non-destructively:

```console
gp --graph old/.portage/graph.jsonl migrate --to-current-kernel
```

The command writes a new graph named for the current kernel epoch and an audit file. The source is
never replaced; prior verdicts remain in history but are stale, and every
transport is re-audited under epoch 2.

Version 0.7.0 also keeps graph format 1 and advances to **kernel epoch 3**.
It introduces a separately versioned `elimination` verifier subject and splits
exact coordinate-ring contraction from geometric point-closure authority. A
current `VERIFIED` operation-output verdict plus a current
`VERIFIED_SECTION` polynomial-section verdict licenses exact retained-ring
identity transport. It does not license closed point predicates: those still
need an independently checked field/radical-aware geometric theorem.

This is both a transport-meaning and verifier-trust change, so epoch 2 graphs
must be re-audited. The migration command is now epoch-neutral:

```console
gp --graph old/.portage/graph.jsonl migrate --to-current-kernel
```

It writes `graph.kernel3.jsonl` by default. The old `--to-kernel2` spelling is
accepted only as a hidden compatibility alias; new automation should use the
current-kernel spelling. The source remains untouched and all earlier verdicts
remain readable but stale.

Version 0.8.0 keeps graph format 1 and **kernel epoch 3**. It adds a second,
separately pinned verifier algorithm for the existing elimination-completeness
obligation: `VERIFIED_GROEBNER`. Singular may produce a pure-lex basis and
finite witnesses, but authority is projected only after GP's backend-free exact
checker replays the full proof against the ordered graph inputs. The existing
`VERIFIED_SECTION` meaning is unchanged; either current completeness proof
combines with the same independent `VERIFIED` operation-output verdict.
Constructed eliminations still receive no geometric point-image authority.

This is an evidence and verifier extension inside the OperationContract already
formalized in epoch 3, not a change to transport meaning. Existing section
verdicts therefore remain current; the new verifier identity is independently
versioned and its producer artifacts are content-addressed.

Version 0.9.0 keeps graph format 1 and advances to **kernel epoch 4**. The
polynomial-section verifier was previously under-credited: a checked polynomial
retraction does not merely prove ideal completeness. For every target-valued
point, evaluating the section polynomials gives a source-valued lift whose
retained coordinates are unchanged. Combined with the independent no-invention
verdict, this earns point-surjective image authority over the declared
coefficient algebra. `VERIFIED_GROEBNER` remains ideal authority only.

This reopens the existing Zariski-closed predicate transport cell for
section-certified constructed eliminations, so it is a transport-meaning change
and requires a new kernel epoch. Section verifier version 2 and epoch 4 make all
older section verdicts readable but stale. Migration writes `graph.kernel4.jsonl`
and never replaces its source.

Version 0.10.0 advances to **graph format 2 and kernel epoch 5**. Format 2 adds an
optional structured `condition` to model-level `PREDICATE` claims: a non-empty
conjunction of exact polynomial `ZERO` and `NONZERO` atoms. Every expression is
parsed in the source model ring. On a direct section-certified elimination the
same expressions must parse in the retained-coordinate target ring.

That syntax projects Lean's `RetainedCoordinateExpressible` obligation into the
runtime. Section point-surjectivity may now carry target-expressible predicates
without a closedness hypothesis; all-`ZERO` conditions also derive the existing
closed route. Groebner completeness, manual closure declarations, free-text
predicates, conditions naming eliminated coordinates, and conditions arriving
after an earlier path step do not acquire this authority. This is both a file
syntax and transport-meaning change, hence both counters advance.

`gp migrate --to-current-kernel` copies older native graphs into format 2 / epoch
5 without rewriting their events: the optional condition starts absent, old
verdicts remain readable but stale, and the append-only source remains untouched.

Version 0.11.0 keeps **graph format 2** and advances to **kernel epoch 6**.
Structured conditions can now be reindexed through chains of verified mapped
`EQUIVALENCE` edges before a section-certified elimination. Because `forward`
is the point map, `ALONG` uses the checked `inverse` substitution and `AGAINST`
uses `forward`; literal identity maps preserve syntax. The substitution is
simultaneous, exact, and ephemeral. Any unverified, refuted, or unsupported pass
loses structured expression typing and cannot unlock the downstream transport.

This changes which composed inferences are licensed without adding persisted
syntax, so only the kernel counter advances. Epoch-5 graphs migrate
non-destructively to epoch 6; their old verifier verdicts remain readable but
stale and must be re-established under the new authority boundary.

Version 0.12.0 keeps **graph format 2** and advances to **kernel epoch 7**.
The Lean calculus now exposes generic predicate pullback along a point map, with
identity and composition laws. Runtime structured conditions preserve their
syntax in the sound `AGAINST` direction through a literal identity-coordinate
map when the exact endpoint rings match, or through a currently checked
constructor-built elimination projection. This lets restriction/refinement
pullbacks and projection pullbacks compose with later section-certified
eliminations.

An unspecified polynomial map, an unchecked elimination output, or a malformed
projection still loses structured typing. A RESTRICTION with mismatched exact
endpoint coordinates or characteristics is rejected as ill-typed when both sides
declare that metadata; its point transports require one common point universe. These paths were previously refused at a later operation and are now
licensed, so the kernel epoch advances without a graph-format change. Epoch-6
graphs migrate non-destructively and all earlier verdicts remain stale history.

Version 0.13.0 keeps **graph format 2** and advances to **kernel epoch 8**.
A new `point_lift` verifier subject checks finite point-lift covers independently
of elimination completeness. Each principal-open chart gives rational formulas
whose denominators are powers of one nonzero guard; a final polynomial fallback
applies where all guards vanish. Bounded localization/radical searches produce
cofactors, and the graph fold replays every stored polynomial identity with the
small exact checker.

Current no-invention plus `VERIFIED_POINT_LIFT` now grants the same
point-surjective image authority as a checked global polynomial section, while
leaving exact contraction closed unless section or Groebner completeness is
also proved. This licenses new nonclosed retained-predicate transports, so it is
a kernel-epoch change. The proof envelope and verdict field are computed-only,
fingerprint-bound, and independently stale. Epoch-7 graphs migrate
non-destructively; their old verdicts remain readable history.

Version 0.14.0 advances to **graph format 3** and **kernel epoch 9**.
Models may now declare two independent, bounded semantic attributes:

```json
{"coefficient_domain":"Q","point_universe":"ALGEBRAIC_CLOSURE"}
```

`coefficient_domain` is currently exactly `Q` or the prime field `F_p`
determined by `characteristic`. `point_universe` is `BASE` or
`ALGEBRAIC_CLOSURE`, relative to that coefficient domain. The legacy `field`
and `universe` prose remain readable but cannot coexist with their structured
replacements and do not silently acquire their authority.

Partition verification now requires every branch to share both attributes with
the parent. A failed radical-cover test is `NOT_EXHAUSTIVE` when the declared
point universe is algebraically closed; over `BASE` it remains the weaker
`NOT_GEOMETRICALLY_EXHAUSTIVE` debt. Partition verifier version 3 fingerprints
the new scope, so previous verdicts become stale rather than changing meaning.
Version 0.14 also adds the standalone `localization_membership_v1` translation
checker. It grants no persisted graph or transport authority, so it is an
evidence-language extension within epoch 9 rather than another semantic epoch
change.

Version 0.15.0 remains at **graph format 3** and **kernel epoch 9**. It adds the
standalone `sparse_polynomial_v1` evidence encoding to the shared exact
polynomial checker. A sparse value is a closed object containing canonical
nonzero coefficient strings and a descending lexicographic list of monomials;
each monomial names positive powers in ring-variable order. Existing term,
exponent, coefficient-bit, variable-power-entry, multiplication, and global
arithmetic budgets still apply.

This is an evidence-language and resource-boundary extension, not a transport
change. Legacy infix polynomial strings remain accepted. The localization and
coefficient-expansion validators preserve sparse inputs through checking and
normalized reports instead of rendering them into an infix expression that the
same checker would conservatively refuse. The first live batch replay checks
all twelve frozen JC q-window pivots independently; it does not grant authority
to their composition or to the surrounding research claim.

Version 0.16.0 remains at **graph format 3** and advances to **kernel epoch 10**.
It adds one narrowly scoped graph authority: an `EMPTY` claim on a recorded
principal-open model may cite `LOCALIZED_UNIT_IDEAL_CERT`. The
`verify.localized_unit_ideal` producer searches a bounded set of guard
monomials; only an exact cofactor identity promotes the claim. A bounded miss is
`UNVERIFIED`, never a refutation or nonemptiness result.

The persisted `localized_unit_ideal_v1` proof envelope is fingerprint-bound to
the exact claim, model, characteristic, ordered ring variables, generators,
and open conditions, and the graph fold replays it with the backend-neutral
exact checker. The certificate base-changes because its polynomial identity
does. It grants EMPTY only at that open model. Existing RESTRICTION transport
refuses EMPTY from the open chart to its parent, so this epoch adds no new
transport-table cell. Epoch-9 graphs migrate non-destructively; all earlier
verdicts remain readable but stale.

Version 0.17.0 remains at **graph format 3** and **kernel epoch 10**. It adds
two standalone, closed translation validators. `laurent_lowering_v1`
independently evaluates bounded finite Laurent straight-line programs over the
shared exact-polynomial coefficient ring, checks declared equalities, and may
export a value as canonical `sparse_polynomial_v1` only after an explicit
monomial shift clears every negative exponent.

`laurent_coefficient_pipeline_v1` verifies a nested Laurent specification and
coefficient-expansion specification, then requires total, unique, exact
export-to-image bindings. Consequently, a hand-edited intermediate cannot
inherit the upstream receipt merely because its downstream scalar rows are
self-consistent. These verdicts remain standalone evidence: they grant no
persisted claim, graph transport, source-chart theorem, or H3 authority.
Version 0.17 therefore extends the evidence language and compiler-pass trust
boundary without changing graph syntax or kernel transport meaning.

Version 0.18.0 remains at **graph format 3** and **kernel epoch 10**.
It adds two surfaces outside persisted graph authority.
`grand-portage-projection/v1` is a deterministic, read-only projection of a
folded campaign for review and visualization. It carries source fingerprints
and an explicit `DERIVED_READ_MODEL_ONLY` authority marker; neither projection
JSON nor the generated Three.js explorer is accepted by the kernel.

The closed `localized_triangular_solve_chain_v1` evidence schema checks an
ordered sequence of exact localized affine substitutions and fingerprints every
intermediate generator state. Version 2 additionally checks exact cofactors
against persistent normalization generators. The live second source ladder
requires precisely this distinction: all five polynomialized solves agree with
the native faces modulo `15*t^3+1`, not as literal ambient polynomials. Both
schemas bind the native receipt digest and deliberately grant no graph model
equivalence, emptiness, source membership, coverage, or H3 conclusion. Lean
proves the semantic normalization and chain-composition laws that a future
graph-bound result would need. Consequently v0.18 extends review tooling and
the standalone evidence language without changing graph syntax or transport
meaning.

Version 0.19.0 remains at **graph format 3** and **kernel epoch 10**. It is a
consolidation and composition release. The JC `c9_11` p-axis adapter compiles a
specialized factor/affine receipt to the existing localized-unit-ideal proof
language and uses the existing graph-bound verifier to mint only local `EMPTY`.
No new graph field, edge type, claim kind, transport cell, or verifier authority
is introduced.

`grandportage.evidence` adds a descriptive shared affine context, evidence
envelope, and static authority manifest. All specialized standalone evidence
contracts retain graph effect `NONE`; `verify.localized_unit_ideal` remains the
only manifest entry with the narrowly contained `LOCAL_EMPTY` effect. The
fan-out merge and exact-polynomial differential reports are derived assays only.
A projection bug fix maps certificate and witness verdicts to the claims they
verify; projections remain `DERIVED_READ_MODEL_ONLY` and are never accepted as
kernel input.

Version 0.20.0 advances to **graph format 4** and remains at **kernel epoch 10**.
Format 4 adds the optional, closed `ring_iso_certificate` field to a mapped
`EQUIVALENCE`. Its first representation, `mapped_ring_iso_v1`, carries one
exact cofactor row for every generator in both ideal-pullback directions. The
ring-isomorphism verifier expands every row with the backend-neutral polynomial
checker and separately checks both forward/inverse map compositions.

This is a proof-carrying alternative for the existing coordinate-ring
isomorphism obligation, not new authority: successful solver search and a
successful exact envelope license the same identity transport between the same
exact endpoint quotients. The ring-isomorphism verifier advances to version 3,
so earlier map verdicts become stale and must be rerun. No edge type, claim
kind, transport cell, or containment scope changed; kernel epoch 10 therefore
remains current. Invalid envelopes are `UNVERIFIED`, not refutations. Format-3
graphs migrate non-destructively to format 4 with the optional field absent.

The two live JC consumers are the five-step source top and second faces. The top
face represents localization with an inverse coordinate; the second face uses
its normalization relation to supply a checked polynomial inverse. Both compile
to exact cofactor envelopes and retain no source-extraction, parent, coverage,
actual-source-membership, or H3 authority.

Version 0.21.0 remains at **graph format 4** and **kernel epoch 10**. It adds
two isolated review consumers without expanding graph authority. The JC
depth-6 assay independently decodes the frozen boundary residuals, verifies
the generic and discriminant mapped equivalences, and replays a landed 23-step
chain through 25 digest-bound face tables. Its evidence envelope has graph
effect `NONE` because raw E-system-to-face extraction remains an explicit
premise. The Stacks applicability sidecar pins three theorem statements and
audits their printed and application-specific hypotheses; discovery ranking
and application packets likewise have no graph effect.

The exact substitution checker now preserves an already-canonical sparse
polynomial when every nonidentity coordinate map is absent from its support.
The shortcut follows an exact parsed support test and changes only resource
use; verifier meaning and version remain unchanged. Version 0.21 therefore
adds no edge type, claim kind, transport cell, verifier authority, graph field,
or kernel-epoch transition.
Version 0.22.0 keeps graph format 4 and kernel epoch 10.
Containment verifier version 3 recognizes one backend-free proof already
implicit in ideal semantics: if every target generator is an exactly parsed,
verbatim member of the source generator list, unit cofactors establish the
required ideal inclusion. Every non-subset case still uses the existing backend
reduction, and malformed equal payloads are refused.

This changes verifier implementation and trust without changing containment or
transport meaning. Version-2 containment verdicts therefore remain readable
but stale and must be recomputed; no kernel-epoch transition is required. The
first live consumer is the 78-variable JC finite-template assay.

Development after v0.22 introduces derived projection schema v2. It replaces
duplicate node records with references into the projection collections. This is
a read-surface compatibility boundary only: projections remain non-
authoritative,
and graph format 4, kernel epoch 10, and folded graph meaning are unchanged.
Within one kernel epoch, no field may silently acquire a more permissive
interpretation. A syntax-only extension can bump `graph_format`; transport
meaning or verifier trust bumps `kernel_epoch` or the narrower verifier/backend
implementation version as appropriate.

## Epoch-0 graphs

Unversioned graphs are epoch 0. Version 0.14 continues to read them through a conservative,
read-only importer. It will not append new events to them and will not blend
them with epoch-1 graphs.

The importer can preserve or reduce authority, never increase it:

- malformed truthy licensing values become `false`;
- a missing `map_kind` becomes the non-licensing `RATIONAL` kind, except that a
  `RESTRICTION` remains the same-coordinate `IDENTITY_MAP` inclusion its type
  already asserts;
- legacy `witness` is read as `strictness_witness`;
- retired `zariski_dense` is dropped;
- old verifier verdicts remain history but are inactive;
- cited, no-map `ring_iso` declarations do not license identities;
- fingerprintless baseline acceptances are stale until deliberately accepted
  again.

## Migration

Migration never rewrites the append-only source:

```console
gp --graph path/to/graph.jsonl migrate --to-epoch1
```

This writes `graph.epoch1.jsonl` and `graph.epoch1.jsonl.audit.json` beside the
source. The audit records the source SHA-256 and every normalization or dropped
field. The new graph is strict-loaded before either artifact is written.

To activate a migrated graph in a new campaign root, choose its destination
explicitly:

```console
gp --graph old/.portage/graph.jsonl migrate --to-epoch1 \
  --epoch1-output new/.portage/graph.jsonl
```

Existing output is never overwritten. Epoch-0 and epoch-1 logs cannot be merged
until the epoch-0 side has been migrated.

## Verifier verdicts

A computed verdict is executable trust. Epoch 1 records:

- verifier identity and verifier-specific version;
- kernel epoch;
- backend contract, implementation, and exact binary version;
- a SHA-256 fingerprint of the complete semantic input;
- a typed execution trace whose entries reference complete, content-addressed
  raw execution envelopes.

A legacy verdict, a verdict from another implementation epoch, or a verdict
whose target input changed remains visible in history but is `STALE` and does
not populate any effective evidence field. Rerun the verifier to mint a current
answer.

Algebraic verifiers also require an explicit model characteristic. Omission is
unknown, not characteristic zero.

Backend protocol 2 / Singular implementation 3 stores each exact nonce-bearing
program, argv, exit state, stdout, stderr, parsed output, and certificate in a
canonical envelope under `.portage/artifacts/sha256/`. The envelope address is
part of the verdict trace. Objects are durably published before a graph-affecting operation reference or
verdict is appended, so a persistence failure cannot create a dangling record.
Operation references are non-authoritative notes; verdict traces carry authority. Run:

```console
gp artifacts check
```

to verify every reference, inner transcript hash, backend identity, and trace
projection. Missing objects fail this explicit audit but do not make graph
folding depend on ambient filesystem availability. Content is immutable and
deduplicated; there is no automatic garbage collection.

## Current milestone: narrow backend seam and M2

The next architectural step after the epoch-1/L3 hardening cut is a narrow CAS
backend seam, not a promise of broad multi-CAS support. `SingularBackend` remains
the reference implementation and must preserve the exact program, backend
identity, input fingerprint, and verdict provenance that were actually run.

The first M2 slice now provides backend-neutral ring specifications, immutable
execution artifacts, and a semantic `SingularBackend` for identity classification,
ideal and unit-ideal membership certificates, independent certificate checking,
point evaluation, saturation, elimination, mapped pullback, partition coverage,
and factorizing decomposition. Structured operations reject an artifact attached
to a different program, and verifier events fingerprint a typed execution trace.
Only the exact production adapter and probed binary may persist authority;
subclasses, injected runners, and version overrides are test-only and can run only
with `record=False`. Pre-M2 verdicts remain readable but stale under verifier
provenance version 2.

The trust model has three explicit lanes. Certificate-bearing answers are checked
by replayable arithmetic independent of the search. Direct normal-form reductions
remain inside the named, versioned Singular/verifier trusted computing base.
Verifier-native structural decisions, such as a vacuous containment, explicitly
spawn no backend artifact. Each is recorded as the evidence mode it actually uses.

The golden corpus compares mathematical ideals by mutual certified membership,
not by generator spelling or Groebner presentation. It includes characteristic-
dependent membership, non-involutive maps, saturation whose first witness exponent
is nine, compact elimination output, geometric holes over a base field, overlapping
covers, non-prime one-piece decompositions, CAS errors, and partial output. Backend
disagreement blocks promotion; it is not resolved by silently choosing one answer.

The transcript-completeness boundary binds a fresh nonce to every execution and
accepts mathematical output only when the matching marker is the final
non-whitespace line. Singular implementation version 2 made pre-marker verdicts
stale; implementation version 3 adds the durable content-addressed envelope.
The first narrow elimination-completeness certificate was a checked polynomial
section, which earns the missing contraction inclusion without trusting a second
backend.
Version 0.8 adds a second route for cases with no polynomial section: Singular
produces a bounded pure-lex basis and representation witnesses, while the small
backend-neutral exact checker independently verifies source span, every critical
pair, the elimination order, and retained-basis membership in the target ideal.
The producer remains untrusted search; only the checked certificate carries
authority. Epoch 4 recognizes that the section additionally supplies explicit
point lifts. Epoch 5 adds the claim-side retained-coordinate expressibility
obligation. Epoch 6 composes that obligation through verified mapped coordinate
changes using exact contravariant substitution. Epoch 7 derives ordinary
predicate pullback through concrete identity and checked projection maps. The
remaining semantic work is typed point-lifting evidence beyond global polynomial
sections and explicit maps for the remaining nonidentity operations. Backend cross-checking can strengthen confidence in certificate
production, but it is not part of the trusted argument.

The release order is now visible in the epochs: close known semantic defects,
cut format 1 / kernel epoch 1, finish the backend evidence seam, then advance to
kernel epoch 2 when the elimination contract exposed a narrower real licence,
then kernel epoch 3 when a certificate earned back only the coordinate-ring
half, kernel epoch 4 when polynomial sections were correctly recognized as
point-lifting evidence, graph format 2 / kernel epoch 5 when retained predicate syntax made that
authority safely usable beyond closed conditions, kernel epoch 6 when verified
coordinate changes made that typing compositional, kernel epoch 7 when the
generic point-map pullback law became executable for restrictions and
projections, and kernel epoch 8 when finite checked point-lift covers gained
point-surjective authority.

## Sealed campaigns

A sealed epoch-0 experiment should continue with the executable pinned when it
was sealed. Do not migrate or reinterpret it mid-experiment. Migration is for a
new artifact after the seal opens, or for a new campaign root.

Epoch-0 append refusal is intentional: the compatibility importer remains
read-only and a declaration writes nothing until the graph is explicitly
migrated beside its source. Current epoch-1 writers may select one exact log
with global `--graph`; repeated graph arguments remain read/merge syntax and
are refused for declaration. The `gp declare`, `portage_declare`,
`portage-declare`, and MCP declaration surfaces all use the same transactional
store path.
