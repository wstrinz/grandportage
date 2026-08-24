# Grand Portage v0.29 public release record

Version: `0.29.0`

Graph format: `6`

Kernel epoch: `11`

Collected checks: `1515`

v0.29 introduces selected number-field embedding identity. A model may carry a
closed REAL isolating interval or COMPLEX isolating box, while omission/null
retains abstract-ring behavior. Endpoint and edge fingerprints bind the full
serialized map to both selected endpoint definitions.

An identity map between different selected embeddings is refused structurally.
A genuine polynomial field automorphism remains a ring equivalence, but no
longer copies a free predicate unchanged between selected images. Conflicting
model and edge IDs remain fail-closed; byte-identical redeclarations remain
idempotent for branch merges.

The same pre-release boundary also accumulated bounded ordered-real semantics.
`REAL_CLOSURE` is supported over Q only when coupled to a selected REAL
embedding. Structured predicates may assert exact signs of a univariate
polynomial at that selected root. The verifier checks root isolation with
Sturm arithmetic, refines exact rational intervals, and records a deterministic
receipt that the graph fold replays before activating the verdict.

## CFG23 replay

- `22_4`: the false plus/minus identity is refused; `w -> -7-w` remains a
  polynomial automorphism; exact plus-root relabeling retains predicate
  transport.
- `Q(i)`: the false identity of `i` and `-i` is refused; `x -> -x` remains a
  polynomial conjugation equivalence.
- `26_4`: the selected real root in `(1,2)` is a valid `REAL_CLOSURE` model and
  its positivity verifies exactly; a decoy interval with no root is
  inconclusive and grants no authority.
- All six RFC v1.4 fixture families and all 26 adversarial mutations are
  represented in native GP tests. Required-ID reassignment, endpoint drift,
  map drift, and duplicate model/edge IDs all change custody or fail closed.

## Validation

- Full suite: `1465 passed, 50 skipped` in 53.32 seconds.
- RFC v1.4 reference checker: six clean fixtures, 26/26 mutations detected,
  and 3/3 required maps visited, passing, and semantically verified.

## Remaining boundary

This bounded slice does not claim multivariate real-locus decision procedures,
quantifier elimination, arbitrary semialgebraic transport, or ordering changes
through field automorphisms. Comparisons reuse the one-expression condition
grammar (`a < b` is `NEGATIVE(a-b)`). Nontrivial embedding-changing maps still
refuse predicate transport, while incompatible exact sign assertions at one
selected model create visible debt.

## RFC closure audit

The accepted v1.4 implementation requirements are complete in GP: selected
endpoint identity, duplicate model/edge-id refusal, endpoint-bound map
fingerprints, all six fixture families, all 26 mutation controls, and native
`22_4`, `26_4`, and `Q(i)` replays. The ordered-real follow-up is also present.

The RFC series leaves six design choices that do not block this bounded public
release:

- `conjugate_of` remains descriptive rather than mandatory symmetric custody;
- nontrivial complex boxes remain `STRUCTURAL_ONLY`; exact argument-principle
  or resultant isolation is a separate verifier;
- selected embeddings remain the structural default for embedding-sensitive
  predicates rather than adding a campaign-wide mandatory scope field;
- `REAL_CLOSURE` uses the ordering selected by an embedding into R and does not
  add witnesses for more general ordered ambient fields;
- required-map fixture specifications remain test/checker custody rather than
  a new authored edge field or certificate event; and
- endpoint/map fingerprints remain syntactically exact rather than quotienting
  polynomial spellings such as `w+1` and `1+w`.

These are explicit future extension points, not known-wrong live verdicts.
