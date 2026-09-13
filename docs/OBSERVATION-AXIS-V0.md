# Observation axis: model-indexed, with explicit forgetting maps

The axis is model-indexed. Neither a global total order nor a complete lattice
of the current observers has been established. IR must parameterize its
vocabulary and its interpretation rather than guess a lattice.

## Existing observations and claim expressibility

| Observer (indexed data) | Claims represented | Existing enforcement |
|---|---|---|
| Field-valued solution sets: `about`, coefficient domain, generators/guards; universe BASE, ALGEBRAIC_CLOSURE, or REAL_CLOSURE (the entire `field.POINT_UNIVERSES`) | EMPTY, NONEMPTY; PREDICATE on points | `field.compatible_point_context`; `check._field_transport_decision` (175); model validation in store |
| A chosen point, coordinates, witness field and point universe | NONEMPTY with witness custody | `check.check_witness_point` (1429); `Atlas.mapWitness`, `existence_does_not_lift_specified_point` |
| Selected structure: REAL isolating interval or COMPLEX selection/box, attached to a named algebraic variable | Selected-root/sign PREDICATE; ordered EMPTY interpretation; selected witnesses | `store._validate_embedding` (143), `check.effective_selected_embedding_identity` (154); `SelectedEmbedding.lean` |
| Expressions in a coordinate ring modulo a defining ideal, or AMBIENT zero ideal | IDENTITY; ZERO/NONZERO atoms require their specified interpretation | `check.effective_origin` (1536), `condition_expressible_at` (1672), `check_identity` (3523), `check_coefficients_in_base` (3009), `check_integral` (3060) |
| Exact indexed family and named members/groups | Family PREDICATE and COUNT; bridge to model claims is separate | `check_families` (2410), `check_evidence_direction` (2525), `store` family_bridge validation; `Atlas.family_member` |

COUNT is not one of the four requested IR claim kinds. Project it as
UNPROJECTABLE rather than silently reinterpret it as a polynomial predicate.
A prose-only PREDICATE also does not supply a machine-readable interpretation.

## Relationships (every pair of the five rows)

A chosen point forgets to NONEMPTY for the same model; `Atlas.PointWitness` and
`mapWitness` expose the data. This forgetful map does not recover a specified
point (`existence_does_not_lift_specified_point`). Selected-point data forgets
selection only when the underlying model/point is fixed; this says nothing
about transporting a sign to another selection. General selected-structure vs
chosen-point observations are UNKNOWN: a selection is not a model solution.

Ordinary points vs selected structure: conditional forgetting as above, not a
global refinement. Ordinary points vs ring identities: evaluation is a quotient
observation on a fixed ring and observer family; it need not be faithful
(`reduced_observation_kills_epsilon`). A general reconstruction equivalence is
UNKNOWN. A chosen point vs ring identities likewise observes via evaluation but
cannot recover ring equality; no global refinement is proved. Selected structure
vs ring identities is UNKNOWN globally: ordering/root selection is extra data,
and reduced selected observers still kill epsilon.

Families vs each of ordinary points, chosen points, selected structure, and
coordinate rings: UNKNOWN without an explicit member/model encoding. The
existing family bridge supplies bounded elimination and binding, not a universal
comparison of these vocabularies. These four UNKNOWN pairs are not proofs of
incomparability. In particular, enumerating vocabulary labels would not establish
their semantic relationships.

Within point universes, BASE -> closure needs a specified field map. The runtime
requires identical point universes; it does not supply all such embeddings or
ACF/RCF transfer. We therefore do not install a global closure-universe lattice.

## Loss needs interpretation and available evidence

Let a vocabulary V at M be predicates/observations on M's state space, with
expressibility `Expresses V c`. For a step S, claim/direction k, and available
premises A, define the unresolved transport obligations by

    lost(S,V,A)(k) := Expresses V k and not
      exists requirement-set R, Profile(S,k,R) and R is discharged by A.

This computes **unlicensed** observations, not necessarily semantically destroyed
information. Failure may be UNKNOWN. Semantic information loss instead compares
the observer-equivalence kernels before/after a specified map: distinguishable
inputs becoming observationally equal. A preservation table alone does not
compute those kernels. The two notions must not be conflated. `IR.lost` uses the
former, explicitly diagnostic notion with discharge indexed in Step; its licence
lemma is an admission theorem, not a reconstruction theorem.

An explicit model context would retain about/computation field, ordered variables,
relations/guards, point universe, and optional selected structure; a vocabulary
would reference that context and an interpretation. Existing fields are data for
this index, not values we may delete and rederive from an enum. Derived projections
could report expressible claim kinds and required gates once those semantics are
fixed. The full relation/lattice remains an abstract parameter in IR v2.
