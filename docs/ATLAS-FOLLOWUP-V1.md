# Follow-up: interpreter requirements, custody, and the next experiments

v0.35.0 is released. This work continues on a separate review branch and grants
no new runtime authority. The feedback is useful, with three qualifications:

1. Partiality blocks generic point transport, not every specialization result.
   The mapping already retains integral AMBIENT identity transport ALONG under
   its separate coefficient and map obligations.
2. Closure under a finite observation vocabulary is a relative admission test.
   Equality of profiles does not establish that two operations have identical
   evidence producers, binding obligations, or semantics beyond that vocabulary.
3. A general absence claim for a theory of custody is premature. W3C's
   [PROV constraints](https://www.w3.org/TR/prov-constraints/) already specify
   consistent provenance histories, derivation, invalidation, and normalization.
   [Proof-carrying authorization](https://www.cs.princeton.edu/research/techreps/337)
   already composes proof components for context-dependent authorization goals.
   These are adjacent comparisons, not claims that either subsumes GP. A useful
   research question is how independently replayed mathematical evidence, its
   interpreter requirements, and changing endpoint bindings compose together.

## Decision: keep the core Mathlib-free for this slice

The existing `Operations`/`Laws` boundary suffices for operation transport and
unit-ideal interpretation. Keep the default build small and dependency-free.
Before rational normalization, use a separately pinned Mathlib integration
package to discharge the interfaces for standard field structures. Standard
real-number infrastructure exists in
[Mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Real/Basic.html).
Do not commit to an untested dependency/toolchain combination now.

Mathlib would supply library instances and lemmas, not a proof of GP's Python
parser, resource-bounded normalization, or receipt binding. Conversely, Mathlib
is not logically required to state a universally quantified interface theorem;
it is the practical route to connecting it to standard mathematical structures.
No claim of soundness for every standard ordered field is added by this work.

## Second interpretation: unit cofactors

`UnitInterpreter.lean` proves `unit_certificate_empty` from a syntactic
`Derivation` of `sum h_i*f_i = 1`, generator vanishing, `Laws`, and `1 != 0`.
The explicit example is `1*x + 1*(1-x) = 1`. The shared calculus gains the
ordinary one-times law, discharged by the integer instance. The contradiction
uses no ordering or characteristic-zero premise. A zero algebra satisfies the
same `Laws` and the example equations, proving that nontriviality cannot simply
be deleted from this model class.

This is not a full rational-coefficient theorem. The exact Python checker also
accepts the integer example in characteristic two, but rejects `1=(1/2)*2`
there. Denominator validity is a real requirement of rational interpretation.
GP's CHAR_0 tag remains a conservative projection of the current Q verifier;
the new Lean theorem does not broaden that runtime policy.

The new native graph test uses the real unit-ideal producer and recorded
verification: Q -> R -> Q -> C succeeds after verification; the same prefix
followed by specialization to F_2 refuses. Fresh F_2 verification independently
earns FIELD_SPECIFIC(F_2), but does not reopen the Q-origin inference. Changing
the Q generators while retaining the receipt removes current authority and
closes the route. Unlike the ordered example, C is a permitted target.

This is a second graph interpretation, not a new serialization parity gate:
the unit example's Lean proof and Python model are explicitly written, while
the existing automated example serialization still covers the ordered sample.

## Package D: first bounded diagnostic inventory

Run `python scripts/atlas_requirements.py`. The model class is arbitrary
cofactor lists and points in `Operations + Laws`. The three available premises
are DERIVATION, GENERATOR_VANISHING, and NONTRIVIAL. Available means assumed;
an absent premise is not assumed false. The conclusion is inconsistency of all
available premises at a point.

The eight subsets yield one PROVED cell, four REFUTED cells using the retained
zero-algebra countermodel, and three UNKNOWN cells. The positive link is
`unit_certificate_empty`; the negative witness combines `zeroAlgebra_laws`,
`unit_sample_derivation`, and `nontriviality_deletion_countermodel`. Absence of a
retained proof or countermodel stays UNKNOWN, even if an elementary argument
could settle it. Incomparable supplied sufficient sets remain alternatives.

The solver minimizes only within the supplied catalog. It neither discovers
Lean proofs nor checks a correspondence between Python premise names and Lean
types. That dictionary is a review obligation; the Lean declarations themselves
are checked by the aggregate build. Every row has authority NONE. This is one
interpreter profile, not the full 56-cell requirements atlas or a novelty claim.

## Package E: choose the domain before building an adapter

A geometric realization campaign is not automatically an independent
non-polynomial test merely because its input is a graph. A full census may also
be outside that campaign's approved work. Do not build census machinery to
manufacture an adapter use case.

A suitable next target is an existing finite combinatorial classification with
an executable completeness checker: meaning fixes labeled versus isomorphism
classes; preservation fixes the quotient/cover relation; evidence checks both
coverage and exclusions; binding fixes the input universe, canonicalizer, and
checker version. The experiment must explain an actual refused promotion or
remove duplicate validation. A toy relabeling of GP family fields alone would
not pass package E's admission condition. No foreign-domain reuse is claimed.

## Operational custody

The failure cache and post-execution identity snapshot are now in REVIEW.md's
attack surface. A new regression keeps an earlier execution's unavailable
identity unchanged after a later successful identification. It uses a test
adapter and makes no claim of native authority. Retry policy is unchanged;
proving recovery safe requires per-execution identity and mixed-trace checks,
not merely deleting failed cache entries.

## Validation and next boundary

The Lean aggregate builds 32 jobs. The new native composition test passes
against Singular 4.2.1; it does not depend on a fake backend granting authority.
The bounded inventory and cache-recovery controls run in deterministic CI.
A full non-live run and existing parity gates are recorded with this review.

Next: expand the requirements inventory only with retained theorem/countermodel
pairs; select a real independent classification consumer; introduce a pinned
Mathlib adapter when rational/standard-field interpretation becomes the next
proof obligation. No second release is implied by these research additions.
