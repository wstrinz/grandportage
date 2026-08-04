# Foundations and prior art

**Purpose.** A bounded research note for Grand Portage (GP), not a claim of
novelty and not a design commitment.  It was written against kernel epoch 8,
`OPERATION-CONTRACTS.md`, `REVIEW.md`, and the current Lean shadow.  In
particular, Lean already has models-as-predicates, inclusion transport,
predicate pullback and composition, mapped equivalence, freshness-aware
evidence licensing, and the saturation/elimination/point-lift contracts.  The
questions below are about compressing or strengthening what remains; they do
not reopen those results.

## Adopt now

### Assurance-case vocabulary: use the distinctions, not the authority model

[SACM 2.3](https://www.omg.org/spec/SACM/2.3) provides a useful interchange
vocabulary for separately identifiable claims, argumentation, and evidence.
GP already makes the more important separation: an immutable artifact, parsed
answer, validation mode, provenance freshness, semantic relation, and licensed
conclusion are different facts.

Use these correspondences in documentation and review:

| GP | closest assurance-case idea | important difference |
|---|---|---|
| refusal | a challenge to a proposed inference | it is a *static transport prohibition*, not automatically a defeater |
| counterexample to a cell | defeater that is sustained | mathematical countermodel; it closes that licence generally |
| accepted finding/debt | recorded residual doubt or risk acceptance | administrative visibility only: it never restores a refused inference |
| current validation | evidence applicability/freshness | GP's `Licenses` makes freshness an executable precondition |
| replaced evidence | supersession/history | retain history, but only the current evidence may authorize a new edge |

This last distinction is non-negotiable.  Assurance 2.0 treats defeaters as
recorded doubts that may be developed, resolved, or retained as residual
doubts; it deliberately discusses confidence in the resulting case
([Bloomfield, Netkachova, and Rushby](https://arxiv.org/abs/2405.15800),
[confidence note](https://arxiv.org/abs/2205.04522)).  A GP refusal can instead
mean a proved non-transport theorem, an ill-typed claim, missing evidence, or a
deliberately conservative boundary.  None is a numerical reduction in
confidence.  Do **not** introduce confidence scores or let `accept` become an
authority override.

Small operational consequence: accepted findings should remain queryable with
reason, accepting revision, covered inputs/epoch, and a `superseded_by` or
`retracted_by` link when applicable.  That improves the read surface identified
in `REVIEW.md`; it must be implemented only with an append-only history and
with the invariant that acceptance has no effect on `Licenses`.

### Certificates: keep small, replayable algebraic envelopes

The current checker already has the right shape: the search backend is not the
authority, while explicit finite equalities are independently re-expanded.
This matches the standard proof-producing pattern: a membership certificate is
a cofactor identity `f = Σ h_i g_i`; a unit/emptiness certificate is the special
case `1 = Σ h_i g_i`; saturation and radical claims require the corresponding
power witness before that identity is replayed.  A checked Gröbner envelope
needs both generator provenance and its finite critical-pair/reduction facts,
not merely a printed basis.

That is consistent with existing proof-checker work based on algebraic
certificates ([Chaieb--Wenzel](https://www.cl.cam.ac.uk/~lp15/Grants/Chaieb-case.pdf))
and with current work that treats cofactor representations as ideal-membership
certificates ([Hofstadler--Verron](https://arxiv.org/abs/2302.02832)).  Preserve
the current distinction between certificate-replay, named-backend decisions,
and verifier-native structural facts; collapsing all three under “certificate”
would hide the TCB rather than shrink it.

## Bounded research questions

### R1. Relational transport core (one Lean spike; no runtime rewrite yet)

Institution theory is the nearest broad ancestor: an institution packages
signatures, sentences, models, translations/reducts, and a satisfaction
condition that is invariant under change of notation
([Goguen--Burstall technical report](https://www.lfcs.inf.ed.ac.uk/reports/86/ECS-LFCS-86-10/)).
It is not GP's calculus as-is.  GP edges can be deliberately lossy relations,
and GP claims include point existence, emptiness, scope, and provenance facts
rather than only sentences preserved by a signature morphism.

The sharper candidate is a binary point relation `R : A -> B -> Prop`, with
two predicate transformers:

```text
R_exists(X)(b) = exists a, X(a) and R(a,b)       -- direct image
R_forall(Y)(a) = forall b, R(a,b) -> Y(b)        -- universal pullback
R_exists(X) subset Y  iff  X subset R_forall(Y)  -- Galois connection
```

This separates three facts currently easy to conflate: a relation maps source
points into target points, it is total on source points, and it is
surjective/liftable over target points.  The proposed Lean spike should define
these notions and derive, under named hypotheses, the EMPTY/NONEMPTY variance,
everywhere-predicate transport, identity, and relational composition.  Then
instantiate it for inclusion, maps, equivalences, and point-lift covers; record
which current operation-contract facts fail to instantiate.  The latter result
would be valuable: it identifies real multi-sorted/partial evidence rather
than forcing it into a relation.

The connection to approximation theory is structural, not a proposal to add
abstract interpretation: existential image and universal preimage form the
standard adjoint pair behind sound over/under-approximation.  Use the
Galois-connection test only to state exactly which direction a lossy operation
licenses; do not infer a “best abstraction” or a new optimizer from it.

Success criterion: fewer primitive point-cell proofs with all present Lean
countermodels and operation distinctions preserved.  Stop if the necessary
side conditions (scope, coefficient expressibility, partial maps, or claim
syntax) dominate the relation; those belong in typed contracts, as the current
`Conditions.lean` result already suggests.

### R2. Evidence lifecycle and defeaters (data-model design, after live use)

Investigate a minimal append-only lifecycle vocabulary: `active`,
`superseded`, `retracted`, and `accepted-for-triage`, each referring to an exact
event and reason.  Ask whether a proposed inference should carry a first-class
challenge record (source, target, premise, and disposition), borrowing the
*traceability* discipline of SACM/Assurance 2.0 without importing their
confidence calculation.

Acceptance test: a fresh reader can distinguish active blockers, historical
refusals, and consciously carried work, while a property test confirms that no
lifecycle state ever changes the transport verdict or makes stale evidence
current.  This directly addresses the existing “no retraction mechanism” and
read-surface risks; it should not precede more live campaign evidence.

### R3. Certificate interface inventory (only when a repeated bottleneck appears)

Inventory each deployed algebraic result by proposition, exact ring/field,
inputs, certificate equations, checker, and resulting GP authority.  Include:

* ideal membership / unit ideal: cofactor identity;
* saturation: exponent plus `f g^n` membership identity;
* radical membership: exponent plus `f^n` membership identity;
* Gröbner elimination: basis provenance, span witnesses, order, and critical
  pairs; and
* local rational lift charts: denominator powers, guarded identities, radical
  fallback, and exhaustiveness.

This is an audit inventory, not a universal proof language.  The recent
LPAC/Pacheck line demonstrates that replayable polynomial proofs can be
compressed and reuse patterns can reduce checking costs
([Kaufmann--Hofstadler](https://arxiv.org/abs/2507.20267)).  Consider it only
if GP measures certificate size, repeated subproofs, or replay time as a real
cost; GP's current plain equalities maximize independent auditability.

## Defer

* **SACM serialization, W3C PROV export, or assurance confidence scores.**
  They improve exchange or management, not the semantic authority kernel.
* **A wholesale institution/category redesign.**  First test R1 against the
  concrete point cells and operation contracts.
* **Math-in-the-Middle/MMT/OpenMath integration.**  Math-in-the-Middle is a
  central ontology and shared vocabulary for interoperability
  ([OpenDreamKit paper](https://arxiv.org/abs/1603.06424)); MMT adds formal
  theories and type systems ([MMT documentation](https://uniformal.github.io/doc/language/index)).
  OpenMath is an extensible semantic representation standard
  ([OpenMath 2.0r2](https://openmath.org/standard/om20-2019-07-01/)).  All are
  promising *vocabulary/interchange* layers for ring, map, ideal, and
  certificate names, but none decides that a particular artifact is current,
  verified, or licensed.  Revisit only once GP has multiple backends or a
  demonstrated interchange need.
* **A universal certificate algebra.**  Different GP authorities intentionally
  have different semantic payoffs (ideal exactness versus point lifting, for
  example).  Preserve those distinctions until repeated adapters prove a
  common intermediate language earns its complexity.

## Source posture

The standards and project documentation above are primary sources; the three
research papers are direct author preprints/venues.  They establish useful
neighbours and terminology, not that GP is an instance of any one framework.
