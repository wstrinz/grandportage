# A bounded preservation-atlas program

This is the research continuation of [the v0 mapping](ATLAS-MAPPING-V0.md).
The first implemented slices ship in v0.35.0; they do not claim a new general
preservation theorem. Here “metamath” means the broader
study of mathematical transfer, not an implementation in the Metamath prover.

The next slice is now implemented in
[CERTIFICATE-INTERPRETER-V0](CERTIFICATE-INTERPRETER-V0.md): an explicit
integer-expression derivation/evaluation proof with an ordered integer instance
and an unordered counterexample, plus graph composition and stale-receipt tests.
This completes a bounded B instance and the ordered-certificate part of C.

## The question worth pursuing

For a mathematical change of representation or context, what must be preserved
to carry a particular conclusion, and what checked evidence establishes those
requirements for this occurrence of the change?

Separate four judgments:

1. **Meaning:** the source and target claims have well-defined interpretations.
2. **Preservation:** the semantic operation preserves this kind of claim under
   explicit premises.
3. **Evidence:** an artifact and its interpreter establish those premises.
4. **Binding:** the evidence applies to these endpoints, this payload, and this
   current graph state.

The first two judgments have extensive prior art. The last two make GP's audit
problem interesting. A theorem can be true while its cited receipt is stale;
a certificate equality can replay while its proposed contradiction interpretation
is invalid; a map can preserve existence while losing custody of a witness.
An atlas that collapses these distinctions would erase what GP is useful for.

## First results, now implemented

The mapping accounts for every point and identity cell and identifies the
non-table gates. The new Lean module proves several small, independently stated
laws; its scope is explicit rather than hidden in certificate names. The Python
and Lean reach implementations agree on 139 canonical decisions. Mutation tests
ensure the comparison rejects missing, duplicated, malformed, or changed output.
Hosted CI passes the build, both parity commands, and the Python test lanes.

The implementation deliberately leaves the graph format, epoch, certificate
verifiers, and transport licences intact. The visible GP change corrects
`gp table` and marks the old Boolean stability registry as legacy. These changes form the v0.35.0 release; subsequent research remains incremental.

## The atlas has its own preservation correspondence

Let O be operations, C be interpreted claim classes, and write o ⊨ c when o
preserves c under the fixed semantic convention. Define:

    commonClaims(X)     = { c | every o in X preserves c }
    commonOperations(Y) = { o | o preserves every c in Y }

Then:

    Y ⊆ commonClaims(X)  iff  X ⊆ commonOperations(Y).

`preservation_polarity` proves this elementary antitone correspondence. Adding
operations can only shrink the claims common to them. Applying both operators
gives a closure construction, suggesting a disciplined way to group edges by
their preservation profiles. This construction is elementary, not a novelty
claim and not a method for proving the initially unknown cells.

Its practical consequence is a better edge-admission question: does the proposed
edge add a coherent operation class with a demonstrably different preservation
profile, or merely rename existing operations? A finite atlas can answer the
second question relative to its admitted claim vocabulary. It cannot establish
that two operations agree on all possible mathematics.

## Observation is an independent axis

The model should specify what an observer can see: ordinary points, an actual
witness and its coordinates, polynomial identities modulo an ideal, order and
selected roots, or an indexed family member. These observations distinguish
different equivalences of the same underlying presentation.

For example, epsilon is nonzero in a dual-number algebra but epsilon squared is
zero. Any zero- and multiplication-preserving observation into a structure with
no nonzero square-zero elements kills epsilon. The new Lean example proves this
directly. It explains why even adding more *field-valued* point observations
cannot recover the nilpotent information needed by GP's IDENTITY claims.
Allowing observations in algebras with nilpotents opens a different question;
this motivates a future functor-of-points dictionary, not a present runtime
feature. See the primary Stacks source [in the mapping](ATLAS-MAPPING-V0.md).

## Evidence interpretation is more promising than a single scope lattice

A certificate should be understood through an interpreter with requirements.
For SOS, replay establishes an equality. The contradiction proof then uses
ordered arithmetic. For an ideal-combination certificate, the interpretation
uses algebraic evaluation and nonzero constants. Those requirements differ even
if two current certificates happen to earn the same reach tag.

Consequently a tag such as ORDERED is a compact result of interpretation, not a
replacement for it. NONE records missing authority; unknown, refuted, and proved
stability should remain distinct. The new `StabilityKnowledge` demonstrates this
separation but is not wired into runtime state.

The next useful proof is an end-to-end *small* certificate: a formally evaluated
polynomial identity, its cofactor vanishing, and a contradiction in an explicit
algebraic interface. The current ordered theorem starts at the evaluated equality.
Moving that boundary one step toward the actual verifier would strengthen GP
more than adding many certificate-name declarations.

## Composition is the next experiment

One-step cells cannot describe all useful failures. A chain may preserve a
conclusion while losing the evidence needed to continue, or remain syntactically
connected while changing a selected embedding or point universe.

Use a small matrix of routes, with expected outcomes fixed in advance:

| Route | Required distinction | Observable success criterion |
|---|---|---|
| Ordered certificate R → Q | Reach-class instantiation versus concrete field extension | EMPTY interprets within ORDERED; unrelated point transport still refuses R → Q |
| Ordered certificate R → C | Equality versus contradiction | Equality replay can survive; EMPTY authority refuses |
| Q ideal certificate → F_p | Field change versus specialization | No invented Q → F_p field embedding or inherited CHAR_0 reach |
| Image → closure → chosen closure point | Existence versus witness custody | Existence alone cannot discharge the requested lift |
| Exact family → member → model | Universal elimination versus binding | Listed member, coverage, group evidence, and model agree |
| Point equivalence → identity rewriting | Observation vocabulary | Nilpotent counterexample blocks point-only authority |

Live validation also exposed an operational version of the custody question:
an unavailable backend-identification result is cached for the process lifetime.
A later computation may answer while authority remains unavailable. Retrying
identification can be useful, but a successful later probe must never silently
certify an earlier execution whose identity was not established. Recovery needs
an explicit per-execution provenance argument; this audit does not change it.

The ordered-certificate routes now have graph tests; the unsupported
point-universe change is rejected at graph construction. This work does not
claim to have added all six graph-level fixtures. The proofs and parity cover parts of their
semantics. Existing runtime tests cover many adjacent cases; each new experiment
should identify the additional failure mode it would detect before adding tests.

## What “minimum requirements” must mean

At least three different questions are possible:

- A sufficient rule proves transport under a set of premises.
- A solver finds the least available annotation satisfying a fixed rule system.
- Those premises are necessary for every semantic implementation of the claim.

Trocq already provides a sophisticated version of the second question; its
journal paper explicitly separates its sufficient tables from conjectured
minimality. GP should not advertise the third result after implementing the
first or second. The primary paper and exact sections are in the mapping.

For a GP prototype, use a finite premise vocabulary and enumerate candidate
assignments. Each positive cell needs a theorem under exactly those premises.
Each claimed necessary premise needs a countermodel when removed, within the
same model class. Failure to find a countermodel is UNKNOWN. Multiple
incomparable sufficient sets should remain alternatives rather than being
collapsed into a misleading single “weakest” label.

This requirement calculation should initially be diagnostic and must not grant
runtime authority. Admission into GP would additionally need evidence producers,
verifiers, binding rules, and retained negative controls.

## Ordered work packages and stopping conditions

| Package | Concrete deliverable | Admission / stopping condition |
|---|---|---|
| A: current audit | 56-cell mapping, Lean laws, read-surface fix, parity | Delivered here; do not call interface proofs full verifier verification |
| B: one certificate interpreter | Polynomial evaluation bridge for one existing certificate shape | A checked example and a changed-context counterexample; otherwise retain explicit gap |
| C: composition experiment | A minimal graph fixture for each new failure mode above | Current context and evidence custody visible at every step |
| D: requirements prototype | Finite relation-premise solver with proof/countermodel links | Necessity claims only where deletion countermodels are retained |
| E: foreign-domain comparison | One non-polynomial domain using the same four judgments | Reuse must explain a real refusal or eliminate duplicated machinery |
| F: broader theory | Precise comparison with Isabelle, Trocq, and partial Galois transport | Demonstrable result beyond terminology alignment before novelty claims |

Package B has a bounded integer-expression instance, and C has the ordered
certificate experiments linked above. The rest of C and packages D–F remain
follow-on research. A new edge type or claim language should wait for those experiments.
The IMAGE_CLOSURE/ALONG/EMPTY opportunity should be taken only when its checked
geometric premise and point-universe interpretation can be exhibited together.

The next target is to extend B to rational normalization or explicit algebra
homomorphisms, then test C with a second certificate interpretation. That tests
reuse where GP can supply evidence and counterexamples, while leaving the larger
theory open to being refined or rejected by the results.
