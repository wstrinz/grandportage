# Theory ledger

Append-only notes from the non-authoritative Lean shadow. Entries identify an
existing theory, record a refutation/compression, or leave a bounded question
open. Runtime disagreement is a finding; Lean is not the source of authority.

## Identifications

- **2026-08-24 — kernel epoch 11: selected structure is a separate gate.**
  `SelectedEmbedding.lean` models the two-root conjugation counterexample and
  the safe identical/omitted-selection cases. `selected_embedding_identity`
  is not a fifth identity-rewriting gate: it is the first explicit member of
  an extra-structure-preservation family for predicates that read an ordering
  or selected embedding. `modeledKernelEpoch` is pinned to 11 and CI compares
  it with the runtime epoch.
- **2026-08-24 — structure context is not certificate scope.** EMPTY
  certificate scope describes stability under field change. A selected
  embedding instead belongs to the model-side validity context read by a
  predicate. The shadow keeps these axes separate rather than stretching
  `CertificateScope` until two different mechanisms share one name.

- **2026-08-23 — point transport as predicate transformers.** Existential
  image and universal precondition form the familiar adjunction behind
  over/under approximation. Totality and surjectivity determine variance;
  predicates still need correspondence along the relation.
- **2026-08-23 — transport table as preservation table.** Several point rows
  are domain-specific instances of model-theoretic preservation under
  extensions or morphisms. A proposed new edge type should first exhibit a
  coherent relation class and preservation profile.
- **2026-08-23 — certificate scope as stability.** `CertificateScope.lean`
  makes the two-level registry an admission interface: each kind supplies a
  stability theorem or a counterexample, and derived scope is maximal among
  justified scopes.
- **2026-08-23 — runtime scope is an atom-under-scheme poset.** Exact declared
  field scopes are incomparable atoms below field-independent `SCHEME`, not a
  single undifferentiated lower point. All eight builtin kinds now name a Lean
  decision: the five identity/integer shapes are extension-stable; nonsquare,
  bounded rational-point search, and carried citations retain countermodels.
  The citation countermodel formalizes missing transported justification, not
  a claim that the cited theorem itself is intrinsically field-relative.

## Refutations and compressions

- **2026-08-23 — four identity gates are not one gate.** `Conditions.lean`
  separates smaller-ideal origin, expressibility, carries/reflects, and
  partiality. A single `Carries` gate would license a false descent.
- **2026-08-23 — ambient identity is not a primitive gate.** It is
  contravariant identity transport from the zero ideal.
- **2026-08-23 — totality cannot type predicates.** Even a total and
  surjective relation transports unrelated predicates only after an endpoint
  correspondence premise is supplied.
- **2026-08-23 — negative witness evidence is not extension-stable in
  general.** Adding a witness destroys `NoWitness`; a field-relative
  certificate therefore needs a countermodel, not a prose label.

## Open questions

- Epoch 11 deliberately defers symmetric `conjugate_of` custody, exact
  nontrivial complex-box isolation, mandatory campaign-wide embedding scope,
  general ordered ambient fields, authored required-map certificates, and
  quotient-normalized endpoint/map fingerprints. These are conservative
  refusals, not missing licences in the current kernel.
- A preservation-theorem audit may compare the bounded table with ACF/RCF
  transfer principles, but current `REAL_CLOSURE` support is not a general
  Tarski-transfer rule: it checks selected univariate signs and exact selected
  endpoint identity only.

- Audit every transport row against a named preservation theorem or retained
  countermodel; use the result as the admission test for a seventh edge type.
- Study whether a typed claim language dissolves the expressibility gates.
  This is a study question, not authorization to redesign runtime claims.
- Keep certificate-typed transportability as the possible novel object. Wait
  for ARR15 and another foreign domain before extracting a paper-level theory.

## Atlas audit after v0.34.0

- `Atlas.lean` adds bounded Isabelle-style quantifier transfer, data-level
  witness mapping, restriction of stability, and proved/refuted/unknown
  stability knowledge. These are independent Lean statements, not imports of
  external prover theorems. Predicate relatedness remains an explicit premise.
- The canonical epoch-12 reach model separates class instantiation from concrete
  field extension. `instantiate_sound` proves target-class membership;
  `orderedReach_stable` and `char0Reach_stable` are membership-stability laws,
  not algebraic certificate-validity theorems. The 139-row Python/Lean comparison
  supplements the historical Boolean scope registry, which remains legacy.
- `orderedSOS_contradiction` proves contradiction from a replayed evaluated
  equality, zero cofactor terms, and explicit ordered-arithmetic laws. Polynomial
  parsing/evaluation, concrete field laws, and receipt binding remain outside
  that proof. Equality alone is not the contradiction interpretation.
- `preservation_polarity` states the elementary antitone correspondence between
  operation classes and their common preserved claims. It organizes known
  preservation facts; it does not prove unknown table entries or minimality.
- A square-zero/nonzero example proves that reduced observations kill epsilon.
  Ordinary field points therefore miss information needed for coordinate-ring
  equality; a general functor-of-points reconstruction is not formalized here.
- No false kernel licence was reproduced. IMAGE_CLOSURE/ALONG/EMPTY is a
  conservative refusal with a possible stronger geometric rule, pending checked
  authority and point interpretation. No transport licence changed.
- The primary-source mapping and outstanding algebraic obligations are in
  [ATLAS-MAPPING-V0](../docs/ATLAS-MAPPING-V0.md); the bounded research sequence is
  in [PRESERVATION-ATLAS-PROGRAM](../docs/PRESERVATION-ATLAS-PROGRAM.md). Trocq's
  sufficient constraints and its constraint solver must not be represented as
  a proved globally minimal semantic requirements theorem.

- **Certificate interpreter continuation:** `CertificateInterpreter.lean`
  supplies a small expression language and proves equational derivations sound
  under evaluation. `certificate_empty` derives the evaluated equality from the
  derivation and vanishing cofactor terms from the model equations.
  `sample_derivation` proves the x²+1 SOS example, and `integer_laws` plus
  `integer_order` discharge the concrete integer interpretation. An explicit
  Gaussian-integer solution preserves equality but rules out the ordering.
  The Python parser, rational normalization, and general field libraries remain
  outside the proof. `InterpreterParity.lean` serializes this exact example for
  Python replay and comparison with the graph fixture.
