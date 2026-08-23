# Theory ledger

Append-only notes from the non-authoritative Lean shadow. Entries identify an
existing theory, record a refutation/compression, or leave a bounded question
open. Runtime disagreement is a finding; Lean is not the source of authority.

## Identifications

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

- State concrete stability theorems for every runtime builtin certificate
  kind, including the algebraic premises hidden by the Mathlib-free model.
- Audit every transport row against a named preservation theorem or retained
  countermodel; use the result as the admission test for a seventh edge type.
- Study whether a typed claim language dissolves the expressibility gates.
  This is a study question, not authorization to redesign runtime claims.
- Keep certificate-typed transportability as the possible novel object. Wait
  for ARR15 and another foreign domain before extracting a paper-level theory.
