# Phase 0a — localization caller and representation boundaries

Fully text-read localization.py, ordered_sos.py and test_localization.py, plus complete localized_unit_ideal, ordered_sos and localization CLI handler definitions. LOCALIZATION-REVIEW.json records hashes, definition intervals, mathematical arguments and remaining implementation obligations. All 29 localization source tests pass; their injected backends and provenance do not establish live CAS execution.

Six small controls reproduce two representation defects. A valid sparse guard verifies directly and through JSON CLI output. Default text output emits the VERIFIED header, then raises uncaught TypeError while joining guard dictionaries as strings. Render guard values explicitly before joining and verify the complete successful output path. Preserve this as a reporting crash, not an ordinary mathematical REFUSE.

Equivalent infix guards x and x+0 are rejected as duplicates, but infix x plus its sparse representation is accepted. Canonical values preserve representation type, so uniqueness compares different keys. Repeated inversion is mathematically harmless here; this is a mismatch with the distinct-after-normalization contract. A proposed fix is representation-independent canonical keys, subject to explicit contract disposition.

The membership and chain soundness arguments remain narrow. Inverting every guard lets a checked guard-multiple identity imply localized zero. Chain induction from r_0=1 yields a guard monomial modulo the ideal; a zero final remainder proves that exact open model empty. Neither establishes ambient or parent emptiness. Existing transport tests include direct field mutation, while other tests exercise persisted proof replay; these are distinct evidence strengths.

Resource limits are per helper/row, not one shared request budget. The chain caps guards and steps but not generator count; generator normalization creates fresh arithmetic budgets. No stress-cost bound is claimed. Ordered SOS admits a rational identity that contradicts an ordered-field point; downstream point-scope admission and its full tests remain next.

Corpus, expectations, adapters, frozen oracle and immutable latest replay are unchanged. No campaign harvest or Lean spike occurred. Phase 0 remains active.
