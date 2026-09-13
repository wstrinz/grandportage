# Reading IR v2 (diagnostic specification)

`IR.lean` contains the four runtime claim kinds, indexed statement syntax,
model-indexed vocabulary, algebraic context, six relation-class instances,
conditional preservation profiles with alternative premise sets, evidence,
per-execution binding, and a licence derivation tree. Profiles and vocabulary
interpretation are parameters. String predicate/state references require an
external interpretation; integer Expr is not a general rational parser.

`Licence.leaf` requires expressibility, a valid receipt, and current binding.
`Licence.step` retains all premise licences, nonempty premises at its source,
its target, the applicable profile alternative, actual discharge, and current
bindings for both evidence and step. `licence_step_admission` excludes claims
outside the expressibility/covered-profile intersection. `lost` computes
unlicensed observations under available discharge; it does not assert irreversible
information loss. `profile_polarity` instantiates the existing atlas polarity.
`sound` is induction under explicit leaf and step interpretation hypotheses;
it proves no Python parser, normalizer, backend identity, or binder correct.

## What is implicit, and what format 8 already stores

The packet's claim that only Preservation is first-class is too strong.
`ARCHITECTURE.md` section 3 already describes checked evidence, context binding,
and sealed authority receipts. Models, statements, verdict representations,
verifier versions, fingerprints, family bridges, and inference premises exist.
The following are missing **reified relationships/proofs**, not necessarily
missing information requiring a new storage format:

| Procedural obligation (current source line) | IR field / obligation |
|---|---|
| `check._field_transport_decision` 175: reach instantiation vs point-context compatibility | Claim.context + Step.profile's context premises |
| `check.effective_selected_embedding_identity` 154 | Vocabulary interpretation + selected-structure correspondence |
| `check.condition_expressible_at` 1672 and `check_coefficients_in_base` 3009 | Statement typing at each model; context-bound expression reference |
| `check.audit_inference` 349–375: predicate rewriting across a path | Step justification for the source/target statements, not only kind |
| `check.effective_exact_contraction` 1563 and image gates 1842–1880 | Profile alternatives plus evidence of exactly the needed premise |
| `check.effective_certificate` 1881, `provenance.current_verdict` | Evidence interpreter/requirement profile distinct from its reach projection |
| `check.audit_inference` 239–288: exhaustive coverage and all premises | Licence tree; nonlocal partition/family constructors retain coverage and each premise binding |
| `check.check_stale_paths` 2324 and provenance/binder freshness | Binding of step endpoints/payload/state and each execution identity |
| `check.check_unexhibited_witness` 1351 | Claim vocabulary distinguishing existential truth from chosen-witness custody |

These exceed the packet's five-item investigation threshold, but most can be
exposed as a read model. Existing `family_bridge` is already explicit; lack of
its model-independent semantics in this prototype is an IR limitation, not a
new defect in format 8. `SPEC.md`'s older scope paragraph still describes the
Boolean certificate-kind summary; the epoch-12 implementation is more precise.
This audit records that discrepancy without changing runtime rules.

All relation-class instances here are conditional mathematical specifications.
Necessary-condition/restriction share left-total relational content; additional
algebraic distinctions stay in profiles. Closure, field-map, and specialization
premises are parameters. No theorem silently assigns these properties to GP's
edge labels. Projection must retain unresolved predicates, never manufacture them.

## Read-model continuation

Licence.partition and Licence.family now represent nonlocal joins, with explicit
coverage/member premises and individual bindings. The old co-location limitation
above describes the initial prototype. grandportage/explain.py classifies each
of the nine obligations as REIFIED, DATA_GAP or ADAPTER_GAP. A REIFIED data tree
is conditional on the interpretation hypotheses of IR.sound, not a Lean proof
serialized by Python. See IR-V2-CORPUS-REPORT.md for the withheld measurement.
