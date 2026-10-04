# Phase 0a - CAS program and transport custody

Read cas.py lines 1-690 and 735-835; together with Batches 74-75 this completes source text reading. Semantic review remains partial. Three bounded controls use injected runners and one isolated scratch graph; no live Singular execution.

CASProgram validates constructor inputs, but stores mutable lists and renders them again at execution. A shadowing statement rejected in the constructor reaches the injected runner after body mutation and its mock complete transcript parses. This contradicts the absolute non-bypassable wording for direct Python callers; no live CAS or external-input exploit is claimed.

run_cas persists caller-supplied program.generators, not parsed output generators. A synthetic run emitting x records a model with supplied generators [1]. This creates a declaration, not an operation or contraction verdict; output-to-model provenance wording is stronger than the enforced binding.

Transport validates type and selected field relationships, but does not resolve source or prove maps before execution. Source existence and graph structural compatibility are checked later during append, as previously tested in Batch 16. Mapped substitutions and drops also retain caller-owned data until event construction.

Aborted runs persist an artifact plus an attempt note and mint no model. CAS errors, nonzero non-abort exits and parsing errors raise before run_cas persistence; those failure classes do not receive the same durable attempt record.

Successful recording persists objects before fold-validated append, so failed append can leave content-addressed orphans. This is not crash-atomic graph persistence or proof of relation semantics.

Program semantic fingerprints include rendered text, ordering and outputs but omit generators metadata used to declare the resulting model. A fingerprint therefore binds the execution request, not every model declaration field.

GP_SINGULAR_ARGV uses whitespace split, so quoted executable paths/arguments with spaces are not preserved. Identifier matching uses dollar rather than fullmatch and the expression/body guard remains an acknowledged denylist, not a typed language proof.

Proposed fixes are explicit immutable validated snapshots, output/model binding, consistent failure custody and structured argv. These remain design considerations, with no frozen code change. All 352 corpus cases validate unchanged. Phase 0 remains active; campaign manifest and later Lean cap prerequisites still apply.
