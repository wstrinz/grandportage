# Grand Portage v0.33.0 authority-boundary release

Graph format **7**, kernel epoch **11**, collected checks **1,716**.

This release centralizes the point where checked verdict evidence becomes
current, event-backed graph authority. It is deliberately behavior-preserving:
no graph schema, verifier identity, input fingerprint, transport-table cell, or
Lean theorem changes. Epoch-12 field reach and family/model composition remain
a separate semantic release.

## Authority binding

All ten existing verdict subjects now pass through
`grandportage.authority.check`, `bind`, and `project` during graph fold. The
binder records the event and semantic input fingerprint, verifier identity and
version, kernel epoch, and execution provenance that made the evidence current.
Subject-specific proof objects replay against the exact graph state before an
`AuthorityReceipt` is minted.

The receipt types are sealed internal values. This prevents ordinary package
callers from accidentally skipping the checker/binder path; it is an API
construction boundary, not a hostile-code security mechanism. Receipts remain
on the folded in-memory graph and are never written to graph JSONL, so existing
files remain byte-compatible.

The projection matrix is unchanged. Stale verdicts remain history-only.
Malformed representation evidence projects nothing. Rejected elimination and
point-lift proof objects retain their current historical verdict without
erasing authority established by an earlier accepted proof.

The pure checker still consumes folded authority, declarations, and kernel
rules to license or refuse transport. Those check-time decisions are not
misrepresented as verifier receipts.

## Review hardening included

- `gp review` offers a cold-reader-safe full-history view, including supported
  supersession chains, without requiring live CAS access.
- Point-witness verification rejects free symbols before constructing or
  launching a CAS program.
- Quotient identities are explicitly labelled vacuous when a current verified
  unit-ideal anchor already proves that the model is the zero ring.

These diagnostics add no event field or verdict and grant no new authority.

## Compatibility and deferred work

Existing graph-format-7 / epoch-11 logs need no migration. Existing verdicts
remain current under exactly the prior epoch, verifier, backend, and input
fingerprint rules. No release-specific artifact is needed to read old logs.

Field reach, family-to-model composition, new semantic context bindings, and
the certificate-specific migration matrix remain gated for v0.34 / epoch 12.
The acceptance matrices and counterexamples are retained in
`review/v0.32-preflight/README.md` and `review/v0.32/SOL-HANDOFF.md`.

Exact release validation and artifact digests are recorded in
`review/v0.33/validation.txt`.
