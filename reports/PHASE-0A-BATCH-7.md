# Phase 0a - complete first pass over deleted tests

The agreed historical-review milestone is complete: all 29 deleted test files were read, and all 226 test functions have a recorded disposition. This is a first-pass test review, not completion of Phase 0a, a full audit of imported implementations, or G0.

## Corpus and execution

Added 52 neutral cases, GP-X73 through GP-X124. The corpus now contains 165 cases: 43 acceptance controls and 122 refusals. Final replay: 158 agreements, four known conservative differences, one diagnostic observation, one pending case and one unsupported case. All pre-existing cases and expectations are preserved byte-for-byte.

The offline historical run selected 197 functions, yielding 271 parametrized instances. All 271 pass across the initial run and the targeted retry. The initial run had 247 passes and 24 failures: 23 came from this review harness incorrectly assuming Windows supplies a non-null executable in its subprocess audit event; one required the missing optional SymPy dependency. The harness was corrected and SymPy 1.14.0 / mpmath 1.3.0 installed in the F: environment. Only those 24 failures were rerun, and all passed. Original failed reports are retained alongside the retry and consolidated results.

This includes full ordered chain face substitution, rederivation of the five reduced source rows, large finite-template compilation, localized contradiction replay, affine-block/residual arithmetic and the selected historical report checks. It does not include the full current release suite, live Singular, companion source regeneration or Lean compilation. Counts overlap earlier batches and should not be summed.

Twenty-nine original functions remain unrun: 27 require companion campaign inputs and two require live Singular. One of the live-CAS scenarios has an independent offline certificate-refusal projection (GP-X77); that does not mark its original backend test as executed. The per-test ledger therefore has 28 blocked dispositions and one extracted-but-unrun original function.

## What the new cases establish

- GP-X73-81 replay exact triangular and boundary isomorphism certificates, with wrong-solution, wrong-cofactor and missing-inverse controls. A bad certificate yields UNVERIFIED, not a mathematical refutation of an isomorphism.
- GP-X82-89 distinguish source commitments, input preflight, ordered reduced solves, actual unit identities and the report's stated limits. The fast chain route does not stand in for full face substitution; the latter passed as a separate historical regression.
- GP-X90-96 replay graded face extraction and reject altered rows, supports, coordinate series, formula windows, outputs and exhausted work budgets. Scratch outer hashes are repinned only where the original mutation tests do so, allowing the intended inner check to run.
- GP-X97-105 cover explicit overlap resolution, incompatible scopes, generic-versus-exceptional fibers, partial coefficient maps and scoped closeouts. These are derived metadata contracts, not newly proved campaign conclusions.
- GP-X106-118 distinguish an exact field-valued point from a failed search, an unresolved cover branch, unilateral recurrence premises, first-order fibers and broader nonlinear claims. The finite recurrence instance is checked, but its generic Lean theorem is not recompiled.
- GP-X119-124 are deliberately small mathematical projections: a nonzero nonunit can still be a zero divisor; rank alone does not make an affine right-hand side compatible; one empty fiber does not empty the parent; cancelling a nonunit can discard an exceptional component. Pinned exact polynomial routines check the identities and counterexample points.

A first draft corpus run exposed an adapter path error: the scratch frontier manifest used an absolute root where the old bundle API requires a relative root. Its positive control failed, so the negative observations from that draft were not taken as evidence. The adapter was corrected and the final run reaches the explicit-resolution and incompatible-scope guards. The immutable draft run is retained for diagnosis.

## Review findings and limits

The historical inverse-coordinate collision test changes state fingerprints first. A separate diagnostic reproduces the actual rejection: step zero's input fingerprint does not match. It does not establish that the inverse-coordinate collision guard was reached. See HISTORICAL-COLLISION-AUDIT.json and its reproducible audit script.

Several other distinctions matter: stored native replay counts are metadata, mocked subprocess summaries are parser tests, source-name assertions are not Lean proof replay, and a fixed projection contract is not a general theorem admission checker. The ledger records these limits instead of turning every passing regression into a neutral mathematical case.

The snapshot contains 112 byte-identical historical GP files totaling 15,874,307 bytes. Every file is pinned by Git blob, SHA-256 and length. All work, caches and temporary artifacts remain on F: where practical. No companion campaign sources were read or harvested and no public repository was changed.

The next bottleneck is current-tree and earlier-history semantic coverage: 23 of 368 current-tree files remain partially reviewed, 345 unreviewed, and none claimed fully reviewed. A24 is still pending and X53 still unsupported. Campaign incident classification and cost analysis await the completed source manifest. No kernel code or Lean spike has begun.
