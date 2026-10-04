# Phase 2 full-contract layer review

2026-09-30. Policy: phase2-full-contract-layers-v2.

Will's approved rule is applied to the full unchanged fixture: the primary layer owns everything required to pass that fixture. Secondary kernel duties remain visible but never make a mathematical, parser, render or filesystem fixture a kernel test. A custody-only projection is insufficient.

All 459 cases are accounted for exactly once and bound to their original byte hashes. Counts: kernel 79; profile 239; adapter 94; surface 17; host 30. Unresolved: 0. The former 111 pending cases are resolved under the approved rule. The earlier resolved cases were also rechecked. No remaining decision request is needed.

The generator now contains 19 explicit reviewed ID groups. There is no blanket X1-X412 profile assignment or numeric fallback. An ID absent from the catalog becomes unresolved, retains all possible primary layers including kernel, and blocks kernel selection. Each row records a review group, rationale, source evidence pointers, secondary layers and corresponding duties. The validator checks those fields against the reviewed policy as well as coverage, source hashes, types and consistency.

## Boundary decisions

- GP-X211 is host: complete storage roundtrip/dedup behavior. Canonical bytes and bound evidence identity are secondary duties.
- GP-X230 is host: actual process/recording behavior; completion creates no mathematical claim.
- GP-X302 is adapter: canonical composition exports. Exact algebra replay is a profile duty and intermediate receipt identity a kernel duty.
- GP-X370 is adapter: legacy format-8/epoch-11 migration is outside the native kernel fixture contract.
- GP-X388 is surface: unknown frontier status must be projected honestly; its secondary kernel duty retains open debt.
- GP-A27-partial is kernel: admission success is explicitly supplied synthetically; quotient scope does not establish the requested full group.
- GP-X09, GP-A01 and GP-A08a are kernel: mathematical truth is assumed, while the required existence/reach rule is absent.
- GP-X175 is kernel: the supplied success/proof-mutation sequence tests stale stored binding, with no polynomial/cofactor content to replay. A secondary profile duty requires mathematical validation of any replacement certificate.
- GP-X193-X198 are kernel finite recorded-use coverage. Both asserted dimensions and construction/conclusion uses are supplied explicitly. Place repair cannot discharge order debt, and a conclusion-only use still requires its index. This does not establish mathematical universe completeness or constraint strength.
- Native point/cofactor/chain and ordered SOS fixtures stay profile when their complete contract requires mathematical replay, including GP-X02, GP-X45, GP-X134 and GP-X308. Binding failures alone cannot discharge them.
- Supplied frozen report mutation contracts GP-X35-X44 and GP-X97-X116 are adapter, with retained scope, premise and identity duties recorded separately.

## Verification and G2 limit

Ran: python -B -m unittest discover -s tests -p test_layer_tags.py -v; python -B tools/check-layer-tags.py. All 16 tests pass. Generation and validation preserve all original fixture bytes, and all 459 hashes match the previous registry. git diff -- corpus/must is empty.

Tests cover incomplete coverage, duplicate IDs, stale hashes, malformed metadata, policy contradictions, secondary-duty consistency, removed reviewed IDs, unresolved kernel candidacy, and the agreed concrete boundaries. The inventory regressions check both dimensions, the conclusion-only use, empty recorded-use limits, and independence from profile-like labels; the stored-proof regression checks the supplied mutation and replacement duty. G2 result eligibility requires reviewed kernel-primary policy and a runner's complete-fixture pass attestation. It rejects secondary-only coverage, projection-only passes, incomplete passes and forged retagging. The metadata query lists candidates only; these checks execute no oracle and establish no G2 conformance pass.

Only the five assigned metadata/tool/test/report files were edited. No shared docs, Lean files, source cases, commits or pushes were changed by this worker.

Active charge for this refinement: 23 minutes total, including the final three-minute inventory/binding correction, review, implementation and verification. The earlier metadata assignment's 15-minute charge is separate.
