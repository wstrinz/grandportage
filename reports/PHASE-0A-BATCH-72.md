# Phase 0a — conditional triangular substitution chains

Fully read triangular.py, test_triangular.py, both v1/v2 synthetic certificates and the complete CLI handler. All 20 offline tests pass: exact chains, cofactor mutation, context binding, pivot restrictions, wrong step order, missing substitution, changed fingerprints and CLI authority wording.

Soundness is conditional and local: where the declared coefficient is a unit and normalization equations vanish, the verified affine identity makes the selected equation equivalent to pivot=solution. Substituting that exact solution into every remaining generator preserves their constraints. V2 cofactor identities establish normalization modulo supplied equations, not their membership in the original ideal. The report explicitly leaves interpretation of these equations and units open.

Distinct pivots, pivot-free solutions/context and retained unit variables simplify reconstruction. Solutions may not even depend on future pivots, so the supported class is narrower than arbitrary triangular systems. Final generator lists retain the original variable context: dropping solved equations without reconstruction maps is not equality of loci in that ambient space. Graph binding and forward/reverse point maps remain explicit obligations.

Source receipt IDs/digests are metadata, not fetched receipts. Canonical state fingerprints preserve ordered normalized polynomial lists; they do not prove source provenance or geometric equivalence. The standalone checker shares an arithmetic budget across steps, while its public fingerprint helper does not duplicate all verify preconditions. No new graph-authority route or checker admission is established.

All 352 corpus cases validate unchanged; no expectation, adapter, frozen source, campaign harvest, CAS, Lean work or publication changed. Phase 0 remains active.
