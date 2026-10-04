# Exact contraction without a valid-evaluation lift: neutral candidate

## Pinned source

Read `lean/GrandPortage/OperationContract.lean` from read-only predecessor `$DEV/grand-portage` at commit `ac4155787207e2847d248cffed7be871d5dcd577`. Blob `c805f85ff1288553f855daf072695578afebde2d`; SHA-256 `7c9afad6ba96f38f352554b778d2e9e01a1cb37f540a477da12e8f2042838196` (829 lines).

- Lines 182-185 define exact contraction as `J g ↔ I (embedding g)` for every retained `g`.
- Lines 322-341 require a valid evaluation for each affine point and define point-surjectivity by a source lift for every target point. Lines 343-349 say a polynomial section additionally carries `precompose_valid` and `retract_embedding`.
- Lines 767-795 instantiate the identity embedding with `zeroI` at **both** endpoints. Source valid evaluation is always false, target valid evaluation always true. Exact contraction holds by identity; a concrete target point exists; a source lift would require a false validity proof.
- Lines 799-812 provide the positive contrast: with `anyValidEvaluation` at both ends, the identity map lifts every target point. The rest of that theorem addresses predicate expressibility separately.

## Smallest candidate

**Negative conditional rule — REFUSE.** Source and target rings are `Int`; embedding is identity; source and target ideals are `zeroI`; evaluation codomain is `Unit`. Supply exact contraction as a checked premise. The target has the constant `Unit` evaluation and it vanishes on `zeroI`. Every source evaluation is declared invalid. Refuse the conclusion that exact contraction alone makes the projection point-surjective: the target point has no valid source lift.

**Positive contrast — ACCEPT under the added premise.** Keep the same rings, ideals, embedding and target point, but allow every source evaluation. The target evaluation itself is a source lift, and identity embedding preserves retained coordinates. This isolates the missing valid-evaluation premise without changing ideal equality.

This is a design only; no GP-X identifier or case has been added. `incompleteEliminationParams` is the name of a shared parameter record, but theorem 778 uses `zeroI` for both ideals, so this candidate is not the earlier strict-lower-target completeness example.

## Existing cases and observation route

| Case | What it observes | Missing from this residual |
|---|---|---|
| `GP-X07` | Exact contraction does not by itself authorize geometric closure for predicate transport. | No target point, validity predicates, or point-surjectivity conclusion. |
| `GP-X360` | A Gaussian target root is missed by the integer source under an operation map. | Its payload does not assert exact ideal contraction. |
| `GP-X05`/`GP-X06` | Predicate transport with point-surjectivity supplied as a premise; expressibility changes the verdict. | Neither derives a lift from contraction. |

**Current observation: `UNSUPPORTED` (null observed verdict).** `oracle/ROUTES.json` supplies `exact_contraction` and `point_surjective` separately. `tools/check-corpus.py:118-135` passes those arguments to `kernel.transport`; the pinned kernel signature at `oracle/checkout/grandportage/kernel.py:975-982` and branch at 1184-1207 consume point-surjectivity as an input. The `q3_map` route in `tools/q3_map_probes.py:12-51` handles fixed Z-to-Z[i] controls and has no abstract evaluation-predicate or exact-contraction check.

A future reference-only route could check the finite identity/zero-ideal model and its all-valid contrast. It would be a new observation path, not a Lean or native verifier verdict. None was built or run here.
