# Grand Portage x Jacobian source-depth-6 coordinator packet

> **Resolution (2026-08-01):** JC commit `cb3136c` delivered the requested
> ordered certificate and native replay checker. GP independently replays all
> 23 solves and two residuals and welds both endpoints. GP subsequently derived
> the 25 faces from five exact reduced rows and bound the complete finite model.
> JC d4a18b4 now freezes the conditional normalized-root-to-row seam; the
> coefficient-level original-pair-to-normalized-root map remains explicitly
> open. No actual-source or H3 authority has been minted.

**Date:** 2026-07-31
**Audience:** lead JC implementation/coordinator agent
**Purpose:** request the smallest native proof-carrying artifact needed to connect the actual-source depth march to the boundary polynomials already checked by Grand Portage (GP).

## Reference state

- JC research tree: `9fe68c2`
- GP released base: `63dea8d` (`v0.20`); the source-depth-6 consumer is currently isolated WIP above that base.
- Native JC receipt: `d2_plane_72_108/f2_h3_source_depth6_receipt.json`
- Native receipt SHA-256: `3c9954943d94faf8122ef556aa7248454d3d3d03e460747c6d55c0d3bc4a1464`
- GP adapter: `experiments/jc_h3_source_depth6/adapter.py`
- GP frozen projection: `fixtures/jc_source_depth6/boundary_v1.json`
- GP authority tests: `tests/test_jc_source_depth6_authority.py`
- More detailed field-level request: `experiments/jc_h3_source_depth6/NATIVE-RECEIPT-REQUEST.md`

## Executive request

Please preserve the native discovery pipeline and add a companion certificate for the exact actual-source march from the already-established second face through depths 2--6. The certificate should let an independent checker replay the ordered substitutions and recover the two terminal residuals.

GP-native JSON is neither requested nor preferred. Stable native fields plus a native replay checker are ideal; the isolated GP adapter will translate them afterward.

## What GP already checks

The current adapter independently:

- imports the 3,262-term `R2B` and 6,124-term `beta` sparse polynomials and recomputes their native digests;
- verifies the exact boundary witness `R2B = -5*c2_3*c8_7*t` on the declared stratum;
- verifies that `beta` remains nonzero after `c4_5 = c2_3^2 / 4`;
- verifies the generic `alpha != 0` affine solve through a structured mapped-ring isomorphism;
- verifies that the discriminant branch collapses exactly to `beta = 0`;
- persists a backend-free GP campaign with five models, two `VERIFIED` edges, and no findings;
- backstops the generic and discriminant branch laws in Lean.

This currently earns authority only for those two boundary-stratum rewrites. It deliberately earns no actual-source edge, chart cover, source membership, or H3 conclusion.

## The one blocking gap

The frozen native receipt records 33 ladder rungs by term count and SHA-256 only. Those commitments are good provenance, but a hash is not algebraic evidence: GP cannot reconstruct or independently check that the ordered substitutions lead from the actual-source E-system to `R2B` and `alpha*c7_5 + beta`.

Because the top and second faces have already been consumed elsewhere, the smallest new artifact consists of:

- 20 ordered rungs at depths 2--5;
- three solved rungs at depth 6; and
- the two pivot-free residual rows at the depth-6 boundary.

## Preferred deliverable: exact ordered step records

For each solved step, retain:

- depth, row, source slot, and pivot coordinate;
- the exact equation after all prior substitutions, in the native sparse format;
- the exact pivot coefficient and its declared `t`-unit witness;
- the exact solved value, in the native sparse format;
- any explicit cofactor modulo `15*t^3 + 1` used for normalization;
- input and output state fingerprints; and
- the ordered prior substitutions represented by that state.

For the pivot-free rows `E[2,21]` and `E[3,22]`, retain the exact final post-substitution equations and exact receipts identifying them with `R2B` and `alpha*c7_5 + beta`. Include normalization cofactors when equality is modulo the pin rather than literal ambient equality.

Suggested companion artifacts in `math-stuff/d2_plane_72_108/`:

- `f2_h3_source_depth6_chain_certificate.json`
- `f2_h3_source_depth6_chain_verify.py`
- `F2_H3_SOURCE_DEPTH6_CHAIN_CERTIFICATE.md`

It is fine to leave the frozen existing receipt unchanged and add these beside it.

## Compact alternative

If expanded states are prohibitively large, provide a closed exact straight-line program from the second-face state to the 23 solved values and two residuals. Its bounded instructions may use addition, multiplication, rational scaling, substitution, and reduction by an explicit multiple of `15*t^3 + 1`. Bind the program, input state, output maps, and variable order by full digests.

A reusable recurrence theorem with exact initial conditions and a finite list of exceptional boundary steps is also acceptable if its semantics is checked in Lean.

## Acceptance criteria

The native artifact is ready for the GP lane when:

1. An independent replay starting from the second-face state reconstructs every ordered step and both final residuals, including the published native digests.
2. Reordering steps, omitting a prior substitution, or changing a state fingerprint is rejected.
3. Mutating a pivot coefficient, declared-unit witness, solved value, or normalization cofactor is rejected.
4. Mutating a final residual coefficient is rejected.
5. The checker states clearly whether each equality is literal in the ambient ring or only modulo the pin.
6. The producer writes the receipt atomically, so interrupted long runs cannot leave a plausible partial certificate.

The producer may remain computationally expensive. The frozen certificate and its independent replay should be reasonably quick and deterministic.

## Explicit non-goals

- Do not rerun an approximately 85-minute computation merely to reassert the same hashes.
- Do not migrate the JC discovery implementation into GP.
- Do not design a general formal-series framework for this request.
- Do not put GP integration on the critical path for ongoing mathematical discovery.
- Do not infer source membership, chart coverage, or H3.
- Do not classify the ideal generated by `R2B` and `beta`; that is a separate research question.
- Do not reserialize the already-covered top and second faces if the second-face input state can be bound exactly.

## Handoff back to the GP lane

Please report:

- the landed JC commit;
- certificate and source-receipt digests;
- the exact replay command, result, and approximate runtime;
- the stable field schema;
- whether normalization is ambient or modulo the pin; and
- any remaining asserted or unmaterialized transition.

GP will then freeze a bounded projection, translate it through the isolated adapter, add mutation/refusal tests, and seek only the narrow actual-source necessary-condition authority supported by the certificate.

## Bottom line

The final boundary algebra is already proof-carrying and independently checked. The next valuable JC deliverable is not more evidence about the endpoint; it is a compact, replayable witness for the ordered source-to-boundary composition seam. That is what will let GP turn a persuasive native calculation into a licensed transition without absorbing the research engine.
