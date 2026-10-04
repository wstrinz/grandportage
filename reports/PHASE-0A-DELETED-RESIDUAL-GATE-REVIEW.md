# Phase 0a deleted-test residual gate review

Source pin: `7991c9052f13e8dcaa78b5eae36f31663e080c1e`. Static screen of prior residual rows 6, 11, 16, 20, and 21; row 16 contributes seven separate mutations. The parent is integrating the separate Cramer controls for row 2.

## Finding

All 11 screened mutations stop at a prerequisite binding, sparse/native commitment, fixed projection, or fixed verdict equality gate. None reaches an independent arithmetic replay that would justify a new neutral case on this evidence. Existing cases cover each reached mechanism at its stated scope. The historical source tests still record exact fixture regressions; mechanism reuse does not claim full fixture replay. Smallest genuine neutral residual after this screen: **none**.

## Gate-by-gate screen

### Row 6: gp_prerequisite.sha256 -> 64 zeroes

- Reached gate: **C1: prior-GP record must equal the literal fixture/sha256/required_result tuple and the previous fixture bytes must match their expected hash** (prior-dependency binding equality).
- Existing principle cases: `GP-X71`, `GP-X72`, `GP-X324`.
- Match: GP-X71 rejects a changed cited digest; GP-X72 rejects changed native parent bytes. GP-X324 supplies the unchanged necessary-block baseline. The historical mutation changes only a digest string in a prior-GP dependency record.
- Limit: This is a previous-GP prerequisite, not the p-axis source binding in the small cases. The C1 short circuit does not revalidate the previous adapter or test affine round-trip on the altered record.
- Frozen code: `oracle/history/checkout/tests/test_jc_h3_b0_depth8_free_plane.py:94-98` (historical mutation); `oracle/history/checkout/experiments/jc_h3_b0_free_plane/depth8_adapter.py:264-275` (C1 literal record and byte hash; C2 downstream previous-adapter check); `oracle/history/checkout/experiments/jc_h3_b0_free_plane/depth8_adapter.py:456-471` (validation order: projection, C1, native, arithmetic).

### Row 11: psi8_certificate.r8_1.sparse.terms[0][1] -> -449

- Reached gate: **A1: parsed residual lengths and sparse digests must equal the unchanged certificate commitments** (sparse-body digest binding).
- Existing principle cases: `GP-X325`, `GP-X40`.
- Match: GP-X325 changes an actual checked coefficient while retaining its native commitment; GP-X40 states that an old row commitment cannot bind changed content. The changed valid coefficient reaches the residual sparse-body digest mismatch.
- Limit: The small cases do not replay r8_1 or the 552/704/709-term syzygy. This historical mutation stops at A1 before the A2 identity Psi8=c2_3*r8_1+2*r8_3 is checked.
- Frozen code: `oracle/history/checkout/tests/test_jc_h3_b0_depth8_residual.py:96-100` (historical mutation); `oracle/history/checkout/experiments/jc_h3_b0_free_plane/depth8_residual_adapter.py:587-604` (A1 digest/length before A2/A3 algebra); `oracle/history/checkout/experiments/jc_h3_b0_free_plane/depth8_residual_adapter.py:832-851` (validator call order).

### Row 16: projection.graph_effect NONE -> NONEMPTY

- Reached gate: **M3: entire projection must equal _expected_projection()** (fixed projection/scope equality).
- Existing principle cases: `GP-X327`.
- Match: GP-X327 changes graph_effect on another necessary-block projection and rejects graph promotion without authority.
- Limit: Different fixture and label value; no independent graph check follows the M3 mismatch.
- Frozen code: `oracle/history/checkout/tests/test_jc_h3_b0_free_plane.py:72-73` (parameter 1); `oracle/history/checkout/experiments/jc_h3_b0_free_plane/adapter.py:129-173` (expected graph effect and scope); `oracle/history/checkout/experiments/jc_h3_b0_free_plane/adapter.py:362-376` (M3 before native/arithmetic).

### Row 16: c7_4_affine_pivot.role DETERMINATION_NOT_COMPATIBILITY -> NINTH_COMPATIBILITY_EQUATION

- Reached gate: **M3: entire projection must equal _expected_projection()** (fixed projection/role equality).
- Existing principle cases: `GP-X327`, `GP-X115`.
- Match: GP-X327 shows the fixed projection cannot be relabelled while reusing its checked receipt. GP-X115 is contextual evidence that a solved coordinate has a constrained role, but it changes the role in the opposite direction; no current case tests a false ninth equation itself.
- Limit: The NINTH_COMPATIBILITY_EQUATION label is a semantic distinction not directly represented by those cases. This historical test stops at literal M3 projection inequality and does not count or replay a ninth equation.
- Frozen code: `oracle/history/checkout/tests/test_jc_h3_b0_free_plane.py:74-75` (parameter 2); `oracle/history/checkout/experiments/jc_h3_b0_free_plane/adapter.py:140-159` (pivot role and eight downstream equations); `oracle/history/checkout/experiments/jc_h3_b0_free_plane/adapter.py:362-376` (M3 gate).

### Row 16: remove c5_7=0 from projection.model.equations

- Reached gate: **M3: entire projection must equal _expected_projection()** (fixed model-equation binding).
- Existing principle cases: `GP-X67`, `GP-X124`.
- Match: GP-X67 refuses reuse of a receipt after its equations change; GP-X124 shows an exceptional factor cannot be cancelled without invertibility. The source model requires c5_7=0 for its bounded factor ledger.
- Limit: No check is made that the claimed factorization is actually false on the widened model; the deletion stops at M3.
- Frozen code: `oracle/history/checkout/tests/test_jc_h3_b0_free_plane.py:76` (parameter 3); `oracle/history/checkout/experiments/jc_h3_b0_free_plane/adapter.py:129-159` (model equations and factor scope); `oracle/history/checkout/experiments/jc_h3_b0_free_plane/adapter.py:362-376` (M3 gate).

### Row 16: remove Delta=0 from projection.model.equations

- Reached gate: **M3: entire projection must equal _expected_projection()** (fixed model-equation binding).
- Existing principle cases: `GP-X67`, `GP-X124`.
- Match: GP-X67 covers stale receipt after equation change; GP-X124 covers attempted cancellation of a nonunit exceptional factor. The source explicitly refuses ambient freeness before imposing Delta=0.
- Limit: No arithmetic replay on the widened model follows the M3 mismatch; this is the same equation-binding gate as the c5_7 deletion with a distinct source premise.
- Frozen code: `oracle/history/checkout/tests/test_jc_h3_b0_free_plane.py:77` (parameter 4); `oracle/history/checkout/experiments/jc_h3_b0_free_plane/adapter.py:129-166` (Delta equation and ambient refusal); `oracle/history/checkout/experiments/jc_h3_b0_free_plane/adapter.py:362-376` (M3 gate).

### Row 16: projection.first_open_obligation -> CLOSED

- Reached gate: **M3: entire projection must equal _expected_projection()** (fixed open-obligation/status equality).
- Existing principle cases: `GP-X37`, `GP-X329`.
- Match: GP-X37 refuses to turn a completion label into a missing proof; GP-X329 refuses marking an unexported residual available by relabeling status. The historical edit is likewise a declaration-only closure.
- Limit: Neither case checks the six named depth-eight coefficients; the M3 gate does not discharge that obligation.
- Frozen code: `oracle/history/checkout/tests/test_jc_h3_b0_free_plane.py:78` (parameter 5); `oracle/history/checkout/experiments/jc_h3_b0_free_plane/adapter.py:169-171` (six-coefficient open obligation); `oracle/history/checkout/experiments/jc_h3_b0_free_plane/adapter.py:362-376` (M3 gate).

### Row 16: columns.VD.c8_5 first coefficient -> 14

- Reached gate: **A3: hashes of all four live native coefficient bodies must equal unchanged certificate hashes** (coefficient-body/native-commitment binding).
- Existing principle cases: `GP-X325`, `GP-X40`.
- Match: GP-X325 changes a raw coefficient while retaining its native commitment; GP-X40 captures stale row commitment. The historical edit changes a valid sparse coefficient and is refused at A3.
- Limit: The later A6 pure-b generator equality and S2 substitution checks are not reached; this assertion does not independently establish an arithmetic counterexample.
- Frozen code: `oracle/history/checkout/tests/test_jc_h3_b0_free_plane.py:64-65,79` (parameter 6); `oracle/history/checkout/experiments/jc_h3_b0_free_plane/adapter.py:279-320` (A3 hash before A6 generator equality); `oracle/history/checkout/experiments/jc_h3_b0_free_plane/adapter.py:362-376` (arithmetic call after scope/native).

### Row 16: columns.d7rung:row1/c9_7.c7_4 first coefficient -> 3/2

- Reached gate: **A3: hashes of all four live native coefficient bodies must equal unchanged certificate hashes** (coefficient-body/native-commitment binding).
- Existing principle cases: `GP-X325`, `GP-X40`.
- Match: GP-X325 changes a raw coefficient under a fixed native commitment; the pivot-sign edit reaches the same A3 commitment failure.
- Limit: The later A7 signed pivot identity and A10 affine round-trip are not reached. GP-X328 changes projection transport text rather than this native coefficient, so it is not an exact match.
- Frozen code: `oracle/history/checkout/tests/test_jc_h3_b0_free_plane.py:68-69,80` (parameter 7); `oracle/history/checkout/experiments/jc_h3_b0_free_plane/adapter.py:279-320` (A3 hash before A7 pivot equality); `oracle/history/checkout/experiments/jc_h3_b0_free_plane/adapter.py:340-350` (later affine round-trip); `oracle/history/checkout/experiments/jc_h3_b0_free_plane/adapter.py:362-376` (validation order).

### Row 20: native_certificate.verdict.depth9_additive_pair_authorized false -> true

- Reached gate: **N7: entire scoped native verdict must equal the pinned literal with depth9_additive_pair_authorized=false** (fixed verdict/authority field equality).
- Existing principle cases: `GP-X113`, `GP-X65`.
- Match: GP-X113 refuses a higher-order nonlinear inference from a first-order fiber exclusion without a checked bridge; GP-X65 refuses authority from a certificate declaration alone. Flipping this flag asserts an unsupported stronger result, and N7 only checks the pinned verdict object.
- Limit: Neither case tests a depth-nine additive pair on this exact fiber. The N7 mismatch occurs before N8 omega_comb nonzero and any additional witness checks; the test does not replay a depth-nine obstruction.
- Frozen code: `oracle/history/checkout/tests/test_jc_h3_depth8_fiber.py:78-84` (historical mutation); `oracle/history/checkout/experiments/jc_h3_depth8_fiber/adapter.py:148-165` (N7 full verdict equality before N8); `oracle/history/checkout/experiments/jc_h3_depth8_fiber/adapter.py:263-276` (validator call order).

### Row 21: polynomials.C.terms[0][1] -> 2

- Reached gate: **P9: sparse digest of C must equal the unchanged native reconstructed fitting-condition digest** (sparse-body/native-receipt binding).
- Existing principle cases: `GP-X325`, `GP-X40`.
- Match: GP-X325 changes a checked coefficient under fixed native commitment; GP-X40 captures stale content commitment. The S4 edit changes C but retains the native fitting-condition digest.
- Limit: The source mutation is not a witness counterexample. P9 precedes P10/P11 leading-slice checks and W1-W4 exact K-point evaluation, so those arithmetic conclusions are not reached.
- Frozen code: `oracle/history/checkout/tests/test_jc_h3_s4_scope.py:72-78` (historical mutation); `oracle/history/checkout/experiments/jc_h3_s4_scope/adapter.py:80-86` (sparse digest definition); `oracle/history/checkout/experiments/jc_h3_s4_scope/adapter.py:362-413` (P9 before term/slice/point arithmetic).

## Closure boundary

This gate screen downgrades the five earlier minimum-residual labels to bounded mechanism or binding reuse. It does not modify the earlier fixed reconciliation, create cases, or adjudicate the parent’s final closure. A future demand for exact source-fixture regression replay would be a separate testing objective; it is not evidence of a missing neutral inference case here.
