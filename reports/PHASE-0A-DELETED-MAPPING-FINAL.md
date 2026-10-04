# Phase 0a deleted-test mapping: final fixed reconciliation

Source pin: `7991c9052f13e8dcaa78b5eae36f31663e080c1e`. This reconciles only the 42 assertions in `PHASE-0A-DELETED-MAPPING-REVIEW.json` against current corpus payloads and parent closure decisions. It does not reopen the 174-item nonincident disposition or decide the parent-owned Cramer question.

## Result

- 42 historical assertions reconciled: 10 binding-only reuse, 2 bounded mechanism reuse, 8 exact case reuse, 4 minimum residual, 1 split; parent-owned arithmetic judgment, 1 split with minimum residual, 16 supported nonincident.
- Exact reuse requires the same altered premise and refusal/acceptance mechanism. Binding-only reuse is restricted to the relevant digest or source-currentness gate. Positive fixture checks marked nonincident remain source evidence; the cited small cases do not stand in for complete fixture replay.
- Minimum residuals remain at rows 6, 11, 16, 20, and 21. Row 2 preserves an exact exponent-one-versus-two distinction for parent Cramer judgment. No case or source file was changed.

## Assertion-by-assertion disposition

### 0. `test_changed_jump_schedule_is_refused` — Exact case reuse

Source: `tests/test_jc_h3_adjoint_recurrence.py` at historical line 86; review `#/reviews/0`. Prior label: `unresolved`.

Cases: `GP-X321`.

Premise/mechanism: The same pinned unilateral recurrence changes the declared jump schedule from [7,9,11,13] to [7,8,11,13] while keeping the checked sequence and annihilator claim; the validator refuses the J2 premise.

Limit: No broader recurrence theorem is inferred.

### 1. `test_zeroing_depth13_endpoint_refuses_minimal_shift_claim` — Exact case reuse

Source: `tests/test_jc_h3_adjoint_recurrence.py` at historical line 95; review `#/reviews/1`. Prior label: `partial`.

Cases: `GP-X118`, `GP-X318`.

Premise/mechanism: The positive checked depth-13 endpoint and its zeroed counterpart are the same minimum-eighth-shift premise pair; zeroing the entire last nonzero depth removes minimality.

Limit: The case addresses minimality, not every endpoint property.

### 2. `test_exact_affine_and_quotient_replay_classifies_phi_narrowly` — Split; parent-owned arithmetic judgment

Source: `tests/test_jc_h3_b0_compatibility.py` at historical line 36; review `#/reviews/2`. Prior label: `partial`.

Cases: `GP-X119`, `GP-X120`.

Premise/mechanism: The cases distinguish nonzero/nonunit from nonzerodivisor in the affine quotient, the narrow phi classification tested by the frozen fixture.

Limit: The full 3137-term fixture, determinant, resultant, dimensions, guards, and module rendezvous are source evidence. Neither case replays the exact clearing exponent 2 and power-one refutation.

Minimum residual: Parent-owned Cramer judgment: determine whether the exact exponent-two versus exponent-one premise needs a separate bounded control; do not equate the nearby nonunit cases with that arithmetic claim.

### 3. `test_changed_native_binding_refuses_before_replay` — Binding-only reuse

Source: `tests/test_jc_h3_b0_compatibility.py` at historical line 89; review `#/reviews/3`. Prior label: `mapped_outer_hash_only`.

Cases: `GP-X71`.

Premise/mechanism: Changing a source_bindings SHA to all zeroes stales the native source binding before replay, the same digest-currentness gate.

Limit: F3 outer binding only; no native arithmetic replay.

### 4. `test_changed_witness_polynomial_refuses_by_frozen_artifact_digest` — Binding-only reuse

Source: `tests/test_jc_h3_b0_compatibility.py` at historical line 96; review `#/reviews/4`. Prior label: `mapped_outer_hash_only`.

Cases: `GP-X44`.

Premise/mechanism: Changing a witness-polynomial coefficient changes frozen fixture bytes and fails the artifact digest gate.

Limit: F4 outer artifact identity only; not a semantic witness-polynomial check.

### 5. `test_arithmetic_and_scope_mutations_refuse` — Exact case reuse

Source: `tests/test_jc_h3_b0_depth8_free_plane.py` at historical line 87; review `#/reviews/5`. Prior label: `partial`.

Cases: `GP-X324`, `GP-X325`, `GP-X326`, `GP-X327`, `GP-X328`, `GP-X329`, `GP-X330`, `GP-X37`, `GP-X331`.

Premise/mechanism: The positive depth-eight block and eight separately parameterized raw-column, transported-block, graph-effect, D7-sign, residual-label, equivalence-label, CLOSED-open-obligation, and never-inverted-R mutations are represented by these controls.

Limit: The accepted decision is complete for the eight historical mutations; no algebraic invalidity beyond their checked commitments is claimed.

### 6. `test_changed_previous_gp_prerequisite_refuses` — Minimum residual

Source: `tests/test_jc_h3_b0_depth8_free_plane.py` at historical line 94; review `#/reviews/6`. Prior label: `unresolved`.

Cases: `GP-X324`.

Premise/mechanism: GP-X324 is the same unmodified depth-eight block baseline, but its existing mutations do not change the prior-GP prerequisite digest.

Limit: GP-X121/X122 are affine compatibility checks and GP-X71 is a different source digest binding.

Minimum residual: One bounded REFUSE control: retain the checked block and replace only gp_prerequisite.sha256 with 64 zeroes; require C1 prerequisite-currentness refusal.

### 7. `test_changed_native_binding_refuses` — Binding-only reuse

Source: `tests/test_jc_h3_b0_depth8_free_plane.py` at historical line 101; review `#/reviews/7`. Prior label: `mapped_outer_hash_only`.

Cases: `GP-X71`.

Premise/mechanism: Zeroing the named native source binding is the same digest-currentness gate.

Limit: F3 binding only; no arithmetic replay.

### 8. `test_changed_fixture_refuses_by_digest` — Binding-only reuse

Source: `tests/test_jc_h3_b0_depth8_free_plane.py` at historical line 109; review `#/reviews/8`. Prior label: `mapped_outer_hash_only`.

Cases: `GP-X44`.

Premise/mechanism: Changing authority_boundary to widened changes frozen artifact bytes.

Limit: F4 outer digest only; no authority-boundary semantic judgment.

### 9. `test_explicit_residual_pullback_and_finite_unit_replay` — Supported nonincident

Source: `tests/test_jc_h3_b0_depth8_residual.py` at historical line 43; review `#/reviews/9`. Prior label: `partial`.

Cases: `GP-X319`, `GP-X320`.

Premise/mechanism: The finite quotient unit/gcd mechanism is exercised by the exact positive unit and false-gcd controls.

Limit: The full residual pullback counts, 709/4123 terms, exceptional content, and 14-dimensional witness are positive frozen-source observations; no separate false conclusion is attempted.

### 10. `test_scope_pin_order_digest_middle_and_slice_mutations_refuse` — Exact case reuse

Source: `tests/test_jc_h3_b0_depth8_residual.py` at historical line 88; review `#/reviews/10`. Prior label: `partial`.

Cases: `GP-X319`, `GP-X123`, `GP-X332`, `GP-X333`, `GP-X334`, `GP-X335`, `GP-X71`.

Premise/mechanism: The positive finite unit and each historical scope/pin/order/digest/middle/slice mutation are mapped in the parent-accepted six-mutation extraction.

Limit: Each mutation is a distinct fixture premise; the source-digest member remains a binding refusal.

### 11. `test_changed_syzygy_body_refuses` — Minimum residual

Source: `tests/test_jc_h3_b0_depth8_residual.py` at historical line 96; review `#/reviews/11`. Prior label: `partial`.

Cases: none.

Premise/mechanism: No current case changes the sparse r8_1 syzygy-body coefficient itself.

Limit: GP-X334 removes the explanation for a missing middle residual, a different premise.

Minimum residual: One bounded REFUSE control: alter only psi8_certificate.r8_1.sparse.terms[0][1] to -449 in the frozen fixture; require A1 refusal.

### 12. `test_changed_finite_algebra_modulus_refuses` — Exact case reuse

Source: `tests/test_jc_h3_b0_depth8_residual.py` at historical line 111; review `#/reviews/12`. Prior label: `partial`.

Cases: `GP-X336`.

Premise/mechanism: The quotient modulus first coefficient is changed while the finite unit assertion and sliced equations are retained, exactly the historical modulus mutation.

Limit: No claim about all possible modulus edits.

### 13. `test_changed_fixture_refuses_by_digest` — Binding-only reuse

Source: `tests/test_jc_h3_b0_depth8_residual.py` at historical line 118; review `#/reviews/13`. Prior label: `mapped_outer_hash_only`.

Cases: `GP-X44`.

Premise/mechanism: Widening authority_boundary changes the frozen fixture bytes and trips the outer digest.

Limit: F4 only; no semantic promotion check.

### 14. `test_complete_factor_ledger_and_affine_round_trip` — Supported nonincident

Source: `tests/test_jc_h3_b0_free_plane.py` at historical line 38; review `#/reviews/14`. Prior label: `partial`.

Cases: `GP-X73`, `GP-X74`.

Premise/mechanism: The current cases carry the ordered affine normalization and inverse-round-trip mechanism.

Limit: The full factor ledger and exact fixture counts are positive source checks, not distinct attempted invalid conclusions.

### 15. `test_report_has_no_graph_or_research_promotion` — Supported nonincident

Source: `tests/test_jc_h3_b0_free_plane.py` at historical line 53; review `#/reviews/15`. Prior label: `unresolved`.

Cases: `GP-X327`, `GP-X41`, `GP-X89`.

Premise/mechanism: Graph-effect NONE and H3/scope refusal principles are represented by these negative controls.

Limit: The test asserts the original report fields, including six coefficients and four refusal strings; it has no changed premise or attempted promotion. These cases do not reproduce the whole report.

### 16. `test_scope_and_arithmetic_mutations_refuse` — Split with minimum residual

Source: `tests/test_jc_h3_b0_free_plane.py` at historical line 82; review `#/reviews/16`. Prior label: `partial`.

Cases: `GP-X327`.

Premise/mechanism: GP-X327 reuses the graph_effect promotion principle, but on a different depth-eight fixture.

Limit: The historical free-plane test parameterizes seven distinct mutations, including equation/role/open-obligation edits and two arithmetic changes; GP-X328 uses a different D7 sign transport.

Minimum residual: Minimum bounded residual family on the free-plane fixture: graph_effect NONEMPTY; pivot role NINTH_COMPATIBILITY_EQUATION; remove c5_7=0; remove Delta=0; first_open_obligation CLOSED; change VD c8_5 coefficient to 14; change pivot sign to +3/2. Preserve M3 versus A3 refusal distinctions.

### 17. `test_changed_native_binding_refuses` — Binding-only reuse

Source: `tests/test_jc_h3_b0_free_plane.py` at historical line 89; review `#/reviews/17`. Prior label: `mapped_outer_hash_only`.

Cases: `GP-X71`.

Premise/mechanism: Zeroing the free-plane receipt source binding stales source identity.

Limit: F3 binding only; no receipt arithmetic replay.

### 18. `test_changed_fixture_refuses_by_digest` — Binding-only reuse

Source: `tests/test_jc_h3_b0_free_plane.py` at historical line 96; review `#/reviews/18`. Prior label: `mapped_outer_hash_only`.

Cases: `GP-X44`.

Premise/mechanism: Widening the authority-boundary text changes frozen fixture bytes.

Limit: F4 outer digest only.

### 19. `test_zeroed_omega_comb_is_refused` — Exact case reuse

Source: `tests/test_jc_h3_depth8_fiber.py` at historical line 69; review `#/reviews/19`. Prior label: `unresolved`.

Cases: `GP-X322`, `GP-X323`.

Premise/mechanism: The named fiber positive control retains checked nonzero omega_comb; its paired control replaces omega_comb with the exact zero element and refuses the nonzero-dependent conclusion.

Limit: Only this named witness and first-order fiber claim are covered.

### 20. `test_authorizing_depth9_pair_is_refused` — Minimum residual

Source: `tests/test_jc_h3_depth8_fiber.py` at historical line 78; review `#/reviews/20`. Prior label: `partial`.

Cases: none.

Premise/mechanism: No current case changes native_certificate.verdict.depth9_additive_pair_authorized from false to true in this fiber fixture.

Limit: GP-X113/X114/X115 concern neighboring inference/scope claims, not the N7 authorization flag.

Minimum residual: One bounded REFUSE control with the identical fiber fixture except depth9_additive_pair_authorized=true; require N7 refusal without minting a depth-nine pair.

### 21. `test_sparse_body_mutation_is_refused` — Minimum residual

Source: `tests/test_jc_h3_s4_scope.py` at historical line 72; review `#/reviews/21`. Prior label: `unresolved`.

Cases: none.

Premise/mechanism: No current case changes the sparse polynomial C body coefficient in the S4 fixture.

Limit: GP-X106/X107/X117 concern search status, branch, or point-witness conclusions rather than P9 sparse-body integrity.

Minimum residual: One bounded REFUSE control changing only polynomials.C.terms[0][1] to 2; require P9 refusal.

### 22. `test_frozen_digest_is_a_checked_boundary` — Binding-only reuse

Source: `tests/test_jc_h3_s4_scope.py` at historical line 81; review `#/reviews/22`. Prior label: `mapped_outer_hash_only`.

Cases: `GP-X44`.

Premise/mechanism: Re-serializing the frozen JSON with sorted keys changes its checked bytes.

Limit: F5 byte-identity gate only; no source or algebra change.

### 23. `test_frozen_polynomials_compile_to_existing_localized_unit_identity` — Supported nonincident

Source: `tests/test_jc_h3_wall_ob_open.py` at historical line 82; review `#/reviews/23`. Prior label: `partial`.

Cases: `GP-X63`.

Premise/mechanism: GP-X63 exercises the localized unit-ideal identity that the frozen polynomials positively compile to.

Limit: The exact 502/499-term frozen polynomials are source evidence; the case does not replay that complete fixture and the test attempts no false conclusion.

### 24. `test_checked_in_authority_fixture_is_exact_adapter_output` — Supported nonincident

Source: `tests/test_jc_h3_wall_ob_open.py` at historical line 94; review `#/reviews/24`. Prior label: `unresolved`.

Cases: none.

Premise/mechanism: The wall-OB test compares checked-in authority bytes with deterministic adapter output.

Limit: A positive serialization regression guard with no altered premise or attempted false conclusion; digest refusal cases are not equivalent to this equality.

### 25. `test_graph_verdict_mints_only_local_empty_on_exact_consequence_model` — Supported nonincident

Source: `tests/test_jc_h3_wall_ob_open.py` at historical line 100; review `#/reviews/25`. Prior label: `partial`.

Cases: `GP-X63`, `GP-X64`, `GP-X65`.

Premise/mechanism: The local EMPTY claim and refusal to turn a certificate name into wider authority align with these bounded cases.

Limit: The original graph event sequence and exact consequence-model fixture are positive source evidence, not replayed end to end here.

### 26. `test_certificate_name_without_current_verdict_has_no_authority` — Exact case reuse

Source: `tests/test_jc_h3_wall_ob_open.py` at historical line 112; review `#/reviews/26`. Prior label: `mapped`.

Cases: `GP-X65`.

Premise/mechanism: A certificate name without a current checked verdict gives no EMPTY authority, matching the historical current-verdict premise.

Limit: Local p-axis authority only.

### 27. `test_removing_ob_guard_stales_old_authority` — Bounded mechanism reuse

Source: `tests/test_jc_h3_wall_ob_open.py` at historical line 118; review `#/reviews/27`. Prior label: `partial`.

Cases: `GP-X68`.

Premise/mechanism: Removing a required open guard makes a formerly checked receipt stale; GP-X68 tests that same currentness mechanism.

Limit: GP-X68 uses the p-axis t guard, while the deleted test removes the wall-OB guard from a graph event; it does not replay that full event sequence.

### 28. `test_scope_refuses_parent_component_source_and_h3_promotion` — Supported nonincident

Source: `tests/test_jc_h3_wall_ob_open.py` at historical line 135; review `#/reviews/28`. Prior label: `unresolved`.

Cases: `GP-X41`, `GP-X52`, `GP-X64`, `GP-X89`.

Premise/mechanism: The cases bound parent/component/source/H3 or reverse-realization promotion principles.

Limit: The deleted test only asserts original scope strings and not_materialized metadata; it does not attempt a false graph conclusion.

### 29. `test_checked_in_authority_fixture_is_exact_adapter_output` — Supported nonincident

Source: `tests/test_jc_p_axis_authority.py` at historical line 119; review `#/reviews/29`. Prior label: `unresolved`.

Cases: none.

Premise/mechanism: The p-axis test compares checked-in authority bytes with deterministic adapter output.

Limit: Positive serialization regression guard with no changed premise or attempted false conclusion; GP-X44 is not an exact positive match.

### 30. `test_verifier_input_fingerprint_contains_the_frozen_source_digest` — Supported nonincident

Source: `tests/test_jc_p_axis_authority.py` at historical line 218; review `#/reviews/30`. Prior label: `partial`.

Cases: `GP-X71`.

Premise/mechanism: The source digest is visibly included in the verifier input fingerprint, consistent with the source-currentness negative control.

Limit: The string-containment assertion is positive metadata visibility; it does not prove all fingerprint semantics or add a separate invalid conclusion.

### 31. `test_checked_in_boundary_projection_is_canonical_and_scope_honest` — Supported nonincident

Source: `tests/test_jc_source_depth6_authority.py` at historical line 45; review `#/reviews/31`. Prior label: `partial`.

Cases: `GP-X78`, `GP-X79`, `GP-X80`, `GP-X81`, `GP-X82`, `GP-X83`.

Premise/mechanism: The current cases bound projection coordinate/scope principles for the checked boundary.

Limit: The full canonical projection and fixture counts are positive source checks and not replayed by the listed cases.

### 32. `test_native_sparse_coefficient_mutation_breaks_roundtrip_digest` — Binding-only reuse

Source: `tests/test_jc_source_depth6_authority.py` at historical line 63; review `#/reviews/32`. Prior label: `mapped_outer_hash_only`.

Cases: `GP-X40`, `GP-X44`.

Premise/mechanism: Changing a native sparse-map coefficient breaks its committed round-trip digest/binding.

Limit: Only equality and digest integrity are reused; no arithmetic conclusion from the mutated map.

### 33. `test_full_exact_face_replay` — Supported nonincident

Source: `tests/test_jc_source_depth6_chain.py` at historical line 127; review `#/reviews/33`. Prior label: `partial`.

Cases: `GP-X84`, `GP-X86`, `GP-X87`, `GP-X88`.

Premise/mechanism: The cases cover bounded ordered-chain and exact-face principles.

Limit: The deleted test positively replays the complete source fixture and graph_effect NONE; these cases are not the full replay and no false conclusion is attempted.

### 34. `test_full_source_formula_replay_rederives_all_five_rows` — Supported nonincident

Source: `tests/test_jc_source_depth6_face_extraction.py` at historical line 60; review `#/reviews/34`. Prior label: `partial`.

Cases: `GP-X90`.

Premise/mechanism: GP-X90 covers the bounded source-row to face-extraction conclusion.

Limit: The deleted test positively rederives all five rows from the complete formula; GP-X90 is not a full formula replay.

### 35. `test_source_row_coefficient_mutation_breaks_its_digest` — Binding-only reuse

Source: `tests/test_jc_source_depth6_face_extraction.py` at historical line 77; review `#/reviews/35`. Prior label: `mapped_outer_hash_only`.

Cases: `GP-X40`, `GP-X44`.

Premise/mechanism: After repinning the outer fixture, a changed sparse source-row coefficient fails its internal row digest; GP-X40 is the same row-currentness premise.

Limit: Only internal row-binding equality is covered, not downstream face arithmetic.

### 36. `test_dropped_authority_refusal_is_rejected_after_resigning` — Bounded mechanism reuse

Source: `tests/test_jc_source_depth6_face_extraction.py` at historical line 142; review `#/reviews/36`. Prior label: `unresolved`.

Cases: `GP-X89`, `GP-X41`.

Premise/mechanism: Dropping the required H3-promotion refusal after repinning tries to expand authority; GP-X89 rejects that same missing-refusal premise.

Limit: The case uses a chain report rather than the historical face-extraction fixture; it does not replay the exact adapter.

### 37. `test_complete_template_has_the_measured_finite_boundary` — Supported nonincident

Source: `tests/test_jc_source_depth6_full_template.py` at historical line 38; review `#/reviews/37`. Prior label: `partial`.

Cases: `GP-X337`.

Premise/mechanism: The selected-face structural control is compatible with the measured finite boundary.

Limit: The 78/147/25/122 template counts are positive source measurements; GP-X337 is a small structural control, not a full-template replay.

### 38. `test_complete_template_earns_selected_face_containment` — Supported nonincident

Source: `tests/test_jc_source_depth6_full_template.py` at historical line 53; review `#/reviews/38`. Prior label: `partial`.

Cases: `GP-X337`.

Premise/mechanism: Literal selected-generator inclusion gives structural containment without backend search, the narrow mechanism isolated by GP-X337.

Limit: The deleted test uses the complete 147/25 template and a forbidden backend; the small case does not replay all fixture arithmetic.

### 39. `test_mutated_selected_face_loses_structural_authority` — Exact case reuse

Source: `tests/test_jc_source_depth6_full_template.py` at historical line 64; review `#/reviews/39`. Prior label: `partial`.

Cases: `GP-X337`, `GP-X338`.

Premise/mechanism: The positive literal selected generator is paired with a changed selected coefficient 999, removing the structural shortcut and requiring backend fallback.

Limit: This is dispatch authority, not a claim that the mutated polynomial lies outside the ideal.

### 40. `test_authority_still_refuses_reverse_lift_and_h3` — Supported nonincident

Source: `tests/test_jc_source_depth6_full_template.py` at historical line 80; review `#/reviews/40`. Prior label: `partial`.

Cases: `GP-X52`, `GP-X41`, `GP-X89`.

Premise/mechanism: The cases preserve reverse-lift and H3-promotion refusal principles.

Limit: The deleted test asserts refusal strings in the original authority report; no mutation or false conclusion is attempted.

### 41. `test_normalization_bearing_second_face_compiles_with_exact_context` — Supported nonincident

Source: `tests/test_jc_source_ladder_authority.py` at historical line 78; review `#/reviews/41`. Prior label: `partial`.

Cases: `GP-X73`, `GP-X74`.

Premise/mechanism: The ordered affine normalization and inverse mechanism matches the second-face context.

Limit: The five target generators and exact context are positive fixture facts, not fully replayed by these small cases.

## Decision boundary

The six residual-bearing rows identify concrete premises for parent judgment; they are not new cases. All other rows are either exact controls, bounded mechanism/binding reuse, or positive source assertions with no separate invalid conclusion. The companion JSON preserves the full historical test assertion and evidence pointers for all 42 rows.
