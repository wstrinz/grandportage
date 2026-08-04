# JC H3 depth-6 generated GP status projection

This is a machine-owned projection of the GP aggregate replay ledger. It is
not the JC truth ledger and has not been installed into any JC file.

<!-- GP-STATUS-BLOCK:BEGIN schema=gp-status-block/v1 -->
```json
{
  "aggregate_graph_effect": "NONE",
  "authority_ceiling": "CONDITIONAL_NORMALIZED_ROOT_TO_DEPTH6_BOUNDARY_ONLY",
  "binding_digest_algo": "sha256-lf-normalized",
  "bindings": {
    "boundary_fixture": "sha256:4a0cf6999dedf3334e4e9f0b5918303757cdd857b88090017319ab0c87eff991",
    "chain_certificate": "sha256:d5ed44977e1f39312fbd2d30a286f686a0cd26d55dba237420a7a3d2bf513f15",
    "conditional_seam_fixture": "sha256:970515c9548833ee253a64302b8aa5950849ad8cd54fa0bc375d22770156934a",
    "graded_face_fixture": "sha256:6c8887034321884b6bb0aa7cd8cf04d90e472a36f4a6ba4035a53e7eda1aa8a1",
    "r1_r7_native:f2_original_pair_root_normalization.py": "sha256:117e0befbf0a195b85e2d11368f4085ffa0bfd650e410bbafb89fdd6e6adb89a",
    "r1_r7_native:f2_original_pair_root_normalization_manifest.json": "sha256:4d930a9465f1e54d57bf4b5095c1ab0242e78a132e856c6f4e9fbfdffb79db09",
    "r1_r7_native:f2_r6_shear_forcing.py": "sha256:9002b3759c1341aa76e3b5ef5f7edfbc9e490d30ba6539fdad91f71a2a425e76",
    "r1_r7_native:f2_r6_shear_forcing_manifest.json": "sha256:d9c3926f74054c5febb47256626a772fe965d69d0391e55336abe854ddce35eb",
    "r1_r7_native:f2_reduction_certificate.py": "sha256:5ff3faf543ba01e3e6e06f7e79d1120c667fac2836ed27de1a5c41dae07d9da0",
    "r1_r7_native:f2_residual_y_bound_frame.py": "sha256:0953c6f42fd4d54e861b6a213fbdac168be4d49b0bfb1337633ad1ec31b34428",
    "r1_r7_native:f2_residual_y_bound_frame_manifest.json": "sha256:c62748d41f9cfe120990d2739eb963dba4306ebe4a4f03e21e157b380ec9e793",
    "r1_r7_seam_fixture": "sha256:e8b849d772b0a06c1afea60870576930bcc70aef261420e086c8ac5768dde982"
  },
  "ledger_schema": "gp-jc-h3-depth6-milestone-replay/v2",
  "not_supported": [
    "original polynomial-pair membership",
    "source-image sufficiency or reverse lift",
    "chart or branch coverage",
    "H3 promotion",
    "(75,125) verdict change"
  ],
  "open_frontier": [
    {
      "blocks": [
        "original polynomial-pair membership",
        "source-image sufficiency",
        "reverse lift",
        "chart or branch coverage",
        "I4=I1=Im1=0",
        "H3 promotion",
        "(75,125) verdict change"
      ],
      "id": "R5",
      "premises": [],
      "status": "CHECKED_PREMISE_BOUND",
      "why_open": "selected monic depressed cubic face is an inherited premise"
    },
    {
      "blocks": [
        "original polynomial-pair membership",
        "source-image sufficiency",
        "reverse lift",
        "chart or branch coverage",
        "I4=I1=Im1=0",
        "H3 promotion",
        "(75,125) verdict change"
      ],
      "id": "R6",
      "premises": [
        "actual_pair",
        "source_polynomiality",
        "gap5"
      ],
      "status": "OPEN_NONMONOMIAL_FRAME_CONVERSION",
      "why_open": "exact non-monomial eqq1 -> psi2 conversion"
    },
    {
      "blocks": [
        "original polynomial-pair membership",
        "source-image sufficiency",
        "reverse lift",
        "chart or branch coverage",
        "I4=I1=Im1=0",
        "H3 promotion",
        "(75,125) verdict change"
      ],
      "id": "R7",
      "premises": [],
      "status": "INFERRED_UNBOUND_75_125_IDENTIFICATION",
      "why_open": "the cited source does not print the (75,125) identification"
    },
    {
      "blocks": [
        "Q-side positive-j relocation"
      ],
      "id": "R6.Q_side_relocation",
      "premises": [
        "actual_pair",
        "source_polynomiality",
        "gap5"
      ],
      "status": "OPEN",
      "why_open": "pair positive-j does not force Q positive-j"
    },
    {
      "blocks": [
        "original polynomial-pair membership",
        "source-image sufficiency",
        "reverse lift",
        "chart or branch coverage",
        "I4=I1=Im1=0",
        "H3 promotion",
        "(75,125) verdict change"
      ],
      "id": "target_pair_to_normalized_laurent_root",
      "premises": [],
      "status": "UNMATERIALIZED_OPEN",
      "why_open": "the target pair has not been materialized as normalized Laurent-root data"
    }
  ],
  "overall_verdict": "VERIFIED_TO_EXPLICIT_OPEN_OBLIGATION",
  "schema": "gp-status-block/v1",
  "superseded_by": [
    "math-stuff:d0257f9",
    "math-stuff:fb18749"
  ],
  "supported": [
    {
      "graph_effect": "NONE",
      "licenses": [
        "five_reduced_rows_replayed_from_conditional_normalized_root_data",
        "native_row_commitments_welded_to_gp_exact_source_rows",
        "strict_original_source_promotion_refused"
      ],
      "stage_id": "conditional_source_seam",
      "verdict": "VERIFIED_CONDITIONAL_ESYSTEM_SEAM"
    },
    {
      "graph_effect": "NONE",
      "licenses": [
        "R1_R4_closed_inside_conditional_normalized_root_seam",
        "R6_branch_A_refuted_every_gauge_premise_bound",
        "R6_pair_positive_j_forced_premise_bound",
        "R6_landed_point_1_2_actual_nonzero_only_in_landed_normalization"
      ],
      "stage_id": "r1_r7_source_frontier",
      "verdict": "VERIFIED_R1_R7_OPEN_FRONTIER"
    },
    {
      "graph_effect": "NONE",
      "licenses": [
        "exact_depth2_6_faces_from_declared_reduced_esystem_rows",
        "selected_face_equations_are_necessary_under_declared_root_supports",
        "all_25_outputs_welded_to_landed_chain_faces"
      ],
      "stage_id": "graded_face_extraction",
      "verdict": "VERIFIED_GRADED_FACE_EXTRACTION"
    },
    {
      "graph_effect": "NONE",
      "licenses": [
        "certificate_integrity_and_order_verified",
        "solve_and_unit_identities_verified",
        "chain_inputs_welded_to_gp_ladder_solutions",
        "boundary_residuals_welded_to_gp_projection"
      ],
      "stage_id": "ordered_depth6_chain",
      "verdict": "VERIFIED_DEPTH6_CHAIN_ENVELOPE"
    },
    {
      "graph_effect": "NONE",
      "licenses": [
        "exact_boundary_polynomials_decoded",
        "boundary_stratum_rewrites_may_be_checked"
      ],
      "stage_id": "boundary_projection_and_strata",
      "verdict": "VERIFIED_BOUNDARY_PROJECTION_EQUIVALENCES_DEFERRED"
    }
  ]
}
```
<!-- GP-STATUS-BLOCK:END -->
