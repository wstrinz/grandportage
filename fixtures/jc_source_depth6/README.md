# JC source depth-6 fixtures

- boundary_v1.json is GP's exact portable projection of the native boundary
  receipt: the 3,262-term R2B, 6,124-term beta, and 33 rung digests.
- chain_v1.json.gz is byte-identical to the certificate landed by JC commit
  cb3136c. Its compressed SHA-256 is
  7d0ab133e5e0bd3f9f82d6cdac66302c8e3078321113820b56ca2ef04d4a5871;
  its canonical uncompressed SHA-256 is
  d5ed44977e1f39312fbd2d30a286f686a0cd26d55dba237420a7a3d2bf513f15.
- graded_face_extraction_v1.json freezes the five reduced E-system rows,
  finite root supports, coordinate-series manifest, and 25 expected face
  commitments. Its SHA-256 is
  6c8887034321884b6bb0aa7cd8cf04d90e472a36f4a6ba4035a53e7eda1aa8a1.

Run the chain consumer with:

    python experiments/jc_h3_source_depth6/chain_adapter.py

Add --full-replay to recompute all exact chain substitutions. The chain
certificate itself has no graph effect.

Run the independent graded extraction with:

    python experiments/jc_h3_source_depth6/face_extraction_adapter.py
    python experiments/jc_h3_source_depth6/face_extraction_adapter.py --full-source-replay

The stronger mode rederives the five reduced rows from the defining E-system
formula before extraction. This closes raw E-system-to-face translation
validation but retains graph effect NONE and supplies no reverse point lift.

`support_seam_handback_v1.json` is the handback for the newer
support-and-grading result and the generic-`J` specialization result. It keeps
the coefficient-value seam open, records native unconditional R7' and the
premise-free R6 discharge while keeping R7 scalarity independently open. The
formerly explicit exceptional `J` fibres are closed only by the separate
all-`J` closeout handback below. Replay its read-only projection with:

    python experiments/jc_h3_source_depth6/support_seam_handback_adapter.py
    python experiments/jc_h3_source_depth6/support_seam_handback_adapter.py --check-native-bindings
    python experiments/jc_h3_source_depth6/support_seam_handback_adapter.py --check-native-bindings --emit

The adapter creates no graph event and uses only `EvidenceEnvelope` and
`frontier/v1`. Its focused adversarial tests exercise exact-scope premise
propagation and refuse both generic-to-all-fibres and exceptional-zero-to-source-
witness promotions. `--emit` atomically rewrites only the derived review receipt
`review/jc-h3-support-seam-frontier-v1.json`.

`c710_all_j_closeout_handback_v1.json` binds the 29-check native
`C710_DIVISOR_FACE_IDEAL_UNIT_ALL_J` packet. It supersedes only the finite
exceptional-`J` remainder on the declared guarded `c7_10` divisor with
`c2_1=c2_2=0`; it does not promote source sufficiency, a source witness, the
`sigma_kappa_nonzero` branch, or the coefficient-value seam. Replay and emit
its derived receipt with:

    python experiments/jc_h3_source_depth6/c710_all_j_closeout_handback_adapter.py --check-native-bindings --emit

`source_target_first_value_handback_v1.json` binds the 41-check native
gauge-aware first-value packet.  It supersedes the old all-open source-target
coefficient seam only by splitting it into a closed sigma-top partial map and
an open remaining coefficient-map obligation.  It cannot license pair
existence, reverse lifting, source sufficiency, R5/R7, H3, or a graph event.
Replay and emit its derived receipt with:

    python experiments/jc_h3_source_depth6/source_target_first_value_handback_adapter.py --check-native-bindings --emit

`s2_lowjet_guard_peel_handback_v1.json` binds the 31-check exact invariant-J
Sigma guard peel. It closes only the declared `b=R=Delta=0` S2 low-jet cover:
all 15 residual fibres are illegal `det5=0` roots. It leaves global `b=0`,
S1/S3/S4, source sufficiency, H3, and `(75,125)` open. Replay with:

    python experiments/jc_h3_source_depth6/s2_lowjet_guard_peel_handback_adapter.py --check-native-bindings --emit
