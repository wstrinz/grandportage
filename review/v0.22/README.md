# v0.22 graded extraction and full-template review packet

This release closes the previously explicit reduced-E-system-to-selected-face
composition gap while keeping graph format 4 and kernel epoch 10.

## Standalone graded extraction

graded_face_extraction_v1 independently expands five exact reduced E-system
rows to the 25 landed depth-2..6 faces. The stronger replay reconstructs those
rows from normalized finite root series, fourteen P-side triangular
eliminations, and the defining E-system formula. Native-file digest checks are
optional cross-repository provenance checks, not inputs to mathematical replay.

The standalone evidence has graph_effect: NONE. It proves that the selected
faces are necessary coefficient consequences of the declared finite reduced
E-system template. It grants no reverse lift, original-pair membership, chart
coverage, H3, or (75,125) verdict promotion.

    python experiments/jc_h3_source_depth6/face_extraction_adapter.py
    python experiments/jc_h3_source_depth6/face_extraction_adapter.py --full-source-replay
    python experiments/jc_h3_source_depth6/face_extraction_adapter.py --check-native-bindings

## Graph-bound complete-template assay

full_template_campaign.py materializes the complete finite template as 147
nonzero equations in 78 active variables. Those equations contain the selected
25 verbatim. The declared NECESSARY_CONDITION therefore has a concrete point
inclusion: every point of the complete system satisfies the selected system.

Containment verifier v3 recognizes exact parsed generator inclusion as a unit-
cofactor ideal-containment proof and records VERIFIED without a CAS process.
Version-2 containment verdicts are stale. The generated graph is approximately
39.5 MB because generators are still inline; this is an intentional review and
resource-surface assay, not a reason to raise the 64-variable bounds of
specialized evidence checkers.

    python experiments/jc_h3_source_depth6/full_template_campaign.py
    python experiments/jc_h3_source_depth6/full_template_campaign.py --full-source-replay

## What to attack

- malformed but textually equal generators must not earn authority;
- deleting, altering, or reversing one selected generator must refuse;
- changed coefficient domains, point universes, or ring variables must stale or
  refuse the verdict;
- a v2 containment verdict must not remain current under verifier v3;
- failure of the sufficient ideal-membership test must not be reported as a
  refutation of point containment;
- no selected-face survivor may be lifted backward;
- no source membership, parent coverage, H3, or final verdict may be inferred;
- derived read surfaces must not become a second source of authority.

## Release checks

- Python collection: 1,327 checks;
- last full result: 1,286 passed, 41 skipped;
- targeted v0.22 authority and mutation checks: 27 passed;
- Lean: 22 jobs built;
- graph assay: 147 equations, 78 variables, 25 exact selected generators,
  zero findings, and no CAS process.

SHA256SUMS pins this packet and its principal implementation, proof, fixture,
and test inputs. The generated 39.5 MB graph is reproducible and intentionally
not duplicated in the repository.
