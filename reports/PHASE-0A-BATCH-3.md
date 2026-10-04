# Phase 0a — coefficient recovery and deleted-test review

Verified here: 75 cases, comprising 25 acceptance controls and 50 refusals. Replay returned 69 agreements, four unchanged known conservative differences, one diagnostic observation and one pending case (A24). No expected verdict changed. A22 gained recovered source equations and explicit proof data; its original selected values, forced lift and cap are unchanged.

## A22 recovered without repeating elimination search

The four source equations were recovered literally from the pinned test_real_jc_dm4_materializer_discovers_17_retained_relations fixture. Exact substitution checks all four at dm2=1, d2=y, dm4=-y/2, with all other retained template variables zero.

This supplies a direct argument for the scalar-target premise: any polynomial in the contraction of the source ideal also vanishes under that projected substitution. It does not require recovering the historical list of 17 generators. This is a mathematical implication from the replayed source solution, not a claim that the old elimination search was rerun.

For a constant candidate dm4=c, the coefficient checker reconstructs the complete source residuals: only G2 remains, with constant coefficient 3*c and y coefficient 3/2. Exact cofactor replay verifies 1 = 0*(3*c) + (2/3)*(3/2). Hence the cap-zero coefficient fiber is empty. The unrestricted lift and capped refusal are both independently checked; no verdict is inferred from the case's expected label.

GP-X25 checks the cap-zero positive point dm2=1, d2=2, dm4=-1. GP-X26 checks the cap-one nonunit example dm2=y, d2=1, dm4=-y/2. Every equation and declared degree cap is checked. These are source-template solutions, not full JC realizations.

## Coefficient controls

GP-X27–34 distinguish complete expansion from selected rows. A selected expansion earns only the necessary direction; p=q=y supplies the converse counterexample because the selected constant/linear rows vanish while the quadratic row equals one. Further controls reject omitted overflow, invented rows, too few coordinates, reversed packing and parameter leakage into scalar coefficients.

The 75 focused frozen coefficient, Groebner and reference-arithmetic regressions passed (oracle-batch3-tests.xml). Three additional adapter probes rejected a wrong source witness, a lowered cap and a fabricated obstruction coefficient (batch3-adapter-controls.json). This is not a complete release-suite run or a live CAS run.

## Deleted tests and remaining coverage

Read the complete last-retained text of three deleted files: original-pair seam, formalization transport and p-axis authority. Their blobs match the previously inspected v0.27 version byte for byte. The deletion commit, parent revision, blob IDs, SHA-256 hashes and per-test dispositions are recorded in corpus/history/DELETED-TEST-REVIEW.json.

The original-pair seam retains an explicit missing source map and refuses upgrading conditional evidence to original-source authority. The formalization ledger distinguishes forgetting provenance from recovering it, finite data from formal lifts, and a slice from the whole source; its rank-credit example is explicitly inexpressible in the old vocabulary. The p-axis tests bind local emptiness to equations, guards, point universe and native-source digests, and refuse parent authority.

Those historical tests were read, not executed. Existing corpus analogues cover portions of their binding and localization behavior, but neither fixture equivalence nor complete extraction is claimed. Their remaining test-level obligations stay queued, alongside 26 unread deleted test paths. No companion-campaign sources were accessed.

The earlier four conservatisms and diagnostic-only A03a observation are unchanged. A24 still needs the actual collapsed-placement source model. Current-tree and historical coverage remain incomplete; G0 has not been evaluated. Campaign harvesting still awaits the completed manifest, and no kernel implementation has begun.
