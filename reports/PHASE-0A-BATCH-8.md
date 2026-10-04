# Phase 0a - current algebra and producer boundaries

Added 17 cases, GP-X125-141: six acceptance controls and eleven refusals. The corpus now has 182 cases (49 ACCEPT, 133 REFUSE expected). Final replay has 175 agreements, four known conservative differences, one diagnostic observation, one pending case and one unsupported case. G0 remains unevaluated. All 165 pre-existing case files and expected verdicts are preserved byte-for-byte.

## Extracted distinctions

- X125-128: the same three equations have an exact rational unit certificate and a point (13,0) over F23. The rational certificate divides by 23 and 46, so it is rejected in F23; exact substitution checks the counterexample. This offline control does not claim to execute the original live-CAS regression.
- X129-130 and X138: a ninth-power saturation certificate replays exactly. The explicit eighth-power identity fails. A bounded producer searching powers zero through eight returns UNVERIFIED, which supplies no nonmembership proof. Its offline membership double uses exact monomial divisibility for this particular ideal; it is not a general CAS or a new admitted checker.
- X131-133: a pending ideal cannot license an ambient identity. A known empty generator list means the zero ideal: the zero polynomial passes membership replay and 1 fails. Missing evidence is distinct from a computed zero ideal.
- X134-136: substitution requires an image for every variable and is simultaneous. The asymmetric polynomial x^2+y swaps to y^2+x, not x^2+x.
- X137: an elimination result cannot use a removed coordinate. This rejection occurs before any external solver invocation.
- X139-140: a truncated decomposition component is rejected, whereas an explicitly printed zero component parses. These are synthetic producer-parser controls; even accepted output is not a mathematical proof.
- X141: an empty saturation output passes the legacy one-sided output check vacuously, yet omits y. The exact identity x^2*y=1*(x^2*y)+0*(x*y^2), and point (1,1), distinguish this output from the actual saturation. The raw VERIFIED result is preserved alongside refusal of the stronger completeness conclusion.

## Validation and limits

Thirty focused offline regressions pass; three live operation tests are deselected. Raw pytest evidence is in oracle-current-batch8.xml. Four additional constructor-emission controls check library-free Rabinowitsch elimination and avoid malformed empty-ideal declarations. CONSTRUCTOR-EMISSION-AUDIT.json preserves the emitted programs. Compilation/text inspection does not prove those programs execute; original live Singular regressions remain unrun.

The first corpus draft exposed two adapter errors: treating Polynomial.is_zero as callable (two case errors), and treating the decomposition result list as a dictionary (one case error). Corrected adapters replay all fixed expectations. Immutable draft results remain in oracle-runs. The final adapter also fails explicitly if a proposed counterexample does not satisfy its equations. Runner and both probe modules are hashed in the replay report.

CURRENT-ALGEBRA-REVIEW.json records the selected source dispositions and executed test names. Current-tree coverage is 25 partial files and 343 unreviewed files out of 368; no complete semantic source review is claimed. Historical coverage is unchanged. No campaign sources were harvested, no kernel implementation was started, and no live backend execution is inferred from mocked outputs.

Next: fold/merge/retraction, stale premises, verifier versions and independent warrant survival. The campaign sweep still needs the completed source manifest; A24 remains pending and X53 unsupported.
