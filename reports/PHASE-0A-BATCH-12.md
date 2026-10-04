# Phase 0a — coverage inventory, refinement and project criteria

Eight cases GP-X193–200 add three acceptance controls and five refusals. Total: 241 cases, 70 ACCEPT and 171 REFUSE expected. Full replay: 234 agreements, four known conservative differences, one diagnostic observation, one pending case and one unsupported case. All 233 previous cases remain byte-identical.

X193 detects missing place and order components. X194/195 repair each axis independently; the other remains open. X196 represents all recorded uses and has no inventory gap. X197 records no uses and has no detected gap; this is not permission to omit real uses. X198 shows that conclusion reads alone require a component. X199/200 isolate the legacy refinement-tag convention: adding equations is annotated with NECESSARY_CONDITION, while EQUIVALENCE triggers a diagnostic. This does not prove the added equations independent; a redundant equation can preserve the same solution set.

Eight source regressions pass (oracle-inventory.xml). Three independent deletion controls in COVERAGE-BOUNDARY-AUDIT.json remove each asserted axis and then both. The remaining-axis findings persist, but omitted axes are not checked. This is documented opt-in behavior. Declared components may also be too weak, which this inventory cannot detect. Proposed 0.50 treatment: distinguish an asserted and checked inventory from unknown modelling coverage, and never infer model adequacy from silence. This is a proposal, not an adopted schema.

The immutable complete replay is oracle-runs/20260928T123029629655Z.json. The inventory adapter and all cases are hash-bound. No external CAS or campaign source was accessed.

## Historical measurement review

KILL-CRITERIA.md and EXPERIMENT-B.md are fully text-read, with section-by-section dispositions. Their underlying campaign census was not rerun.

The constructor study lists 44 clearly correct labels, 7 clear mislabels, and 6 judgement calls across 57 edges. The reported 88% corresponds to 50/57 not classified as clear errors, not 50 established correct labels. Among clear calls alone the fraction is 44/51 (about 86%). Preserve all three categories and denominators; do not silently classify uncertain cases as correct. The study also replaced its planned paired experiment with retrospective comparison against authored why text. This does not independently verify operation semantics or measure constructors' causal benefit.

A supersession correction invalidated an earlier same-id-only measurement of zero refinements. Remaining prose still repeats a never-refined narrative. Proposed correction: explicitly mark the superseded measurement and retain the replacement-chain method. Unknown relation, unsupported connection and proof that no relation exists must stay distinct; the prose sometimes runs them together.

A6 explicitly acknowledges substantial validators and asks for stronger complexity/cost evidence. Adoption, cold resumption and excellent-Markdown comparisons remain historical unverified claims or plans in these sources. No criterion is declared passed or failed for 0.50 from this reading.

MODELLING_GAPS.md is referenced by the source tests but absent from the frozen GP root; no substitute campaign path was assumed. The quoted limits and GP-owned regression inputs are available here. Trace the original report through the authorized campaign manifest when available.

Current source coverage: 41 partial / 327 unreviewed, zero claimed fully semantically reviewed. Phase 0 remains active; the source manifest still gates the campaign sweep, and the new Lean spike remains deferred.
