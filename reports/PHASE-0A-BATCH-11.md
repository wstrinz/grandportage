# Phase 0a — provenance, warning review and SPEC

Six cases GP-X187–192 add two acceptance controls and four refusals. Total: 233 cases, 67 ACCEPT and 166 REFUSE expected. Full replay: 226 agreements, four known conservative differences, one diagnostic observation, one pending case and one unsupported case. All 227 prior case files are byte-identical.

X187 preserves second-generation construction taint despite a licensed last transport. X188 removes only the first context's dependency on the refused lift: the final context has no construction taint, although the separate refused inference remains reported. This is a diagnostic positive control, not proof of a point or a rule for alternative warrants.

X189 carries an unchanged meaning-bound warning. X190 retypes its relation while retaining the finding id, and reopens the acceptance with its original reason visible. X191 removes the meaning digest and also becomes stale. X192 omits the review record and blocks as a new warning. These are operational permissions, not mathematical acceptance. The adapter uses isolated temporary files under F, calls the actual frozen hook, and retains the raw messages.

Both source regressions pass (oracle-provenance-review.xml). The complete corpus replay is stored immutably under oracle-runs/20260928T122501685787Z.json. The new adapter hash is included in every replay. No CAS process ran.

## Documentation findings and proposed corrections

All 619 SPEC lines have section dispositions in DOCUMENT-REVIEW.json. Full text reading is not exhaustive semantic extraction.

- SPECIALIZATION's claim that no existence statement transports and that this is a theorem is too broad. The Fano/non-Fano examples refute unconditional rules. A08b/c retain integral certificate/witness instances that the old rule conservatively refuses. Proposed wording: no unconditional existence transport; case-specific integral evidence requires a separate checked rule. Do not silently widen the oracle table.
- The status paragraph uses version-0.30/epoch-11 framing while the scope section explains epoch-12 reach. The table's printed-versus-prose drift confession demonstrates why historical claims and current rules need explicit labels. Historical check/session counts were read, not independently re-established.
- Standalone equality receipts, graph-bound authority and geometric consequences are explicitly different. Laurent export, factor-power, product splits, coefficient expansion, exact contraction and point lifts must keep their stated limits in 0.50.
- hook.py lines 184–187 retain an outdated comment saying fingerprintless acceptances are grandfathered. The current evaluate branch rejects them as stale, reproduced by X191. Proposed fix: correct the comment to describe re-acceptance migration; do not weaken the executable check.
- Known live-front obligations were not discovered by GP. Gauge witnesses are not independent incidents. Coverage catches absent structure, not components that are present but too weak. Preserve these limits in the campaign sweep and cost assessment.

No legacy source was edited. Proposed documentation corrections remain review findings. 37 partial / 331 unreviewed sources are partial/unreviewed, with zero claimed fully semantically reviewed. Phase 0a and the broader goal remain open; the complete campaign manifest still gates 0b and the new Lean spike remains deferred.
