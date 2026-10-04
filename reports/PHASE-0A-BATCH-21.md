# Phase 0a — authority binder and registry

The binder, descriptive registry and both dedicated test files were fully text-read and dispositioned in corpus/AUTHORITY-REVIEW.json. Selected store entry/projection and Groebner-envelope code was read; the full subject-replay method remains partial. All 31 dedicated test instances passed.

The authority module delegates freshness to provenance, proof replay to store and target selection to the caller. Its seals prevent ordinary construction with an unrelated token; they are not cryptographic signatures or isolation from arbitrary Python code. Four diagnostic controls show that one checked receipt can be projected directly to a different dictionary, nested extra payloads can change after bind, duplicate projected fields refuse, and stale refused evidence cannot bind. These use explicitly patched freshness and synthetic payloads, exactly to measure the internal API assumptions. They establish no persisted malformed-evidence acceptance and create no graph records.

The store selects target[of] before invoking project and places bind after subject replay. Proposed successor consideration: validate target/context at projection and use immutable proof payloads, so these obligations are visible at the boundary. This is a design candidate, not an adopted core change or a demonstrated end-to-end vulnerability.

Test scope matters: the ten-subject matrices patch provenance rather than verify it; the malformed-derived-proof control demonstrates one replay refusal before binding, not all subjects. Registry drift tests establish descriptive coverage and consistency; generated table equality and Lean name-string presence do not independently prove transport semantics. Historical Boolean scope metadata is explicitly separate from current effective reach.

Evidence: AUTHORITY-BINDER-BOUNDARY.json, oracle-authority-review.xml and tools/audit-authority-binder.py. Full corpus validation ran as the diagnostic prerequisite. No expected verdicts, case inputs, routes or frozen oracle source changed. No full replay was needed for this non-corpus diagnostic addition.

Next: remaining subject-specific store replay branches, with positive and adversarial controls using actual provenance. Phase 0 is active; the manifest still gates the campaign sweep. Source coverage: 57 partial / 311 unreviewed.
