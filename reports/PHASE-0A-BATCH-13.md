# Phase 0a — backend identity and completion envelopes

Ten cases GP-X201–210 add two acceptance controls and eight refusals. Total: 251 cases (72 ACCEPT, 179 REFUSE). Full replay: 244 agreements, four known conservative differences, one diagnostic observation, one pending case and one unsupported case. All 241 previous case files remain byte-identical.

X201 accepts a matching per-invocation identity block under explicit native-path test doubles. X202–205 reject mismatched versions, absent identity, duplicate identity and foreign invocation tokens. Each rejected execution remains retained, cannot record a native verdict and cannot acquire consistent aggregate identity. This reproduces control flow, not a real backend identity. A version banner is not an executable-content digest.

X206 accepts a complete fabricated output envelope. X207–210 reject missing, foreign, duplicate and nonterminal completion markers. Failed parses retain no parsed output. The adapter admits only the stated bounded Q[x] basis request and known offline mutations; three unsupported-input mutation controls ensure unsupported requests are not silently ignored.

Seventeen selected source regressions pass, covering identity, version-probe failure, immutable snapshots, nonce reuse refusal and foreign-artifact injection. All thirteen artifact regressions also pass. Raw XML reports are oracle-execution-envelope.xml and oracle-artifacts.xml; three adapter controls are EXECUTION-ADAPTER-CONTROLS.json. The final hash-bound replay is oracle-runs/20260928T124035734115Z.json; an earlier successful replay is also retained before the adapter's explicit input guards were added. No expected verdict changed.

## Custody versus replay authority

The artifact suite explicitly distinguishes missing raw-file audit debt from graph semantics: removing a retained object makes artifacts check fail without rewriting the folded verdict. Exact identity receipts with cofactor derivations remain current when the local backend is unavailable or reports a different version. Historical unavailable backend metadata remains readable without earning current authority. These are separate source-tested boundaries, not a claim that every artifact or receipt path is safe.

The rework should make evidence availability, proof replay, attempt provenance and current claim authority separately inspectable. This is a design recommendation, not an adopted 0.50 rule. Artifact persistence corruption, swapped evidence, filesystem publication failure and protocol/path failures still need neutral extractions despite their passing regressions.

All of test_inband_identity.py and test_artifacts.py have been read; test_backend.py and cas.py are partial. BACKEND-REVIEW.json retains source hashes and function dispositions. The live in-band test is unexecuted. No process was spawned to run Singular, no graph verdict was minted, and no companion source was accessed.

Source coverage: 44 partial / 324 unreviewed, zero claimed fully semantically reviewed. Phase 0 remains active; verified private freeze preparation is unchanged. Campaign manifest and later spike prerequisites remain outstanding.
