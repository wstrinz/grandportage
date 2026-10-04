# Phase 0a - backend execution and transcript custody

Fully read backend.py and test_backend.py, and cas.py lines 836-1285. All 28 selected offline tests pass; eight live tests are unexecuted. Four diagnostic observations include two real bounded Python subprocesses, with no Singular execution.

Artifacts snapshot program text, nonce, decoded stdout/stderr and canonical parsed/certificate JSON. Mutating ordinary compatibility fields does not change the retained text. Validation checks text hashes and optional exact program, but semantic fingerprint syntax alone does not prove request meaning or mathematical truth.

Two actual bounded Python subprocesses emitting different byte strings, OK newline and O ff K newline, both retain OK newline and the same stdout text digest because errors=ignore drops invalid UTF-8. This is lossy transcript custody, not a cryptographic collision or reproduced proof admission.

valid_fingerprint accepts a final newline because regex match with dollar permits it. No stored-object or authority bypass established; use fullmatch for the advertised lexical contract.

ExecutionArtifact frozen dataclass retains arbitrary abort_reason by reference. A direct injected-runner mutable reason changes the artifact digest after construction while validate_execution_artifact accepts it. Native subprocess produces only strings/null, so this is a direct-API envelope defect, not a demonstrated native attack.

Subprocess stdout/stderr are byte-capped before decoding. WSL uses an inner timeout and Windows taskkill is best-effort; thread joins and pipe closing occur after process wait. Descendant-held pipes and whole-tree races remain unverified. Version probing separately uses capture_output without these byte caps.

In-band identity is bound to a fresh nonce and compared with the cached early probe; failed executions retain their identity and cannot be rehabilitated by a later probe. Banner equality is not executable-byte attestation.

Injected/subclass backends cannot normally record positive authority. The section persistence test overrides this gate, so its eight mocked artifacts establish persistence plumbing only. Eight live mathematical/backend integration tests were read but excluded.

Fix proposals: retain raw bytes or reject encoding errors; tighten artifact field types and fingerprint matching; separately bound the version probe and specify containment guarantees. These are custody/availability findings and do not establish false mathematical admission. Frozen code and all 352 corpus cases remain unchanged and valid. Campaign sweep and Lean prerequisites remain open.
