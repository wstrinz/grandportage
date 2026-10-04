# Freeze release handoff — verified private preparation

Base commit: `ac4155787207e2847d248cffed7be871d5dcd577`.
Existing annotated tag: `v0.37.0`, object `ead053ff209dc192bb61c10774e2fba61f449592`, resolves to that base. Its annotation is `Grand Portage v0.37.0`; it does not itself say frozen. No tag was created, moved or rewritten.

DECISIONS.md item 5 limits this task to private preparation. The approved preparation is complete and verified; public application, a freeze announcement and any v0.37.1 publication remain unperformed. Do not describe this audit as a shipped freeze release.

## Requirement evidence

| Packet 0d requirement | Evidence and status |
|---|---|
| Identify v0.37.0 freeze target | Existing release tag matches the immutable oracle. Freeze designation is prepared in the README banner; no force-retag is proposed. |
| Doc-only v0.37.1 patch | Exactly README.md, SPEC.md and review/v0.37/KNOWN-ISSUES.md. No executable or package-version edits. |
| Repair 17 README mojibake dashes | Exactly 17 occurrences in the pinned README; none in the prepared README. |
| Correct stale SPEC status | Graph format 8 and kernel epoch 12 checked against grandportage/format.py; package version checked against __init__.py. Check count explicitly historical; obsolete session count removed from status. |
| Private links | HISTORY link replaced by private-archive annotation; KILL-CRITERIA remains code-form prose explicitly described as private. Prepared entry-document relative links contain no private-manifest target. No claim of a repository-wide link audit. |
| Exact banner | First line matches the packet verbatim, including no successor name or timeline. |
| Containment issue | Records radical versus ideal containment and warns against using point evidence for coordinate-ring identity. Does not claim advice alone reproduces false held authority. |
| Specialization issue | Records sufficient p-integral certificate/witness cases, surviving open guards, and the old rule's conservative refusal. |
| Patch applies | git apply --check and actual application succeeded in an isolated temporary Git directory. All three resulting files match prepared bytes exactly. |
| Public/private classification | Frozen public-snapshot classifier accepts the complete tracked path inventory plus the new known-issues path; all three patch paths classify public. This is classification, not publication or a content-security audit. |
| Sources remain frozen | Oracle tracked files remain clean; original release tag object is unchanged. |

Reproduce from the private workspace with `.venv/Scripts/python.exe -B tools/audit-freeze-package.py`. It writes only its private audit report and temporary F scratch files. Source/patch/tool hashes and individual link checks are in AUDIT.json.

## If publication is later authorized

Use an isolated release checkout at the recorded base, apply the audited patch, inspect the resulting doc-only diff and run the repository's required documentation/public-snapshot checks. Preserve the existing v0.37.0 tag target. Have the release owner choose any additional freeze designation and v0.37.1 release/tag mechanics; this preparation neither invents a tag name nor force-moves one. Do not imply a fresh 1811-check run from the retained historical count.

Later-discovered lifecycle and documentation findings remain in the private Phase 0 review. This deliberately scoped freeze patch records the two issues requested by the packet; it does not silently expand the public release or fix kernel behavior.

2026-09-28 follow-up: architecture review found the required banner made the prepared README 161 lines, exceeding the frozen test limit of 160. Joining one wrapped prose sentence preserves wording and brings it to 160. The audit now checks the limit, the actual frozen README test passes against the prepared file, and isolated patch application again matches all prepared bytes. Patch serialization remains LF. No public or oracle files changed.
