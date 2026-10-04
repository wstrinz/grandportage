# v0.50.0-alpha staging

2026-10-03. Prepared per [PUBLIC-INTEGRATION-PLAN.md](PUBLIC-INTEGRATION-PLAN.md). Will's decisions: release gate G3a, corpus and source-pinned reports public, label `v0.50.0-alpha`. **Nothing has been pushed to the public `wstrinz/grandportage`; publication needs Will's explicit approval.** Will, 2026-10-03: hold in the workspace; removing all local machine paths, so that everything is CI-capable, is a prerequisite for moving work to the public repository.

## Prerequisites

| Item | State |
|---|---|
| Release gate | G3a ratified 2026-10-03 |
| Portable harnesses | Done. Tools and tests resolve Lean from `$ELAN_HOME` and use `.exe` only on Windows. The Phase 2 receipts were re-executed (see DECISIONS.md). Workspace CI `gp50` job, run 37156326931, on Linux: 410 passed |
| Snapshot manifest v2 | `public-snapshot-v2.json` on workspace master; the snapshot script and its test default to it. v1 is kept as the v0.37 boundary record |
| Freeze parity | The v0.37.1 freeze banner is applied to `HISTORY/README-v0.37.md`, `SPEC.md` and `review/v0.37/KNOWN-ISSUES.md` |
| Public README | Leads with 0.50; one section points to the frozen `v0.37.0` |
| Release notes | [RELEASE-NOTES-v0.50.0-alpha.md](RELEASE-NOTES-v0.50.0-alpha.md) |

## Snapshot audit (candidate: workspace master)

- **Size.** 1,980 files (1,979 public plus the receipt), 52 MB. Largest: Phase 2 receipts of 0.8–4.3 MB.
- **Private paths.** None present: no oracle checkouts, no historical source snapshot, no v0.37 working docs (`CURRENT.md`, `HANDOFF.md`, …), no `.codex/`.
- **Campaign paths.** None outside the custody allowlist.
- **Tests in the materialized snapshot.** The v0.37 CI selection passes 1,748/1,748. One v0.37 contract test was fixed to read the release markers from `HISTORY/`.
- **Secrets.** None: no tokens, keys or email addresses.
- **Local paths: removed** (Will's prerequisite). `tools/neutralize-local-paths.py` rewrote them to portable forms and re-bound the SHA-256 bindings, with receipts `reports/LOCAL-PATH-MIGRATION.json` and `-V037.json`. The ratchet `tests/test_gp50_local_paths.py` (CI `gp50`) keeps the count at zero. Regenerated receipts must be neutralized before commit.

## Publication steps (after approval)

1. Tag the workspace: `git tag -a v0.50.0-alpha <master commit>` and push the tag to `grand-portage-workspace`.
2. Generate the snapshot at the tag: `python scripts/public_snapshot.py --revision v0.50.0-alpha --output-dir <dir>`, then re-audit as above.
3. In a clone of public `wstrinz/grandportage` at master (`6f38e96`):
   - replace the tree with the snapshot as one commit;
   - verify the committed blobs equal the snapshot bytes (the snapshot's `.gitattributes` is `* -text`; the corpus and receipts are SHA-bound);
   - push as a fast-forward and tag `v0.50.0-alpha`.
   The `v0.37.0` tag is untouched.
4. Draft the GitHub release from the notes, and dispatch public CI. The `gp50` job takes the v0.37 oracle from workspace history when the pinned commit is present, otherwise from the public `v0.37.0` tag, which `oracle/PIN.json` records as byte-equivalent for every path a harness reads (post-G3a decision 2). The workspace may then go private.
