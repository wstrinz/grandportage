# Public integration plan

2026-10-02. Proposal only. Every public push needs Will's explicit approval.

## Current lines

| Line | State |
|---|---|
| Public `wstrinz/grandportage` master | v0.37 frozen at `6f38e96` (freeze docs). Snapshot mirror: published through `public-snapshot-v1.json`, so its SHAs differ from the workspace's v0.37 history. |
| Workspace `master` | v0.37 development history plus 0.50, joined by an unrelated-history merge. 0.50 owns the root docs; the v0.37 README and REVIEW live in `HISTORY/`. Tracks `codex/phase-0`. |
| Workspace `codex/phase-0` | 0.50 source of truth. Merges into workspace master after each checkpoint. |

## Approach

Publish 0.50 as the successor major line on public master. Use one snapshot commit per release, as for v0.37, so public history stays linear on top of `6f38e96`. Never force-push. v0.37 stays reachable through its tags, `release/*` branches and `HISTORY/`.

## Prerequisites

1. **Release gate.** Will picks the public gate. The default proposal is after Phase 3 (minimal algebraic profile), when 0.50 first does mathematics a user can run.
2. **Portable harnesses.** Harnesses hard-code the local Lean 4.32.1 path under `$ELAN_HOME`. Resolve the toolchain from `lean-toolchain` through `elan`/`lake env`, then add a CI job that builds `phase2/lean` and runs the 0.50 suite. Because receipts bind adapter bytes, re-execute and re-integrate every harness after the path change.
3. **Snapshot manifest v2.** Extend the manifest for the merged tree, keeping the v0.37 public/private split:
   - public: 0.50 sources, corpus fixtures, layer tags, reports and Lean;
   - private: private harvests, oracle checkouts, caches and machine-local scratch.
   Run the existing snapshot tooling and audit the output, as `tools/audit-freeze-package.py` did for v0.37.1.
4. **Freeze parity.** Apply the v0.37.1 freeze banner (`reports/freeze-v0.37.1/`) to the `HISTORY/` copies in workspace master, so the archived v0.37 docs match what the public freeze says.
5. **Public README.** Lead with 0.50, keep one paragraph stating that v0.37 is frozen with a link to its tag, and keep the v0.37 README contract tests pointed at `HISTORY/`.

## Release steps (after approval)

1. Tag workspace master (`v0.50.0-alpha`).
2. Generate and audit the v2 snapshot.
3. Commit the snapshot onto public master as a fast-forward, tag `v0.50.0-alpha`, and draft release notes from `STATUS.md` and the closeout.
4. Confirm public CI runs both the v0.37 suite and the 0.50 Lean suite green.

## Open decisions for Will

- Which gate: after Phase 3, or a later one.
- Whether the 459-case corpus and source-pinned reports are public at release. They already are in the public shadow.
- Version label: `0.50.0-alpha`, or a new name.
