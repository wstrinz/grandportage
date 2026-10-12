# Grand Portage v0.50.0

The first stable release of the 0.50 rework, covering everything since `v0.50.0-alpha.2` (2026-10-11).

**The goal of this release:** every sentence GP prints is no stronger than what the Kernel established. [GUARANTEES.md](../GUARANTEES.md) states what is guaranteed, and under which assumptions.

**Release commit.** The tag `v0.50.0` sits on the exact commit on which workspace CI passed. The public snapshot is compiled from that commit, and the public CI runs on the tagged commit itself. The commit, the snapshot hash and both CI runs are recorded in the publication receipt, `reports/STABLE-PUBLICATION.json`. Reproduce from the tag.

## Claim authority

- **The goal verdict is held by the Kernel (A2).**
  - A DECIDE goal is now a 3b profile statement: `goal n m true` and `goal n m false`, with `cover n m L` and the implication `spine n m L`.
  - These are held only through admitted rules (`realize`, `spine`, `decide`) and an exhaustive-cover check (`cover_all`).
  - Each rule is proved sound in the binding: `realizeRuleOk_sound`, `spineRuleOk_sound`, `decideRuleOk_sound`, `coverAllCheck_sound`, `fold_held_goal`.
  - Graph matching is a Lean admission check: exact statement equality against the encoder. The Python goal join has left the TCB.
  - A cover is held only by a completeness proof, never by a named premise. Cover records written before A2 are shown as notices to refile.
- **Campaign statement binding (A1).** Every command reads `campaign.json` once, checks its SHA-256 against the bound statement, and parses those same bytes. An edit is refused until `gp restate --reason ...` records it as a versioned event.
- **Content-hash freshness (A3).** A Lean runner is fresh only if a stamp records the hash of its sources and toolchain pin. Modification times play no part.
- **A merge guard covering both profiles.** `gp_ledger3 --guard` runs the Kernel's `resolve` over the merged 3b log, so a merge refuses 3b collisions with the Kernel's own reason.

## Evidence

- **Comparator warrants for 1,882 of 1,887 supported pilot claims (99.7%)**, now including **57 of 62 EMPTY exclusions** (D1).
  - The EMPTY route: Mathlib-only frame normalization (`GPEmpty.frame4`), then one `linear_combination` of the ledger's ideal certificate per claim.
  - The 5 largest EMPTY certificates are refused by size and stay belay-only.
  - Coverage is reported by kind of conclusion, with the trust boundary each kind crosses.
- **CI axiom audit.** Every theorem `GUARANTEES.md` cites is checked on each run to depend only on `propext`, `Quot.sound` and `Classical.choice`. A control must flag a custom axiom.
- **Rope R1a now proves non-vacuity (D2).** Exact ℚ(√3) embeddings of all six TU gadgets are Lean theorems in the rope, each with its distinguished pair at distance 1.

## Usability outside this repo

- **[docs/USING-GP.md](../docs/USING-GP.md):**
  - install, and the full campaign loop in any directory;
  - a worked example, including reach, a refusal and its fix, receipts, `restate`, a two-branch merge and a DECIDE goal decided both ways;
  - from a held claim to a rope.

  A test replays every command block in the guide.
- **A compatibility statement** for `gp-ledger/v1`. `gp --version` reports the version, and `init` records it. A test runs a campaign outside the repository and folds an old-format ledger.
- **Clean refusals** in place of crashes and silent drops:
  - build progress and build failures;
  - schema check;
  - malformed matroid families, and missing `nonzero`;
  - sign atoms on characteristic scopes;
  - consistent "except {…}" scope text;
  - `explain` shows the stored receipt hash.

## Documentation

- [GUARANTEES.md](../GUARANTEES.md) is new.
- [LIMITS.md](../LIMITS.md) is current; the older text is in `HISTORY/`.
- [TCB.md](../TCB.md) opens with a current one-page summary.
- The public manifests no longer name withheld paths. The snapshot classifier lets the longest prefix win. Remaining withheld files are listed in a private overlay that the manifest declares only by SHA-256, and the snapshot refuses if the overlay is missing or altered.

## Withheld

As in alpha.2: campaign packets and ledgers, campaign-sensitive decisions and ropes in preparation, until the related outreach is done.

## Limits

These are listed in [LIMITS.md](../LIMITS.md):
- ℝ only, not every real closed field;
- number fields of degree ≤ 3;
- 5 pilot EMPTY claims without a Comparator warrant;
- no `≥ 0` sign atom;
- no map rule between Gram and coordinate forms;
- no withdrawal of refused claims.

GP cannot tell that a problem was specified wrongly; fidelity reviews are for that.

**No published result has yet been independently re-established outright.**

## Reproducing

You need elan and Python 3.10 or later.
- **Tests:** `python -m pytest -q -k gp50 tests/`. Suites that need private data skip.
- **Lean packages:** build `phase2/lean`, `profile`, `binding` (after `lake exe cache get`) and `census`.
- **R1a:** `cd ropes/r1a && bash REPRODUCE` on Linux.
