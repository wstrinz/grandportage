# Grand Portage v0.53.0

**Lane P, phase 2.** It completes the warrant ladder that [v0.52.0](RELEASE-NOTES-v0.52.0.md) began, and makes OVERSTATED far quieter. The Kernel's 22 files are unchanged.

## The warrant ladder, complete

- **Tier 1, Comparator receipts.** `gp claim … --comparator T` emits a stock-Comparator challenge from the registered statement. The binder checks that the challenge states exactly the claim's type, so the emitter is not trusted. `gp submit … --comparator` binds:
  - the challenge's SHA-256;
  - the theorem;
  - the Comparator and lean4export revisions;
  - a log showing "Your solution is okay".

  The pins are re-checked on every view, so a receipt from other pins counts only as a record.
- **Tier 2, final after a replay.** `gp bind --replay` replays the campaign package with `leanchecker`. A module that skips the kernel's build-time checks is caught. After a passing replay, theorem warrants show as tier 2, no longer "unreplayed".
- **Tier 3, bridges from polynomial claims.** `gp register --bridge DIR:LABEL` names a held 3a/3b claim's meaning as a Lean statement. The P runner re-folds that claim and holds the bridge only while it is held, so withdrawing it un-holds everything resting on it. New theorems, in the CI axiom audit: `fold_held_meaningP_bridged` and `fold_held_meaningP_bridge3`. The bridge is conservative: a polynomial claim held only by a theorem warrant does not bridge.

## OVERSTATED, quieter

Process conditions (a pending review, a merge, a wording fix) are now separate from mathematical premises. A presentation that leaves out an open condition reads "conditions open". OVERSTATED is kept for a tag above the earned tier, or for a dropped mathematical premise.

On the paper-ledger trial, measured against its independent audit:

| Audit verdict | v0.52.0 flagged | v0.53.0 flagged |
|---|---|---|
| overstated (14) | 9 | 8, plus 1 "conditions open" |
| matching (53) | 17 | 6, plus 11 "conditions open" |

The one overstated presentation no longer flagged is overstated in a way GP does not model, a novelty claim. The finding that mattered is still flagged OVERSTATED.

## Ledgers that require a newer reader

New ledgers record `min_reader` in their init record, and from this version on `gp` refuses a ledger that needs a newer reader. Readers older than 0.53 cannot check this. As before, read a ledger with a `gp` at least as new as the one that wrote it.

## Reproducing

`python -m pytest -q -k gp50 tests/`. With CI minutes paused, this release was verified locally on its tagged commit (see the publication receipt). Comparator runs locally under WSL through `tools/lanep-comparator.sh` and `tools/rope-ext4.sh`, on WSL's own filesystem.
