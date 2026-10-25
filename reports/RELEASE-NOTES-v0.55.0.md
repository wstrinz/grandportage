# Grand Portage v0.55.0

Citations, batch claims and safer replay for Lane P. This builds on [v0.54.0](RELEASE-NOTES-v0.54.0.md). The Kernel and toolchain pins are unchanged.

## Added

- **Citations of published results:** `gp submit L --citation REF` records a reference at tier 5, shown with the presentation tag `[CITED]`. Options include `--theorem-number`, `--locator`, `--doi`, `--file` and `--condition`.
  - A citation is recorded only and never holds a claim. GP does not check that the cited result states the claim or has matching hypotheses; that remains a fidelity review.
  - An optional local copy is hashed and re-hashed on every view. A changed or missing file no longer counts until it is re-submitted.
- **`gp claim --batch FILE`:** files many claims with one bind, all or nothing. The file is a JSON list or JSON lines. A refusal names the affected spec and its reason; no claims are filed.
  - The resulting claim records and status match filing the same claims individually, in order.
  - Comparator claims must be filed individually.

On a Mathlib-based campaign, ten theorem claims took 57 s in one batch against 1,023 s as individual claims on a loaded machine. This is a measured example, not a general speed guarantee.

## Fixed

- **Replay memory accumulated across modules.** `gp bind --replay` now runs one `leanchecker` process per module.
- **A timeout left a checker running.** The timeout now kills the whole process tree. Previously, an orphaned checker grew to 49 GB in one trial.
- **A kernel rejection now names its module,** so a failed replay identifies where checking stopped.

## Reproducing

`python -m pytest -q -k gp50 tests/`. Release verification runs locally on the exact release commit, together with the Kernel pin, v0.37 fast suite, check count and public snapshot leak audit. Publication is a separate approval step.
