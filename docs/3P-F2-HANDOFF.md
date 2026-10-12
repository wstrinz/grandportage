# 3P F2 handoff (campaign agent)

Written by the builder on 2026-10-05, after G3P was ratified. Authority: `campaigns/3p-matroids/campaign.json` (stage F2) and `docs/GP-0.50-POST-G3A-HANDOFF.md` §4. Where this note and those differ, they win.

## Who and where

- **A fresh campaign-agent session.** It is not the F0/F1 agent and not the builder. A second cold start shows whether `docs/GP-CLI.md` and the F0 agent's `TUTORIAL.md` onboard a new agent. F2 is volume work, and it is better done with a clean context.
- **Checkout:** `$DEV/grand-portage`. It is on `master` and behind `origin/master`. Run:
  ```bash
  git fetch origin
  git switch -c campaign/3p-f2 origin/master
  ```
  Leave the untracked `corpus/` files alone.
- **Committing:** commit only on `campaign/3p-f2`, and push that branch.
  - Never push `master`, and never force-push.
  - The builder replays the ledger and merges after the replay matches. The builder never edits your files.

## Read first

- `campaigns/3p-matroids/campaign.json`
- `docs/GP-CLI.md`
- handoff §4
- `campaigns/3p-matroids/TUTORIAL.md` and `PHASE-3P-REPORT.md`, written by the F0/F1 agent
- `campaigns/3p-matroids/search/` (its helpers; reuse or replace them)

## What changed since F1

- **ENCODING-FRAME is proved** (`GPBinding.Matroid.frame_iff`). `gp` shows the premise as *discharged* when the Lean encoder re-derives a claim's system. `campaign.json` still says OPEN because its text predates the proof; `gp status` is the current state.
- **Surface fixes from the F1 friction log:**
  - one χ verdict per matroid in `status`;
  - the failing item is named on refusal;
  - missing-file and decimal refusals;
  - `frontier` re-diagnoses old refusals.
- **`gp emit-lean --all`** compiles warrants and refuses the shapes it cannot yet warrant. F1 coverage is 34 of 44. Compiling needs the Lean binding built; that is optional for you, because the builder compiles on replay.

## The task: stage F2

1. **Write a generator** for every simple rank-3 matroid on 3 to 8 elements, up to isomorphism. Put it in `search/` or a new `catalog/` directory in the campaign.
   - The generator is labelled **trusted**. **Catalog completeness is an OPEN premise.** Say both wherever the catalog is used.
   - Cross-check from the builder, unverified, so tag it `[VERIFY]`: the published counts for n = 3…8 are 1, 2, 4, 9, 23, 68 (Mayhew–Royle). A mismatch is a finding, not something to tune away.
2. **Write each matroid** to `matroids/<name>.json` with `name`, `elements` and `lines`. Its `source` gives the generator, its digest, the catalog index, and "catalog completeness OPEN".
   - Where a catalog entry is isomorphic to an F1 matroid (for example F7 or F7⁻), record the isomorphism and reuse the F1 claims rather than filing duplicates.
3. **Hold χ(M) for each M,** or tag each open item `closable in principle` or `no complete method` (the statement's `done`). Use only the admitted moves in `campaign.json`. Expect most entries to be realizable in every characteristic, so automate the common route and spend effort on the exceptions.
4. **No COUNT claim over the catalog** before G4. A per-matroid table in the report is fine, provided the catalog premise appears next to it.
5. **9 elements only if F2 was cheap.** Report F2's cost first. Ask Will before starting n = 9.

## Logs and report

- Write `cost-log.jsonl` and `friction-log.jsonl` from day one, and append to the existing files.
  - Classify every refusal as useful, false or ergonomic.
  - Run `python tools/check-campaign-logs.py campaigns/3p-matroids` before each commit.
- Write an F2 section of at most 500 words as `campaigns/3p-matroids/F2-REPORT.md`. Cover:
  - matroids attempted and held;
  - open items with their tags;
  - cost;
  - friction counts;
  - `emit-lean` coverage, if you ran it;
  - the catalog premise.

## Rules

- **Never edit `ledger.jsonl` by hand.** Use `gp` only.
- **Do not edit tools, profiles or docs outside the campaign directory.** Log the friction instead; the builder fixes surfaces.
- **No outside contact and no downloads.** Generate the catalog locally; do not fetch one.
- **Never run `decide +kernel` on Hex checkers.** Memory blows up.
- **Expect slow folds.** `gp status` takes about 6 s at 44 claims, and every call refolds the whole ledger. If that blocks you at F2 scale, log it as friction and tell Will. Do not work around it in the ledger.
- **Stop and ask Will** if you see:
  - a suspected false ACCEPT;
  - a χ that contradicts a known result;
  - a need for a new checker, rule or statement kind;
  - anything that would change `campaign.json`.
