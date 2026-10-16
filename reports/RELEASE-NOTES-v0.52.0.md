# Grand Portage v0.52.0

New in this release: **Lane P, phase 1.** GP can now hold claims stated as Lean propositions, under named premises. It is built on [v0.51.0](RELEASE-NOTES-v0.51.0.md). The Kernel's 22 files are unchanged, and the existing polynomial profiles are untouched.

## Why

GP 0.50 and 0.51 could state only polynomial systems. In matched trials on two published problems, the decisive claims were out of reach: a rank-9 matroid's exchange graph, and the cones and positivity in a hyperbolicity transport. Meanwhile, a paper ledger of claim, warrant tier, fidelity and named premises caught a real overstatement in a published release. Lane P makes that ledger something GP holds and checks.

## What it does

A campaign whose `campaign.json` says `"profile": "P"` keeps a small Lean package of statements (`def X : Prop`). Then:
- **`gp register X`** binds a statement to its declaration, a hash of its campaign-local definitions, and the toolchain stamp. On every bind, a renamed or redefined statement (or a redefined local dependency) unbinds its claims, with a message naming what changed.
- **`gp claim L --lean X --premise H … --theorem T`** holds the claim "H… ⇒ X" by a Lean theorem.
  - The binder runs no elaboration. It asks the Lean kernel to accept T at exactly that type.
  - T may use only `propext`, `Quot.sound` and `Classical.choice`. `sorry`, `native_decide` and custom axioms are refused.
- **`gp discharge L --premise H --by L2`** removes a premise using a held claim of it (the cut rule).
- **`gp submit L --hand-proof … | --script … | --numerical …`** records evidence that never holds a claim. A hand proof's reviewer conditions become open premises.
- **`gp fidelity`** records a statement's review level.
- **`gp present L --venue V --tag …`** records where a claim is presented. `status` marks a presentation **OVERSTATED** when its tag is above the tier the claim has earned, or when it leaves out an open premise.
- **Views** show tier, fidelity and open premises. `explain` marks the weakest step; `frontier` ranks open premises by the claims they would unlock.
- **Withdrawal** composes: `--cascade` lists the discharges that lose their hold.

**Soundness.** `fold_held_meaningP`: every held claim means "its premises imply its statement", given that the binder's records are sound. It, the cut-rule lemma and the withdrawal lemmas are in the CI axiom audit.

## Known limits of phase 1

- **Tier 2 is "unreplayed".** A module can skip build-time kernel checks. Until the lean4checker replay (phase 2), a theorem warrant is shown as tier 2 (unreplayed).
- **Not yet in phase 1:** Comparator receipts (tier 1) and bridges from 3a/3b claims; both are phase 2.
- **OVERSTATED is noisy.** On the paper-ledger trial it flagged 9 of the 14 presentations an independent audit judged overstated, and also 17 of the 53 it judged fine. The false alarms come from open process conditions (pending reviews, merges) being encoded as premises. Phase 2 separates the two.
- **Statements unbind on any dependency bump.** Pinned dependencies are covered by the toolchain stamp, so moving Mathlib unbinds every claim until you rebind.
- **GP cannot tell a sketch from a proof.** It enforces the state the filer declares, and the reviewer's conditions.

## Reproducing

`python -m pytest -q -k gp50 tests/`. The tag `v0.52.0` sits on the exact commit on which workspace CI passed. Lane P's commands are in [USING-GP.md](../docs/USING-GP.md) and [GP-CLI.md](../docs/GP-CLI.md).
