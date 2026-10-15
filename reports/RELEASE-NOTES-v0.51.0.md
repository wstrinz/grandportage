# Grand Portage v0.51.0

The first release of the 0.51 line, on [v0.50.2](RELEASE-NOTES-v0.50.2.md). It brings a new toolchain, claim withdrawal, and one fix. The Kernel's 22 files are unchanged, and every soundness theorem still holds.

## Toolchain: Lean v4.35.0-rc3 and Hex v0.9.0

- All four packages (Kernel, profile, binding, census) move to Lean `v4.35.0-rc3` (a release candidate), Hex v0.9.0, and Mathlib `6b7abb3c`, Hex's own pin. `KERNEL-PIN.json` changes only its toolchain.
- **Verified before landing:**
  - every Kernel module replays under `leanchecker`;
  - the axiom audit passes (1,190 constants, standard axioms only);
  - folds are byte-identical to v0.50.2 for every campaign ledger and the corpus replays;
  - the DK difftests show 0 mismatches.
- **Binding:** three mechanical edits, for Mathlib's changed `MvPolynomial.coeff` argument order. No theorem's meaning changed.
- **Census LRAT checker:** ported to the new core checker in its native mode, the only mode GP uses. Its kernel mode and streaming import were removed: they copied core internals that rc3 deleted.
- **New requirement: a C compiler (`cc`).** Hex v0.9 links C code (`HexModArith`, `HexArith`) into the runners, so it joins "Hex arithmetic, as compiled" in [TCB.md](../TCB.md). See [USING-GP.md](../docs/USING-GP.md#install) for Windows.
- Comparator and lean4export are pinned to their `v4.35.0-rc3` tags; all 34 3P Comparator shards pass.

## New: claim withdrawal

`gp withdraw LABEL --reason TEXT [--cascade]` withdraws a claim permanently. It closes the long-standing "no withdrawal" limit.
- **How it works:** the Kernel's existing `retract` event, applied to the claim's warrants. No Kernel change.
  - Everything that rested only on the withdrawn claim stops being held, and `status`, `explain` and `frontier` say why.
  - Held claims still mean their statements: the soundness theorems quantify over every event list.
- **New lemmas,** in the CI axiom audit: withdrawal only un-holds (W1), never breaks a fold (W2), and a withdrawn claim is never held (W3).
- **The command:**
  - it prints what changed, including any change to a goal verdict;
  - it refuses to un-hold other held claims unless you pass `--cascade`;
  - it refuses `goal` and `spine` claims, which `gp` files itself;
  - a withdrawn label cannot be resubmitted; file a corrected claim under a new label.
- **Older readers:** gp 0.50.x does not know the new `withdraw` record and will show a withdrawn claim as before. That view is stale, though still sound. Read a ledger with a `gp` at least as new as the one that wrote it; `withdraw` reminds you each time.

## Fixed: a claim that failed to elaborate made the ledger's claims vanish

The 3a runner reports an elaboration failure (such as an undeclared variable) as `elaboration`, not `error`. v0.50.2 checked only `error`, so such a fold was taken for an empty one and the claims disappeared from the views. Now either kind of failure sets the bad claim aside as `unparsed`, and the rest of the ledger folds.

New filings were already refused at `claim`; this matters only for a ledger that holds such a claim from earlier.

## Tooling

- **A differential test** keeps `gp`'s filing-time syntax check, a mirror of the runner's polynomial grammar, in agreement with the runner. Its first run found the bug above.
- **The public snapshot** now reads blobs in one batch (seconds, not minutes). It has a built-in leak audit against the published tree.

## Reproducing

`python -m pytest -q -k gp50 tests/`. The tag `v0.51.0` sits on the exact commit on which workspace CI passed. The binding needs `lake exe cache get`, at Mathlib `6b7abb3c`.
