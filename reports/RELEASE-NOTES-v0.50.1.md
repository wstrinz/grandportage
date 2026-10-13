# Grand Portage v0.50.1

A fix release on [v0.50.0](RELEASE-NOTES-v0.50.0.md). It makes no change to the Kernel, the toolchain or any soundness theorem.

## Fixed: a matroid record could be filed as a different matroid

In v0.50.0, `--matroid` read only a record's `name`, `elements` and `lines`, and ignored every other key. A record that described a matroid any other way was silently encoded from what was left. For example, a rank-9 matroid given as a matrix over F₂, with no lines, became the rank-3 uniform matroid U(3,18). GP then printed "ENCODING-FRAME: discharged", so a claim could be held under the record's name about a different matroid.

The theorems were sound about the system GP built. The sentence GP printed was not. This is the class of overclaim v0.50.0 exists to prevent. It was found in an internal trial by a person reading `gp explain`, not by a refusal.

**Now:**
- A matroid record may use only the keys the encoder reads (`name`, `elements`, `lines`, `source`, `answer_key`), and must give `lines` explicitly. `"lines": []` is U(3, n).
- Any other key is refused, with the fix: state other matroids, of any rank or given by a matrix, as `--system` claims.
- The rank-3 validity checks run at filing, so their errors are refusals.
- The record format is now documented in [USING-GP.md](../docs/USING-GP.md).

**If you used v0.50.0:** a claim whose matroid record carries other keys is now shown as `unread` in `gp status`. Its ENCODING-FRAME premise stays OPEN, so it is never presented as a claim about that matroid; the rest of the ledger is unaffected. Remove the extra keys if the lines alone describe your matroid. Otherwise re-file the claim as a `--system` claim.

## Clearer refusals

- A refused real point names the system file's entry that fails, and the sign it needs: "`signs[0]` is positive at the point; it must be negative". Only the untrusted search's error text changed; the replay and its soundness proofs did not.
- `--matroid` given a path says to pass the family name.

## Documentation

- Research notes on adopting Hex v0.9 and the toolchain it needs, in [docs/research/](../docs/research/). These are notes only; nothing is adopted in this release.

## Reproducing

As for v0.50.0: `python -m pytest -q -k gp50 tests/`. The tag `v0.50.1` sits on the exact commit on which workspace CI passed.
