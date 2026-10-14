# Grand Portage v0.50.2

A fix release on [v0.50.1](RELEASE-NOTES-v0.50.1.md). It makes no change to the Kernel, the toolchain or any soundness theorem. Every fix below came from using GP on real problems: internal trials, and a campaign using GP in the field.

## Fixed: one unparsable claim stopped the whole ledger

In v0.50.1, a claim's polynomial text was parsed only when the ledger folded. One bad text, such as `--target @file` (`--target` had no file input), was accepted at filing, and from then on every command failed to fold:
- `status` and `frontier` crashed;
- sound receipts for other claims were refused with a misleading message.

Since claims cannot be withdrawn, the only way out was a new campaign.

**Now:**
- `claim` checks the syntax of every polynomial text (equations, `nonzero`, `signs`, cover branches, target) and refuses one that does not parse, naming where it is.
- `--target @FILE` reads a long target from a file.
- A ledger already holding such a claim marks it `unparsed` in `status`. That claim is not held, and the rest of the ledger folds as usual.
- A fold that still fails is a refusal, not a traceback.

## Refused: claims over a zero guard

A guard whose canonical form over ℚ is the zero polynomial (`0`, or `(x+1)^2 - x^2 - 2*x - 1`) holds nowhere. An EMPTY claim over it is true only vacuously, yet it reads like a refutation. `claim` and `submit` now refuse such claims and name the guard; a nonzero constant guard is allowed.

[LIMITS.md](../LIMITS.md) states what is not detected (a guard that is zero only on the system, or only modulo a prime), and a convention: pair every guarded EMPTY that others rely on with a non-vacuity claim.

## Documentation

[USING-GP.md](../docs/USING-GP.md) now says:
- what GP cannot state (determinants, positivity, cones, reachability, matroids other than rank 3);
- that named premises form a fixed list;
- how to state a polynomial identity;
- what to do when GP holds only fragments of a result.

## Reproducing

As for v0.50.0: `python -m pytest -q -k gp50 tests/`. The tag `v0.50.2` sits on the exact commit on which workspace CI passed.
