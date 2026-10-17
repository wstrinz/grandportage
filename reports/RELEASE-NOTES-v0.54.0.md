# Grand Portage v0.54.0

Fixes and speed for Lane P, all from running it on a real campaign. It builds on [v0.53.0](RELEASE-NOTES-v0.53.0.md). The Kernel is unchanged, and every claim's verdict is the same as under v0.53.0.

## Fixed

- **A replay that failed for an infrastructure reason could never be cleared.** Under load, `leanchecker` failed to read a file that existed. `gp` reported a kernel failure and withheld every theorem warrant, and because a failed replay outranked a passing one for the same tree, a clean rerun restored nothing.
  - Now only a kernel rejection withholds warrants, and it still sticks until the package changes.
  - An unreadable or missing file, a crash or a timeout reads "replay could not run: …; retry" and changes nothing.
  - A later passing replay decides.
- **Comparator could not check a package with bridges.** The emitted solution imported every module, including the bridges, which need the binding, and the sandbox cannot build that.
  - The solution now imports only the statements and the module that declares the theorem.
  - Verified end to end: stock Comparator accepted such a challenge without the sandbox building the binding.
  - A claim whose proof really needs the binding is reported as needing it.
- **Recorded evidence could change unnoticed.** A hand proof, script or numerical file is now re-hashed on every view. An edited file shows "CHANGED SINCE RECORDED" and a missing one "MISSING"; neither counts until it is re-submitted.
- **A theorem of the wrong type was a truncated message with exit 0.** It is now a refusal (exit 1) that shows the claim's expected type beside the theorem's actual type.

## Faster

- **Bind results are reused** for what has not changed, and only new statements and theorems are bound.
- **A bridged ledger's verdicts are computed once per command,** and cached by content.
- **`gp register --batch FILE`** registers several statements in one bind, all or none.

On a 24-statement campaign:

| Command | v0.53.0 | v0.54.0 |
|---|---|---|
| `status`, `explain`, `frontier` | 64–86 s | 1–2 s |
| `claim --theorem` | 146 s | 42 s |
| two registrations | 92 s + 265 s | 41 s together |

`GP_NO_CACHE=1` turns both caches off.

## Reproducing

`python -m pytest -q -k gp50 tests/`. This release was verified locally on its tagged commit (see the publication receipt).
