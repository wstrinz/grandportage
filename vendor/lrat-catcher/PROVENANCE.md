# Vendored LRAT-Catcher

Source: https://github.com/leansolving/lrat-catcher at `b2e8d59` (v0.2.0), MIT licence (`LICENSE`).

The GP port to Lean `v4.34.0-rc2` (post-G3a decision 4, one-day timebox; it took under an hour) changes two
files: `lean-toolchain`, and two `rfl` steps in `LRATCatcher/Kernel.lean`
(`lratCheckerK_eq`), where `lratChecker` now unfolds through the `Formula` class.
The library, the Ramsey and Schur showcases, and the reflect, cover, kernel and presolve tests
build. The three streaming tests need a POSIX FIFO and a live solver feed, so they are not run
on Windows.
