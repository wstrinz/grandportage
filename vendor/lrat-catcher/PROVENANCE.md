# Vendored LRAT-Catcher

Source: https://github.com/leansolving/lrat-catcher at `b2e8d59` (v0.2.0), MIT licence (`LICENSE`).

The GP port to Lean `v4.34.0-rc2` (post-G3a decision 4, one-day timebox; it took under an hour) changed two
files: `lean-toolchain`, and two `rfl` steps in `LRATCatcher/Kernel.lean`
(`lratCheckerK_eq`), where `lratChecker` now unfolds through the `Formula` class.

The GP port to Lean `v4.35.0-rc3` (Hex v0.9.0 promotion, 2026-10-13) follows two core changes.
`Std.Sat.CNF.Clause` is now a structure (packed atoms and polarities) instead of a literal list,
and `Std.Tactic.BVDecide.LRAT` was rewritten: its internals (`DefaultFormula`, `PosFin`,
`lratChecker`, `compactLratChecker`, `CNF.convertLRAT`) are gone. The public `check` and
`check_sound` remain.

- **Native mode is ported.** Clause literals are built with `CNF.Clause.ofLiterals`, which keeps
  literal order, and `literals_ofLiterals` is added to the `simp` sets that unfold
  `CNF.Clause.eval`. This touches `parseDimacs` (`Basic.lean`), `Cube.toCNF` and `Cube.negClause`
  (`Cover.lean`), the Ramsey and Schur clause builders, `ReflectTest`'s `tinyDef`, and
  `validateDimacs`'s empty-clause warning (`size == 0`).
- **Kernel mode and streaming import are removed.** Both cloned the deleted checker internals:
  `Kernel.lean`, `Stream.lean`, `StreamOracle.lean`, `StreamFeedIrrel.lean`, the `+kernel`
  commands in `Reflect.lean`, the `lratcatch-stream-gen` executable (`StreamGen.lean`),
  `StreamCnfTest.lean`, and their tests (`KernelTest`, `PresolveTest`, `Stream*Test`). GP uses
  neither: the census calls `checkLratCnf`, `checkCover`, `checkCoverRel` and `dimacsRoundTrip`
  only. Restoring them would need a new kernel-reducible clone of the rewritten checker.

The library, all remaining executables, the Ramsey and Schur showcases, and the reflect, cover,
validate, decide, Ramsey, Schur and LeafBench tests build under rc3. `README.md` is upstream's
and still describes the removed modes.
