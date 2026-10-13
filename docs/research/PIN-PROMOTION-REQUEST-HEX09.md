# Promotion request: toolchain for Hex v0.9.0 (R2, not executed)

In PROMOTIONS.md style; facts as of `dbad771`.

## 2026-10-13 (requested): Lean `v4.35.0-rc3` for Hex v0.9.0, toolchain only

- **Kernel files:** none. `phase2/lean/lean-toolchain` changes from `v4.34.0-rc2` to `v4.35.0-rc3`. `KERNEL-PIN.json` is rewritten: only its `toolchain` field changes, and all 22 file hashes stay the same.
- **Outside the Kernel:**
  - the `lean-toolchain` files of `profile/`, `binding/`, `census/` and `vendor/lrat-catcher/`;
  - Hex pins: `v0.6.0` → `v0.9.0`, and HexGraphIso `v0.4.0` → `v0.9.0`;
  - Mathlib: `85e3a25e` → `6b7abb3c`, the Hex v0.9.0 manifest's pin;
  - AutoGeneralization: an rc3-compatible rev;
  - `tests/test_gp50_profile_layout.py`, which hard-codes `inputRev "v0.6.0"`;
  - the `LEAN4EXPORT_REV` in `comparator.yml`, moved to tag `v4.35.0-rc3`.
- **Change:** no checker changes; every Hex API GP calls exists at v0.9.0 ([map](HEX-ADOPTION-MAP.md)).
- **Why rc3:** Hex v0.9.0 and its Mathlib pin are on rc3. v4.35.0 (2026-10-12) is newer than every Hex release, so moving to it is a later toolchain-only promotion, once Hex re-pins.
- **Why not split toolchains:** keeping the Kernel on rc2 while profile and binding move is not coherent.
  - The profile, census and binding require the Kernel by path (`../phase2/lean`). Lake compiles a path dependency with the root package's toolchain. So `gp_ledger` and `gp_ledger3` already run Kernel code compiled by `profile/lean-toolchain`.
  - `tools/gp.py` picks `lake` from `profile/lean-toolchain` (`toolchain_lake`). Its runner stamp (`runner_sources`) does not include `phase2/lean/lean-toolchain`.
  - `check-kernel-axioms.py` and `kernel-pin.py` read `phase2/lean/lean-toolchain`. A split would audit an rc2 Kernel while running an rc3 one, and `test_toolchains_agree` refuses that.
  - A census left on rc2 would compile the Kernel into the same `phase2/lean/.lake` under a second toolchain, so all four packages move. R1a (`v4.34.1`, no Kernel dependency) stays.
- **Reason:** packet §4, R2; a prerequisite for any Lane H adoption.
- **Preconditions** (a scratch build on F:, outside the workspace, before execution):
  1. **FFI.** At v0.9.0, `HexMvPoly` requires `HexModArith`.
     - Profile: the `import HexMvPoly` umbrella reaches `HexModArith.Residue`, whose `@[extern]` C code is built with `cc`.
     - Binding: `HexMvPolyMathlib` imports `HexModArithMathlib`.
     - This machine has no `cc` on PATH; A3 records gmp.h missing.
     - The build must show whether the runners link and the binding elaborates. If not, narrow the imports (`Poly`, `PolyFast`, `Layout`, `Admission/Bridge`) or supply `cc`: a profile or binding change, not a Kernel one.
  2. **LRAT-Catcher:** re-port to rc3 (last time, two `rfl` steps); update its PROVENANCE.md.
  3. **Stop condition.** If any Kernel `.lean` file fails to build unchanged under rc3, this request lapses. A source change needs its own promotion.
- **Authority:** needs Will's approval; the pin is rewritten in the same commit (post-G2 §8).
- **Re-check** (on execution):
  - `lake build` of the Kernel package passes with unchanged sources (135 jobs at the last promotion).
  - `tools/check-kernel-axioms.py`: `leanchecker` replays all 22 modules with exit 0. Every Kernel constant has only standard axioms (1,190 constants at the last promotion).
  - `tools/kernel-pin.py verify` passes after `write`; only the toolchain changed. All nine Kernel test executables pass.
  - Profile, binding and census rebuild; `test_gp50_axiom_audit.py` passes.
  - Fold outputs byte-identical to the rc2 runners: 3P (1,891 claims), the 620-claim fold, the 3b ledger and the corpus 3a/3b replays. DK difftest19/23: 0 mismatches.
  - The gp50 suite passes, re-executing the edited layout test.
  - **Binder.** `gp-binder/v2` records carry the toolchain and Mathlib pin, so every record is refused until re-exported.
    - Re-export the records.
    - Regenerate the theorem warrants under the memory guard (last run: 34 in 402 s, 4.2 GB); `decide +kernel` cost may shift.
    - Rerun the Comparator shards with lean4export `v4.35.0-rc3`.
- **TCB:** TCB.md, GUARANTEES.md and LIMITS.md name `v4.35.0-rc3` (still an RC) and the new pins. Linked `HexModArith` code joins "Hex arithmetic, as compiled", and A3 is restated.
