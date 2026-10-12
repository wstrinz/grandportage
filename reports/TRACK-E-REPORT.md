# Track E report: Comparator warrants for 3P (gate GE)

Builder, 2026-10-09; post-G4 handoff §4. Design: [TRACK-E-EMITTER-DESIGN.md](../docs/TRACK-E-EMITTER-DESIGN.md). GE is Will's to ratify.

## Result

| GE condition | Status |
| --- | --- |
| Stock Comparator passes every emitted 3P challenge in CI | **All 33 shards pass** (CI run 37991244443, 6 parallel jobs, about 11 min). Solutions are built only inside Comparator's sandbox. |
| ≥ 95% Lean-warrant coverage, every gap listed | **1,825 of 1,891 (96.5%)** at GE. After D1 (2026-10-12) it is 1,882 of 1,887 supported claims. The 5 refused EMPTY claims and the 4 unsupported claims are listed in `comparator-MANIFEST.json`. |
| A non-builder agent audits 20 random challenges with zero fidelity defects | **Zero defects** ([GE-AUDIT.md](GE-AUDIT.md), seed 20261009, commit `c70598b`). |
| No Kernel change; 3P replays unchanged | The emitter only reads the ledger. The Kernel pin is unchanged. |

## Coverage by kind of conclusion

Release plan B4, 2026-10-12; counts from `campaigns/3p-matroids/warrants/comparator-MANIFEST.json` (`classes`). "M" is `RealizesRank3` on the matroid's lines.

| Kind | Comparator statement | Warranted | Trust boundary crossed |
| --- | --- | --- | --- |
| map-p | every algebraically closed `K` with `CharP K p` realizes M | 1,241 | GP to rope: kernel `decide` re-checks the map certificate (`certOk`), and the root comes from `IsAlgClosed.exists_root` |
| map-s | the same, for `ringChar K ∉ S` | 9 | as map-p |
| point-p | every field with `CharP K p` realizes M | 86 | GP to rope: the prime-field point embeds into every field in scope, so the result is not limited to algebraically closed fields |
| point-s | every field with `ringChar K ∉ S`, or `CharZero K`, realizes M | 467 | as point-p, with an integer point |
| bridge | every algebraically closed field in scope realizes M (NOT_IN_IDEAL(1)) | 12 | GP to rope: solved from the premise's point, not from GP's bridge rule |
| source | `f` has a root in every algebraically closed field in scope | 10 | GP to rope (`GPCert.exists_rootZ`) |
| **EMPTY** | no field with `CharP K p`, or with `ringChar K ∉ S`, realizes M | **57 of 62** | GP to rope: `GPEmpty.frame4` moves any realization to the framed one, and `linear_combination` re-checks the ideal certificate. The 5 largest certificates are refused by size and stay belay-only (GP TCB) |

Total: 1,882 of 1,887 supported claims; the 4 unsupported claims are not held. A warranted pass needs no trust in GP: only Lean, Mathlib, Comparator and the fidelity of `RealizesRank3` and the line data (audit point 3).

**The EMPTY route (D1, 2026-10-12).** The challenge is `¬ ∃ v, RealizesRank3 lines v` over every field in scope. The prelude `tools/comparator-prelude-empty.lean` (159 lines, Mathlib only) proves frame normalization: `frame4` maps the encoder's frame to e₀, e₁, e₂, e₀ + e₁ + e₂, and `det_zero_iff` reads each framed equation off the realization. Each claim closes by one `linear_combination` of the ledger's cofactors; no kernel evaluation is involved. Stock Comparator (pinned 2312244) accepts `unrealizable_F7m_empty_2` and refuses the sorry, weakened and redefined controls.

## What is emitted

The work uses route B: one generic `certOk` lemma in the solution prelude, then kernel `decide` for each claim. Each challenge states its claim in Mathlib vocabulary: `RealizesRank3`, defined in 5 lines and compared by value, never as a `definition_names` hole.

**Controls.** For each class, Comparator refused a `sorry` solution, a weakened statement, a redefined constant and a bumped certificate, each for the right reason.

**Determinism.** Emission is byte-identical across runs; `tests/test_gp50_comparator_emit.py` checks emission, counts and fidelity mutants.

## The audit

A separate session, with no part in building the emitter, drew 20 claims (11 map-p, 5 point-s, 2 point-p, 2 bridge), wrote its reading of each Lean statement before looking at the claim, checked the brief's pitfalls and Lane O's P01–P41, and checked all 1,825 claims mechanically against the ledger. It raised three points for Will, none of them defects:
1. **NOT_IN_IDEAL(1)** is stated over every algebraically closed field in scope: by completeness of ACF_p, the stronger form of `GP-CLI.md`'s wording.
2. **No ENCODING-FRAME dependence:** challenges state realizability directly.
3. **Valid line data:** `RealizesRank3` means "realizes M" only for valid simple rank-3 line data, which the encoder enforces.

## Known limits

- **5 EMPTY claims are refused** (keys 1761, 1772, 1813, 1816, 1829). Their certificates are too large for `linear_combination`; size 3,570 already takes about 6.5 minutes.
- **CI found one portability bug:** Python 3.12's 4,300-digit limit on integer text. Fixed in `b095fa8`.
- **Memory.** A shard peaks near 7 GB. The CI job adds 8 GB of swap, which covers both the public and the smaller private runners.

Track E commits: `2ea93ed`, `b095fa8`, `f5d132c`; D1: `eb22adb`.
