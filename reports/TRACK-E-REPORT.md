# Track E report: Comparator warrants for 3P (gate GE)

Builder, 2026-10-09. Authority: post-G4 handoff §4. The design is in [TRACK-E-EMITTER-DESIGN.md](../docs/TRACK-E-EMITTER-DESIGN.md). The fixed-ropes handoff later reprioritised Track E (DECISIONS 2026-10-09). GE is Will's to ratify.

## Result

| GE condition | Status |
| --- | --- |
| Stock Comparator passes every emitted 3P challenge in CI | **All 33 shards pass** (CI run 37991244443, 6 parallel jobs, about 11 min). Solutions are built only inside Comparator's sandbox. |
| ≥ 95% Lean-warrant coverage, every gap listed | **1,825 of 1,891 (96.5%).** The 62 EMPTY claims are listed as deferred in `comparator-MANIFEST.json`, and the 4 unsupported claims are not held. |
| A non-builder agent audits 20 random challenges with zero fidelity defects | **Zero defects** ([GE-AUDIT.md](GE-AUDIT.md), seed 20261009, commit `c70598b`). |
| No Kernel change; 3P replays unchanged | The emitter only reads the ledger. The Kernel pin is unchanged. |

## What is emitted

The work uses route B: one generic `certOk` lemma in the solution prelude, then kernel `decide` for each claim. Each challenge states its claim in Mathlib vocabulary: `RealizesRank3`, defined in 5 lines and compared by value, never as a `definition_names` hole.

| Class | Claims |
| --- | --- |
| Map rule at characteristic p | 1,241 |
| Map rule outside S | 9 |
| Point at characteristic p | 86 |
| Point outside S, or at characteristic 0 | 467 |
| Bridge | 12 |
| Source | 10 |

**Controls.** Each class was run once with four deliberately broken submissions: a `sorry` solution, a weakened statement, a redefined constant and a bumped certificate. Comparator refused all four, each for the right reason.

**Determinism.** Two emissions from the same inputs are byte-identical. `tests/test_gp50_comparator_emit.py` checks emission, counts and fidelity mutants on every gp50 run. CI (`comparator.yml`) runs only when dispatched by hand.

## The audit

The auditor was a separate session with no part in building the emitter. It:
- drew 20 claims (11 map-p, 5 point-s, 2 point-p, 2 bridge);
- wrote its reading of each Lean statement before looking at the claim;
- checked the brief's seven pitfalls and Lane O's P01–P41;
- also checked all 1,825 claims mechanically against the ledger and the matroid files.

It raised three points for Will's judgement, none of them defects:
1. **NOT_IN_IDEAL(1).** It is stated over every algebraically closed field in scope. That is equivalent to `GP-CLI.md`'s algebraic-closure wording, by completeness of ACF_p, and is the stronger form.
2. **No ENCODING-FRAME dependence.** Challenges state realizability directly, so a Comparator pass does not depend on ENCODING-FRAME.
3. **Valid line data.** `RealizesRank3` means "realizes M" only for valid simple rank-3 line data, which the encoder enforces.

## Known limits

- **EMPTY (62 claims) is deferred.** It needs frame normalization for `RealizesRank3` (about 400 Lean lines) and an ideal-certificate checker (about 300 lines), or else a kernel evaluation of `frame_iff` that risks memory.
- **CI found one portability bug.** Python 3.12 refuses to convert integers longer than 4,300 digits to text, and certificates exceed that. Fixed in `b095fa8`.
- **Memory.** A shard peaks near 7 GB. The CI runner has 15 GB plus swap, so it fits.

## Custody

0 of 3 Track E commits are custody-only: `2ea93ed`, `b095fa8` and `f5d132c`.
