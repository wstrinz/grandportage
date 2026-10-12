# Track E emitter design

Builder, 2026-10-08. Authority: [post-G4 handoff §4](GP-0.50-POST-G4-HANDOFF.md). Builds on the one-claim spike (Pappus over characteristic 3: stock Comparator passed, and refused a `sorry` control, a weaker-statement control and a redefined-definition control).

## What gets emitted

One Comparator challenge and one solution per held 3P claim. The 3P ledger has 1,887 supported claims:

| Class | Claims | The challenge says, in Mathlib vocabulary |
| --- | --- | --- |
| Map rule, characteristic p | 1,241 | every algebraically closed `K` with `CharP K p` realizes M |
| Map rule, outside S | 9 | every algebraically closed `K` with `ringChar K ∉ S` realizes M |
| NONEMPTY point, characteristic p | 86 | every field `K` with `CharP K p` realizes M |
| NONEMPTY point, outside S / characteristic 0 | 466 / 1 | every field `K` with `ringChar K ∉ S` (or characteristic 0) realizes M |
| EMPTY, ideal certificate | 44 + 18 | no field `K` in scope realizes M |
| Bridge rule, proper coefficient | 12 + 10 | NOT_IN_IDEAL(1) variants; templates fixed after inspection |

"M realizes" is the spike's `RealizesRank3 lines v`. Three elements with `a < b < c` have linearly independent vectors exactly when no line contains all three. It is defined in 5 lines and compared by value, never as a `definition_names` hole. The challenge's line data is copied from the campaign's matroid file.

**Fidelity checks in the emitter.** It refuses to emit, rather than guessing, when any of these fails:
- the matroid is simple and of rank 3 (every pair lies in some independent triple);
- the claim's kind and scope are among the classes above;
- the claim's characteristic or excluded set matches its receipt.

## Solutions

- **Map rule** (the spike's shape). Vectors are built from the encoder's frame and the receipt's map, at a root of the source polynomial (`IsAlgClosed.exists_root`). Each triple's determinant is settled by `linear_combination` from the source relation and `p = 0`.
- **NONEMPTY point.** The point's coordinates lie in the prime field, which embeds into every field in scope. The same determinant lemmas apply, with no root.
- **EMPTY.** The ideal certificate gives `1` in the framed system's ideal, so no realization exists. The solution needs frame normalization: every realization can be moved to the framed one, which is the content of `GPBinding.Matroid.frame_iff`. Solutions may import `GPBinding`; challenges import only Mathlib.

## Shards and the generic-lemma route

The spike's per-triple proofs cost about 6 s of elaboration per claim. A 16-claim shard peaks at about 9 GB. That is fine locally but sets the CI design.

**Route A, per-triple proofs.** About 1,887 × 6 s ≈ 3 h of elaboration. Comparator adds about 40 s per shard plus a rebuild in its sandbox, so about 8 runner-hours per full run. Shards must stay at or below 4 claims to fit a standard private-repository runner (about 7 GB; confirm on the first CI run). Depending on the plan, about four full runs use up a month's included minutes.

**Route B, generic lemma (preferred if the prototype holds).** One theorem in the solution prelude: `certOk data = true → challenge statement`. `certOk` is a small computable checker over integer polynomials modulo p: frame, map image, the determinant pattern of each triple, and the source relation. Each claim's proof is then `realizes_of_certOk _ (by decide)`, with the kernel evaluating `certOk`. This needs a size-bounded prototype first, because evaluating large Hex-based checkers in the kernel has exhausted memory on this machine before. The target is under 1 s and under 2 GB per claim, which makes a full CI run about 30–60 runner-minutes.

**Decision rule.** If the prototype meets the target on the 16-claim spike set, use route B for every class it covers and route A for the rest. Otherwise use route A, with CI on a stratified sample of challenges per push and a full local run before GE.

## CI job

- A `comparator` job on `ubuntu-24.04`, using `systemd-run --user` and landrun as the earlier probe confirmed, with the pinned Comparator `2312244ac7` and lean4export `v4.34.0-rc2`.
- Emitted files are generated in the job from the committed ledger snapshot and the emitter. They are not committed. A manifest lists every challenge's hash, so a change to any statement shows up in review.
- Census claims on native LRAT trust are reported as their own class, outside Comparator's scope (`TCB.md`). The permitted axioms are never widened.

## Gate GE mapping

| GE condition | How |
| --- | --- |
| Stock Comparator passes every emitted 3P challenge in CI | the CI job above (route B), or a sample in CI plus a full local run (route A) |
| ≥ 95% Lean-warrant coverage, every gap listed | the classes above cover 1,887 of 1,891 claims; the 4 unsupported claims are not held, and any emitter refusal is listed with its reason |
| A non-builder agent audits 20 random challenges, zero fidelity defects | `docs/briefs/GE-FIDELITY-AUDITOR-BRIEF.md`, with Lane O's pitfall list v2 |
| No Kernel change; 3P replays unchanged | the emitter reads the ledger and writes nothing to it |

## Order of work

1. The route B prototype (bounded), once host memory allows.
2. The emitter for all classes, with fidelity checks and the manifest.
3. A local full run (Comparator in WSL).
4. The CI job.
5. The GE audit.
