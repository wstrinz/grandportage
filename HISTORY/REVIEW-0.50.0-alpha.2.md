# Review guide: v0.50.0-alpha.2

2026-10-11. This alpha covers everything since `v0.50.0-alpha` (2026-10-04, at gate G3a). Current progress: [STATUS.md](STATUS.md); rulings: [DECISIONS.md](DECISIONS.md). Review does not imply production soundness.

**Withheld from this release.** Active campaign material is withheld until the related outreach to other researchers is done. That covers:
- the campaign packets and ledgers;
- the campaign-sensitive decision entries (pointers remain in `DECISIONS.md`);
- one rope in preparation;
- the builder's working handoff.

Some links in retained documents point to withheld files.

## What GP is
- **A Kernel.** A small, Mathlib-free Kernel folds an append-only ledger of claims, warrants and lifecycle events. It holds exactly the claims whose evidence is admitted, and refuses the rest with a reason.
- **Profiles.** Profiles decide what evidence means, through checkers over exact algebra, each proved sound against Mathlib. The main theorems are `fold_held_meaning` (3a) and `fold_held_meaning3` (3b).
- **Axioms.** Everything uses only `propext`, `Quot.sound` and `Classical.choice`.
- **GP is the belay, not the deliverable.** What we hand to others is a **rope**: a Lean theorem that stock Comparator checks, needing no trust in GP. See [ROPE-CHECKLIST.md](docs/ROPE-CHECKLIST.md).

## New since the first alpha

| Area | What to look at |
|---|---|
| A real pilot campaign (G3P) | `campaigns/3p-matroids/`: χ held for 493 matroids. [F2 report](campaigns/3p-matroids/F2-REPORT.md) |
| Census profile (G4) | `census/`: EXISTS/NONE/EXHAUSTIVE/COUNT; extension covers with a Lean-side generator ([meaning note](docs/CENSUS-EXTENSION-COVERS.md)) |
| Fold performance (GK) | [Track K report](reports/TRACK-K-REPORT.md). Every speedup is proved equal to the code it replaces. A later round on 3b receipts (`profile/GPProfile/PolyFast.lean`, `Real/Memo3.lean`, `Real/OrderedPar.lean`, `Real/CaseTreePar.lean`) cut a 58-minute status to 30–60 s. |
| Semireal, ℚ and ℝ contexts (G3b) | [Phase 3b report](reports/PHASE-3B-REPORT.md): SOS and ordered certificates (with guard selection), real points, root covers, number fields, `case_tree` refutations (collision and forced-unit-distance steps) |
| Comparator warrants (GE) | [Track E report](reports/TRACK-E-REPORT.md): 1,825 of 1,891 3P claims pass stock Comparator in CI. The non-builder [fidelity audit](reports/GE-AUDIT.md) found zero defects. |
| CLI (`tools/gp.py`) | See [GP-CLI.md](docs/GP-CLI.md) for each: 3b claims; the merge guard; graph-bound unit-distance claims (`udg_frame_iff`); DECIDE goals with admitted bridges (`realize_sound`, `spine_sound`); receipt references verified on every fold; `frontier` showing goal obligations |
| Unit-distance theorems | `binding/GPBinding/UDG/`: the rhombus lemma, TU gadget lemmas, Schade averaging, the UDG encoding frame, `spine_sound`, with Comparator challenges |
| **Rope R1a** | [`ropes/r1a/`](ropes/r1a/README.md), a T1 candidate meeting GR1:<br>• stock Comparator in CI on a fresh runner;<br>• a fresh-agent reproduction in 13.2 min;<br>• a non-builder fidelity review. |

## Questions for review

- **Belay vs rope.** Is the split right? Does anything a rope says depend on GP after all?
- **Goal bridges.** A DECIDE goal is decided only through an admitted bridge: a graph-bound frame for the yes side, a `gp cover` spine for the no side. The Python join between them is named in `TCB.md`. Is that join small and obviously right?
- **Receipt references.** Supports may point to `receipts/<sha256>.json`, re-hashed on every fold. Any way to make a fold use bytes other than the ones checked?
- **R1a fidelity.** Do the statements in `ropes/r1a/R1aChallenge/` say exactly what [FIDELITY.md](ropes/r1a/FIDELITY.md) claims? In particular, check the formal-conjectures definitions, which are copied verbatim with attribution in [NOTICE](NOTICE).
- **Scope order in 3b.** Can a ℂ or characteristic-0 fact reach an ℝ claim by any route other than the stated kind-1 rules?

## Known limits

- **ℝ, not every real closed field.** Selected-root signs mean "some root in the interval".
- **Number-field irreducibility** uses the rational-root test (degree ≤ 3).
- **62 3P EMPTY claims** have no Comparator warrant yet.
- **The goal bridges' Python join** is trusted code (`TCB.md`).
- **There is no `≥ 0` sign atom** (use slack squares) and no map rule between Gram and coordinate forms.

## Reproduction

- **Pinned to the release commit.** The stable `v0.50.0` will be tagged on the exact commit on which CI passes (`[TAG-COMMIT]`). Its release notes name that commit ([draft](reports/RELEASE-NOTES-v0.50.0.md)), and you reproduce from the tag itself, not the tag plus a later fix.
- **Tests:** `python -m pytest -q -k gp50 tests/` runs the 0.50 suite.
- **Lean packages:**
  - `phase2/lean` (the Kernel);
  - `profile` (no Mathlib);
  - `binding` (pinned Mathlib, including `UDGRope`);
  - `census`.
- **R1a:** `cd ropes/r1a && bash REPRODUCE` (Linux; about 16 min plus the Mathlib cache download).
- **Excluded, as before:** private campaign harvests and the oracle checkout. Their suites skip.
