# Grand Portage 0.50

Grand Portage holds a mathematical claim only through current, bound evidence and sound admitted rules, and only throughout the scope that evidence earns. When a certificate divides by 2, GP does not let the claim it supports reach characteristic 2.

0.50 is a rework of the [v0.37 line](#v037). A small Lean kernel decides which claims are held. Profiles supply the statement language and the checkers, and their soundness is proved in Lean against Mathlib.

**Status: `v0.50.0`, the first stable 0.50 release.** It is research software, so read [GUARANTEES.md](GUARANTEES.md) for exactly what it guarantees and [LIMITS.md](LIMITS.md) for what it does not. See [STATUS.md](STATUS.md) and the [release notes](reports/RELEASE-NOTES-v0.50.0.md).

**What GP guarantees, under which assumptions, and what it does not claim: [GUARANTEES.md](GUARANTEES.md).**

GP is our **belay**: it keeps our own work honest. What we hand to others is a **rope**: a Lean theorem checked by stock Comparator that needs no trust in GP. The first rope is [`ropes/r1a`](ropes/r1a/README.md).

## What is in this release

- **Kernel** ([`phase2/lean`](phase2/lean)). A Mathlib-free event fold over claims, warrants and supports. It is proved sound, complete, order independent, total and deterministic, on standard axioms only, and pinned in `KERNEL-PIN.json`.
- **3a algebraic profile** ([`profile/`](profile), Mathlib-free on HexMvPoly).
  - Statements are polynomial systems: EMPTY, NONEMPTY, IN_IDEAL, VANISHES_ON, NOT_IN_IDEAL and COVER, over characteristic-set scopes.
  - Checkers replay certificates in exact rational arithmetic. They compute each certificate's *reach*, the characteristics where it holds, from its denominators.
  - Transport rules R1–R4 carry claims along inclusions, polynomial maps and covers.
- **Soundness binding** ([`binding/`](binding), Mathlib). Every claim the kernel fold holds means its statement in every field of its scope, through checkers, rules or generated theorem warrants. See [TCB.md](TCB.md) for what is trusted.
- **Corpus** ([`corpus/`](corpus)). 462 source-linked cases with fixed expectations. All 105 cases owned by the 3a profile agree. There are zero false ACCEPTs across the 242 profile cases.

Since the first alpha, this release adds:
- semireal, ℚ and ℝ claims (3b);
- the census profile;
- a pilot campaign;
- Comparator warrants for 1,882 of 1,887 supported pilot claims, including 57 of 62 EMPTY exclusions;
- the unit-distance theorems;
- rope R1a.

See the [release notes](reports/RELEASE-NOTES-v0.50.0.md), the [guarantees](GUARANTEES.md), the [usage guide](docs/USING-GP.md) and the [review guide](REVIEW.md).

**Coverage by kind of conclusion.** Of the pilot campaign's 1,887 supported claims, only the Comparator-warranted ones need no trust in GP ([Track E report](reports/TRACK-E-REPORT.md#coverage-by-kind-of-conclusion)):

| Kind | Comparator-warranted | Trust needed |
|---|---|---|
| Map rule (at p, or outside S) | 1,250 | Lean, Mathlib and Comparator |
| Point (at p, or outside S / characteristic 0) | 553 | Lean, Mathlib and Comparator |
| Bridge and source (NOT_IN_IDEAL(1)) | 22 | Lean, Mathlib and Comparator |
| **EMPTY** (no field in scope realizes M) | **57 of 62** | Lean, Mathlib and Comparator. The other 5, whose certificates are too large to emit, are held by the belay only (GP's [TCB](TCB.md)). |

[LIMITS.md](LIMITS.md) and [KNOWN-CONSERVATISM.md](KNOWN-CONSERVATISM.md) list what GP refuses that it could, in principle, accept.

## Try it

You need [elan](https://github.com/leanprover/elan); each package's `lean-toolchain` selects its Lean version. You also need Python 3.10 or later.

**Reproduce from the release tag.** `v0.50.0` is tagged on the exact commit on which CI passed; `reports/STABLE-PUBLICATION.json` records it. To use GP on your own problem, start with [docs/USING-GP.md](docs/USING-GP.md).

```bash
cd profile && lake build gp_corpus_run && cd ..
profile/.lake/build/bin/gp_corpus_run . profile/slice/corpus-3a.json
```

The runner prints one JSON receipt: each case's observed verdict, its mechanism and the reach of what was held. To check the soundness proofs, build the binding; this fetches a Mathlib cache:

```bash
cd binding && lake exe cache get && lake build GPBinding
```

The 0.50 tests are `tests/test_phase2_*.py`, `tests/test_gp50_*.py` and `tests/test_layer_tags.py`.

## Reading order

1. [STATUS.md](STATUS.md): the current checkpoint.
2. [REVIEW.md](REVIEW.md): what is new and what to scrutinise.
3. [Phase 3a report](reports/PHASE-3A-REPORT.md) and [Phase 3b report](reports/PHASE-3B-REPORT.md): the profiles, their gates and their findings.
4. [SPEC-CORE.md](SPEC-CORE.md): the core contract.
5. [TCB.md](TCB.md), [LIMITS.md](LIMITS.md), [KNOWN-CONSERVATISM.md](KNOWN-CONSERVATISM.md).
6. [DECISIONS.md](DECISIONS.md): every ratified decision, in order. Campaign-sensitive entries are withheld until outreach.

## v0.37

The previous line is frozen at [`v0.37.0`](https://github.com/wstrinz/grandportage/tree/v0.37.0). It remains the reference implementation and fixture source. Its README and review brief are preserved in [`HISTORY/`](HISTORY).
