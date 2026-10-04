# Grand Portage 0.50 (alpha)

Grand Portage holds a mathematical claim only through current, bound evidence and sound admitted rules, and only throughout the scope that evidence earns. When a certificate divides by 2, GP does not let the claim it supports reach characteristic 2.

0.50 is a rework of the [v0.37 line](#v037). A small Lean kernel decides which claims are held. Profiles supply the statement language and the checkers, and their soundness is proved in Lean against Mathlib.

**Status: `v0.50.0-alpha`; G3a ratified 2026-10-03.** This is a research alpha, not a production release. See [STATUS.md](STATUS.md).

## What is in this release

- **Kernel** ([`phase2/lean`](phase2/lean)). A Mathlib-free event fold over claims, warrants and supports. It is proved sound, complete, order independent, total and deterministic, on standard axioms only, and pinned in `KERNEL-PIN.json`.
- **3a algebraic profile** ([`profile/`](profile), Mathlib-free on HexMvPoly).
  - Statements are polynomial systems: EMPTY, NONEMPTY, IN_IDEAL, VANISHES_ON, NOT_IN_IDEAL and COVER, over characteristic-set scopes.
  - Checkers replay certificates in exact rational arithmetic. They compute each certificate's *reach*, the characteristics where it holds, from its denominators.
  - Transport rules R1–R4 carry claims along inclusions, polynomial maps and covers.
- **Soundness binding** ([`binding/`](binding), Mathlib). Every claim the kernel fold holds means its statement in every field of its scope, through checkers, rules or generated theorem warrants. See [TCB.md](TCB.md) for what is trusted.
- **Corpus** ([`corpus/`](corpus)). 462 source-linked cases with fixed expectations. All 105 cases owned by the 3a profile agree. There are zero false ACCEPTs across the 242 profile cases.

Not yet covered: real and number-field claims (Phase 3b), census and combinatorial certificates (Phase 4), and campaign operations. [LIMITS.md](LIMITS.md) and [KNOWN-CONSERVATISM.md](KNOWN-CONSERVATISM.md) list what GP refuses that it could, in principle, accept.

## Try it

You need [elan](https://github.com/leanprover/elan); each package's `lean-toolchain` selects its Lean version. You also need Python 3.10 or later.

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
2. [Phase 3a report](reports/PHASE-3A-REPORT.md): the profile, its gate and its findings.
3. [SPEC-CORE.md](SPEC-CORE.md): the core contract.
4. [TCB.md](TCB.md), [LIMITS.md](LIMITS.md), [KNOWN-CONSERVATISM.md](KNOWN-CONSERVATISM.md).
5. [DECISIONS.md](DECISIONS.md): every ratified decision, in order.

## v0.37

The previous line is frozen at [`v0.37.0`](https://github.com/wstrinz/grandportage/tree/v0.37.0). It remains the reference implementation and fixture source. Its README and review brief are preserved in [`HISTORY/`](HISTORY).
