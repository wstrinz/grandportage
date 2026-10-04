# Grand Portage v0.50.0-alpha

The first public release of the 0.50 rework, at the G3a gate (ratified 2026-10-03). This is a research alpha, not a production release. The v0.37 line stays frozen at `v0.37.0`; its docs are archived in `HISTORY/`.

## What 0.50 is

GP holds a mathematical claim only through current, bound evidence and sound admitted rules, throughout the scope the evidence earns.
- **Kernel.** A small Lean kernel folds the event log into held claims.
- **Profiles.** A profile supplies the statement language and the checkers.
- **Proof.** Every checker and rule the 3a profile admits is proved sound in Lean against Mathlib.

## In this release

- **Kernel** (`phase2/lean`, Mathlib-free).
  - The fold is sound, complete, order independent, total and deterministic.
  - Retraction removes exactly the claims whose every derivation used the retracted support.
  - Standard axioms only; pinned by `KERNEL-PIN.json`.
- **3a algebraic profile** (`profile/`), on HexMvPoly.
  - Polynomial systems with kinds EMPTY, NONEMPTY, IN_IDEAL, VANISHES_ON, NOT_IN_IDEAL (including geometric nonemptiness) and COVER, over characteristic-set scopes.
  - Exact rational replay of certificates, with computed reach: the characteristics a certificate's denominators allow.
  - Transport rules R1–R4 along inclusions, polynomial maps and covers, plus a bridge from witness points to ideal non-membership.
- **Soundness binding** (`binding/`, Mathlib `85e3a25e`). Every claim the fold holds means its statement in every field of its scope. Theorem warrants are generated as `linear_combination` proofs at each receipt's computed reach, bound through an environment-stamped binder.
- **Corpus** (`corpus/`).
  - 462 source-linked cases with fixed expectations, and gate owners for every case.
  - Signed instantiation fixtures for cases whose inputs omit their mathematics.
  - All 105 3a-owned cases agree; zero false ACCEPTs across all 242 profile cases.

## Not in this release

- Real-closed and number-field claims (Phase 3b).
- Census and combinatorial certificates (Phase 4).
- Campaign operations.
- Any claim about intended meaning: GP cannot tell that a problem was specified wrongly.

See `LIMITS.md` and `KNOWN-CONSERVATISM.md`.

## Reproducing

You need elan and Python 3.10 or later. The `gp50` CI job builds the kernel, the profile and the binding (using a Mathlib cache), then runs the 0.50 suite. The Phase 2 harnesses pin the v0.37 oracle to `oracle/PIN.json`; CI materializes it from the workspace repository.
