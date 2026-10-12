# Grand Portage v0.50.0-alpha.2

The second public research alpha of the 0.50 rework (2026-10-11). It is not a production release. The first alpha, `v0.50.0-alpha`, was at G3a; this one adds gates G3P, G4, GK, G3b and GE, and the first **rope**.

## What changed in the framing

GP is a **belay**: a private ledger that keeps our own work honest, tracking what is held, what rests on named OPEN premises, and what is refused. What we hand to others is a **rope**: a Lean 4 theorem in Mathlib vocabulary, checked by stock [Comparator](https://github.com/leanprover/comparator) on the three standard axioms. A rope needs no trust in GP. The contract is in `docs/ROPE-CHECKLIST.md`.

## In this release

- **Pilot campaign (G3P).** Characteristic sets of rank-3 matroids: χ is held for 493 matroids, with a cold read by Will under 10 minutes (`campaigns/3p-matroids/`).
- **Census profile (G4)** (`census/`, Mathlib-free).
  - EXISTS, NONE, EXHAUSTIVE and COUNT, with certified counting and HexGraphIso canonical forms.
  - Extension covers whose list generator is in Lean, so coverage holds by construction.
- **Performance (GK).** Every speedup is proved equal to the code it replaces (`@[csimp]` or `_eq` theorems), and outputs are byte-identical. There is no cross-run result cache: every fold replays every receipt.
- **Semireal, ℚ and ℝ contexts (G3b).**
  - Exact SOS and Krivine–Stengle certificates, with guard selection.
  - Real algebraic points and root covers.
  - Number fields and `algPoint`.
  - `case_tree` refutations: rhombus-collision and forced-unit-distance steps, with explicit injectivity guards.
  - All proved sound against Mathlib (`fold_held_meaning3`).
- **Comparator warrants (GE).** 1,825 of 1,891 pilot claims are emitted as Comparator challenges and pass stock Comparator in CI. A non-builder audit of 20 random challenges found zero fidelity defects.
- **CLI** (`tools/gp.py`):
  - real-context claims;
  - a merge guard with content-derived keys;
  - graph-bound unit-distance claims;
  - DECIDE goals that are decided only through admitted bridges;
  - receipt files verified by SHA-256 on every fold;
  - a `frontier` that shows unresolved goal obligations.
- **Unit-distance theorems** (`binding/GPBinding/UDG/`): the rhombus lemma, six TU gadget lemmas, Schade averaging, the UDG encoding frame, and `spine_sound`, each with a Comparator challenge.
- **Rope R1a** (`ropes/r1a/`, T1 candidate). These Mathlib-only theorems are pinned to Lean and Mathlib v4.34.1, and use formal-conjectures' `maxUnitDistances` verbatim (see `NOTICE`):
  - the rhombus lemma (a 4-cycle in an injective unit-distance embedding is a parallelogram);
  - the six TU gadget lemmas;
  - heredity;
  - Schade averaging, u(n) ≤ ⌊n·u(n−1)/(n−2)⌋.

  Stock Comparator accepts all 9 and refuses each control with its expected reason. `bash REPRODUCE` reproduces this from a clean machine.

## Withheld from this release

Active campaign material is withheld until the related outreach to other researchers is done:
- the campaign packets and ledgers;
- the campaign-sensitive decision entries (dated pointers remain in `DECISIONS.md`);
- one rope in preparation.

A later release will add them.

## Limits

These are listed in `LIMITS.md`, `KNOWN-CONSERVATISM.md`, `TCB.md` and `REVIEW.md`:
- ℝ only, not every real closed field;
- degree ≤ 3 number fields;
- 62 pilot EMPTY claims without a Comparator warrant;
- trusted Python joins in the goal bridges.

GP cannot tell that a problem was specified wrongly. That is what the rope fidelity reviews are for.

## Reproducing

- **Toolchain:** elan and Python 3.10 or later.
- **Lean packages:**
  - `phase2/lean`, the Kernel;
  - `profile`;
  - `binding`, which needs `lake exe cache get`;
  - `census`.
- **Tests:** `python -m pytest -q -k gp50 tests/`. Suites that need the private oracle or withheld campaign data skip.
- **R1a:** `cd ropes/r1a && bash REPRODUCE` on Linux, about 16 min plus the Mathlib cache download.
