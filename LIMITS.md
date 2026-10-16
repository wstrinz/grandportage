# Standing limits

The current limits of GP 0.50 (2026-10-13), which apply throughout. Guarantees are in [GUARANTEES.md](GUARANTEES.md); sound refusals stronger than necessary are in [KNOWN-CONSERVATISM.md](KNOWN-CONSERVATISM.md); the Phase 2-era limits are in [HISTORY/LIMITS-pre-0.50.md](HISTORY/LIMITS-pre-0.50.md).

## Meaning

- **Soundness concerns the registered statement, model and scope.** Intended meaning, source interpretation and faithful rendering each need their own review.
- **Completeness means finite reachability** under the admitted instances. It is not every logical consequence, exhaustive search or checker acceptance completeness.
- **Empty scopes are vacuous.** They do not supply an existence witness.
- **Only zero guards are refused as vacuous.** `gp` refuses a guard whose canonical form is the zero polynomial (DECISIONS 2026-10-13). It does not detect subtler vacuity:
  - a nonzero guard that vanishes wherever the equations do;
  - guards that are jointly vacuous with the system;
  - a guard whose coefficients all vanish modulo a characteristic in the claim's scope.

  A guarded EMPTY claim is then true vacuously, and `status`, `explain` and `frontier` do not say so. **Convention:** every guarded EMPTY used as a FAIL certificate (a refutation that others rely on) is paired with an E2 non-vacuity claim. E2 is `NOT_IN_IDEAL --target 1` on the same equations plus gᵢ·wᵢ − 1 for each guard gᵢ, with a fresh variable wᵢ per guard, at the same scope. Held, it shows that the guarded locus has a point over an algebraically closed field of the scope.
- **A proved conflict blocks release** separately from held closure. Unknown overlap stays unresolved.
- **Named OPEN premises are metadata.** No checker is admitted for them, and the Kernel does not see them.

## Lane P: Lean-proposition claims (0.52, phase P1)

A P campaign states each claim as a registered `def X : Prop` of its own Lake package (or as prose), with premises as scope. What P1 does not do:
- **Only `lean_theorem` holds (tier 2), and it shows as "tier 2 (unreplayed)".** A module that sets `debug.skipKernelTC` skips build-time kernel checks; the binder's `addDecl` checks only that the theorem's declared type is the claim's. Closing that needs the lean4checker replay (phase P2). Comparator receipts, profile replay of 3a/3b claims and `min_reader` are also P2.
- **The soundness theorem quantifies over every interpretation of the codes.** `fold_held_meaningP` holds for any meaning of the registered codes under which the binder's accepted records are true; that the interpretation is the Lean meaning of the registered declarations (the bridge) is P2, and rests on the binder's report.
- **Statement identity** is a SHA-256 over the campaign-local closure of the declaration (types and definition bodies, theorem types only) plus an environment stamp (toolchain and manifest revisions). Pinned dependencies are covered by the stamp alone, so any dependency bump unbinds every claim until the codes are registered again.
- **Recorded-only warrants never hold.** Exact scripts (4), hand proofs (5), numerical evidence (6) and external checkers' logs from other pins or repositories (1–3, decision 3) are recorded and shown, never folded as support. GP cannot tell a sketch from a proof: it enforces the filer's declared state and the reviewer's conditions, which are OPEN premises.
- **Fidelity is data.** "anchored" always shows as "anchored (asserted)" in P1: no anchor is checked.
- **A vacuous premise (`False`) holds anything,** as with zero guards: a fidelity-review item. `contra` is `false`, so P detects no conflicts.
- **Presentations are display-only records.** OVERSTATED marks a tag above the earned tier, or a presentation that drops a premise or a reviewer's condition; a tag of tier 7 asserts nothing.
- **Cost.** A bind is one incremental `lake build` and one binder process that imports the package. On the reference Windows machine the withheld Mathlib-based fixture took 33–55 s per bind with three statements and six theorems: a no-op `lake build` of 13–20 s, then 20–43 s for `lake env` and the Mathlib import; the per-theorem checks are small. A Lean-core package binds in seconds. Views reuse a recorded bind keyed by the package's source tree and inputs (under 1 s a command).
- **Readers older than 0.52 skip P records,** so P claims are invisible to them.

## Mathematical reach

- **ℝ only, not every real closed field.** Selected-root signs mean "some root in the interval".
- **Number fields of degree ≤ 3.** Irreducibility uses the rational-root test.
- **No `≥ 0` sign atom.** Use slack squares instead.
- **No map rule between Gram and coordinate forms.**
- **5 of 62 3P EMPTY claims have no Comparator warrant.** Their certificates are too large to emit (keys 1761, 1772, 1813, 1816, 1829), so they are held by the belay only.
- **Census** counts rest on named premises (V4-NORMAL-FORM, CELL-COMPLETE for the DK slice); fidelity to the source's predicate is checked differentially, not proved.

## Evidence and trust

- **Axioms.** Only `propext`, `Quot.sound` and `Classical.choice` are allowed. There is no `sorry`, `native_decide`, `Lean.ofReduceBool` or custom axiom.
- **Compiled checkers.** Checkers run as compiled code. The proofs are about the source, so the compiler and runtime are trusted ([TCB.md](TCB.md)).
- **Axiom audits.** The Kernel is audited constant by constant at each promotion. CI (`tests/test_gp50_axiom_audit.py`) checks the main soundness theorems on every run, including a control that must flag a custom axiom. Other binding constants are covered by the phase reports, not CI.

## Kernel pin and promotion

- `KERNEL-PIN.json` binds the 22 Kernel files and the toolchain, Lean `v4.35.0-rc3` (a release candidate, adopted for Hex v0.9.0). Lean `v4.35.0` is newer; moving to it is a later toolchain-only promotion, once Hex re-pins.
- **Changes** go through [PROMOTIONS.md](PROMOTIONS.md) with Will's approval. Each entry needs re-check evidence, and the pin is rewritten in the same commit.
- **The corpus is fixed:** case bytes, expectations, source pins and replay history. Receipts bind test and harness bytes, so changing an executed harness requires re-execution.

## Campaign ledgers

- **Withdrawal is permanent and claim-level** (GP 0.51, [docs/WITHDRAWAL-DESIGN.md](docs/WITHDRAWAL-DESIGN.md)). `gp withdraw` retracts a claim's warrants on every fold. There is no un-withdraw, and the label stays taken: file the corrected claim under a new label. A support cannot be withdrawn on its own (a better receipt replaces it), and `goal` and `spine` claims cannot be withdrawn. Raw retraction and supersession records are not applied: `merge` refuses a log that carries them.
- **Readers older than 0.51 do not see withdrawals.** They skip `withdraw` records, so they show a withdrawn claim, and what rests on it, as held again. That is sound (anything held after a withdrawal was held before), but it reverses the owner's decision. A `gp-ledger/v1` ledger cannot make an older `gp` refuse; read ledgers with withdrawals only with 0.51 or newer.

## Public snapshot boundaries

- **Building a release.** `scripts/public_snapshot.py` builds public releases from `public-snapshot-v2.json`. Every tracked path is public, private or generated, and an unclassified path stops the build. Exact paths override prefixes; otherwise the longest matching prefix decides.
- **Withheld:**
  - `campaigns/`, except `campaigns/3p-matroids/` and `campaigns/schemas/`;
  - `ropes/`, except `ropes/r1a/`;
  - `docs/private/`;
  - `DECISIONS-PRIVATE.md`;
  - a few exactly named files;
  - the oracle checkouts.

  Some public documents link to withheld files.
- **Repositories.** The workspace is private (since 2026-10-10). Nothing goes to the public `wstrinz/grandportage` without Will's explicit OK.
- **Public tests.** Suites that need private data skip in the public snapshot.

## Resources

- Every fold replays every receipt; there is no cross-run result cache. `decide +kernel` never runs over Hex-based checkers. A 3P Comparator shard peaks near 7 GB.
