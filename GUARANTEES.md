# What Grand Portage 0.50 guarantees

Every guarantee below names the theorem or test it rests on. Every theorem uses only `propext`, `Quot.sound` and `Classical.choice`. Standing limits are in [LIMITS.md](LIMITS.md), and the full trust record is in [TCB.md](TCB.md).

## The Kernel

The Kernel ([`phase2/lean/GP50`](phase2/lean/GP50)) is Mathlib-free. It folds an append-only ledger of claims, warrants and lifecycle events.

- **Sound.** If a profile's validators are sound, every claim the fold holds means its registered statement at its scope: `GP50.Semantic.fold_held_meaning` (`NarrowingAdmissionProofs.lean`), built on `closure_sound`. Under sound validators, a conflict the fold reports has no shared witness (`sound_fold_conflict_has_no_witness`). So a confirmed conflict exposes a broken assumption.
- **Complete, as finite reachability.** A claim is held exactly when one of its warrants is reachable in the support graph of admitted checks and rules: `held_fold_iff`, `closure_mem_iff_reachable` and `closure_complete`.
- **Order independent, total, deterministic.** The result depends only on the set of events (`fold_eq_of_mem_iff`, `fold_perm`, `fold_duplicate`). The fold returns a state or a named error (`fold_total`).
- **Pinned.** `KERNEL-PIN.json` binds the 22 Kernel files and the toolchain (`tests/test_gp50_kernel_pin.py`). A change needs Will's approval and an entry in [PROMOTIONS.md](PROMOTIONS.md). Each promotion re-runs `tools/check-kernel-axioms.py`, which replays every module with `leanchecker` and audits the axioms of every Kernel constant.

## Profiles, sound against Mathlib

Profiles supply statements and checkers. The binding ([`binding/`](binding)) proves them sound against Mathlib:

- **3a, algebraic.** `GPBinding.Admission.fold_held_meaning`: a held claim's statement holds in every field whose characteristic its scope contains. `fold_held_meaning_rules` extends this to rules and theorem warrants, under the binder's `RecordsSound`. The per-certificate theorem is `check_sound`.
- **3b, semireal, ℚ and ℝ.** `fold_held_meaning3`: a held claim means its statement in every context its scope denotes, including SOS, ordered, real-point, case-tree and number-field evidence.
- **Census.** `GPCensus.fold_held_meaning` (Mathlib-free): a held claim holds at every parameter its scope lists.
- **Encodings.** The matroid frame is proved by `GPBinding.Matroid.frame_iff`, and the unit-distance frame by `GPBinding.UDG.udg_frame_iff`. In both cases `gp` re-derives the system with the Lean encoder.
- **Withdrawal (0.51).** Both runners retract a withdrawn claim's warrants in every fold. The theorems above quantify over every event list, so what stays held keeps its meaning. `GPProfile.Withdraw` (Mathlib-free) proves that withdrawal only un-holds (`withdraw_antitone`), never breaks the fold or merge of a log without supersessions (`withdraw_resolves`), and leaves a withdrawn claim not held (`withdraw_unholds`; for every 3a and 3b run, `runWith_withdrawn` and `run3_withdrawn`).

## What "held" means

On every command the Kernel fold replays every receipt and reaches a warrant for the claim. By the theorems above, the claim's registered statement is then true in every model its scope denotes.

**Reach.** A certificate holds a claim only where its arithmetic is valid. A certificate that divides by 2 does not reach characteristic 2 (`tests/test_gp50_gp_cli.py`: `test_2_fano_empty_over_q_excludes_2`, `test_3_non_fano_rational_point_does_not_reach_2`).

**Goals.** A DECIDE goal's verdict is held by the Kernel.
- `goal n m true` is held only through the admitted `realize` rule (`realizeRuleOk_sound`, from `udg_frame_iff` and `realize_sound`).
- `goal n m false` is held only through `decide`, from a held `spine` implication (`spineRuleOk_sound`, from `spine_sound`) and a held `cover`.
- A cover is held only by an exhaustive-list check (`coverAllCheck_sound`), never by a named premise.
- Held goal claims mean their statements (`fold_held_goal`, `fold_held_not_Q`).

`status` and `frontier` print the fold's verdict. The one thing they add is to *withhold* "decided" when a held goal claim inherits OPEN named premises ([design](docs/A2-GOAL-STATEMENT-DESIGN.md)).

## The TCB on one screen

| Trusted | For what |
|---|---|
| The Lean 4 kernel and the three axioms | every proof |
| The pinned toolchain (`v4.35.0-rc3`, a release candidate; R1a uses `v4.34.1`) | elaboration and compiled code |
| Compiled checkers: Hex v0.9.0 arithmetic with the linked `HexModArith`/`HexArith` C code, GMP-backed `Rat`/`Int`, and the vendored LRAT checker (census) | running the code the proofs describe |
| Mathlib at the binding's pin (`6b7abb3c`) | that its definitions say what the meanings intend |
| `tools/gp.py` | serialising each claim's statement and scope faithfully, invoking the runners and merging their results |
| Stock Comparator, `lean4export` and `landrun`, pinned by commit (`comparator.yml`, `ropes/r1a/REPRODUCE`) | rope and warrant checks |

**Not trusted:** certificate producers (CAS, SAT solvers and search tools); the Python matroid and graph encoders, whose output the Lean encoders re-derive; Comparator emitters, whose output Comparator checks; file modification times (runner freshness uses content hashes, `tests/test_gp50_runner_freshness.py`). An edited campaign statement is refused until restated (`tests/test_gp50_statement_binding.py`).

## What is not claimed

- No published result has yet been independently re-established outright.
- **Intended meaning and encoding are separate obligations.** The theorems cover the registered statement. Whether that statement says what a paper means is the job of fidelity reviews, such as rope `FIDELITY.md` files and the [GE audit](reports/GE-AUDIT.md).
- **Named OPEN premises are metadata, not Kernel facts.** `gp` tracks and prints them ("modulo …", "conditional:"). The Kernel neither checks them nor depends on them.
- **Completeness is not search.** It is finite reachability under the admitted instances. It does not cover every logical consequence, exhaustive campaign search or checker acceptance.
- **Coverage is uneven.** Only Comparator-checked claims need no trust in GP. Five 3P EMPTY claims, whose certificates are too large to emit, are held by the belay only. See [coverage by kind](reports/TRACK-E-REPORT.md#coverage-by-kind-of-conclusion).
- **Axiom audits.** CI audits the theorems cited here (`tests/test_gp50_axiom_audit.py`, with a control); the full Kernel audit runs at promotion.
