# Phase 3P report: the campaign agent's run (F0 and F1)

2026-10-05. Inputs: `campaign.json`, `GP-CLI.md` and handoff §4. Search: Singular and sympy, untrusted; GP replayed everything.

## Result

F0 and F1 are done. **All 11 matroids have χ(M) fully held, modulo the OPEN `ENCODING-FRAME` premise.**

| M | χ(M) held | Stated answer [VERIFY] | How |
|---|---|---|---|
| F7 | {2} | {2} | ℚ C1 certificate (denominator 2), plus an F₂ point and a bridge |
| F7⁻ | all except 2 | all except 2 | ℚ point (one guard = 2), plus a mod-2 C1 certificate |
| M(K4) | all | all | ℚ point, all guards ±1 |
| U(3,6) | all | all | ℚ point outside {2,3,5,7}; F₄ and F₉ via map; F₅ and F₇ points |
| Pappus | all | all | ℚ point outside {2,3,5}; F₄, F₉ and F₂₅ via map |
| Desargues | all | all | ℚ point outside {2,3,5}; F₁₆ and F₉ via map; F₅ point |
| AG(2,3) | all | all | ℚ(ω) via map outside {3}; F₃ point |
| AG(2,3)∖e | all | all | the same as AG(2,3) |
| PG(2,3) | {3} | {3} | ℚ C1 certificate (denominator 3); F₃ point |
| non-Pappus | ∅ | ∅ | one integer C1 certificate, every characteristic |
| non-Desargues | ∅ | ∅ | one integer C1 certificate, every characteristic |

- **Correctness.** F0 is exact, and there are zero disagreements with the stated answers. No result breaks the Rado–Vámos dichotomy.
- **Safety.** There were no false ACCEPTs, as far as I could test them. I deliberately ran three overclaims and one control, and all four were refused. The Kernel pin is unchanged.
- **Ledger.** 44 held claims, 4 refused, 0 open.

## Cost

About 38 agent-minutes over 36 logged turns, plus a 5-minute first-use build of `gp_ledger`. Token counts are unavailable. Most of the time went into search tooling; a GP submit took about 2 seconds.

## Friction: 17 refusals, 10 useful, 7 ergonomic, 0 false

Real catches: two `proper_coefficient` receipts at a zero coefficient (my bug), three tutorial overclaims, and map submissions made before their premise was held.

Ergonomic findings for the builder, roughly in order of importance:
1. **`status` has no χ roll-up.** The reader has to assemble "χ(PG23) = {3}, fully held" from three lines. This is the main risk to the Elm test. One verdict line per matroid would fix it.
2. **Generic exact-replay message.** One message ("a residual, a point or a guard") covers every replay failure, including `proper_coefficient`, where none of the three applies. It never names the failing equation, guard or coefficient.
3. **Uncaught exception on a missing receipt.** `gp submit` with a missing receipt file prints a Python traceback, not a refusal.
4. **`--matroid` takes a name, not a path**, which the doc doesn't say.
5. **Decimals in a point** are refused as "unexpected character '.'" instead of "decimals are not exact; write p/q".
6. **`status` is slow:** 16 seconds with 48 claims.
7. **Doc gaps.** `--outside ""` (every characteristic) and the map rule's guard-obligation format are undocumented. A mod-p point can earn a sound ℚ widening, which contradicts "the reach is exactly {p}".

No builder fixes have been made yet. Every ergonomic item is marked `reported_to_builder`.

## Deliverables (all in `campaigns/3p-matroids/`)

- `ledger.jsonl`, `tailings.json` (61 entries, in source / reliability / completeness form), `cost-log.jsonl` and `friction-log.jsonl`. The logs pass `check-campaign-logs.py`.
- `TUTORIAL.md`: the F0 script, with three overclaims, one honest result, one tailing and one earned widening.
- `matroids/`, `receipts/` and `systems/` for replay.
- `warrants/`: **coverage is 4 of 44 held claims (9%).** The generator covers only EMPTY by a C1 certificate over ℚ. Points, bridges, maps and mod-p certificates are outside it, so no realizability direction has a warrant. The warrant files are emitted but **not compiled here**, because the Mathlib binding is not built in this checkout.

## Open items

- **`ENCODING-FRAME`** is OPEN on every result. It is *closable in principle*: the PGL₃ normalization is standard, and a Lean proof should be cheap.
- **Citations.** The F1 citations (Oxley, 2nd ed.) carry section numbers from memory, so they are still `[VERIFY]`. The ledger agrees with every stated answer, but nobody has checked the citations against the book.
- **F2** (the catalog up to 8 elements) has not started.

## Questions for Will

1. **How to classify `emit-lean` coverage refusals.** No friction class fits. They are not catches, the message is clear, and the claim stays held. I kept them in `warrants/coverage.txt` rather than adding 40 friction entries. My recommendation: treat coverage as a separate metric, not as friction.
2. **Autonomy disclosure.** Besides the three permitted inputs, I read `AGENTS.md`, the top of `STATUS.md` and the 3P commit message. I did not read the builder's source beyond two traceback lines. I wrote the F1 line sets from geometric definitions.
