# Review guide: v0.50.0

2026-10-12. The first stable 0.50 release. The earlier guides are in [HISTORY/](HISTORY/). Start with [GUARANTEES.md](GUARANTEES.md), then the [release notes](reports/RELEASE-NOTES-v0.50.0.md). Review does not imply production soundness.

Active campaign material is withheld until outreach is done (see the release notes). Some links in retained documents point to withheld files.

## What changed since alpha.2, and why

An external review of alpha.2 found that the remaining risks were places where **the sentence GP prints could outrun what the Kernel established**. This release closes them:

| Concern raised | What v0.50.0 does | Where to check |
|---|---|---|
| The goal verdict came from a Python join over proved pieces | The goal is a Kernel-held profile statement, reached only through admitted rules proved sound. Graph matching is a Lean admission check. | `profile/GPProfile/Real/Goal.lean`, `binding/GPBinding/Real/GoalSound.lean`, [A2 design](docs/A2-GOAL-STATEMENT-DESIGN.md), `tests/test_gp50_gp_cli_udg.py` |
| Edits to `campaign.json` after `init` went undetected | The statement is bound by hash, and every command verifies it; a deliberate change is a `restate` event | `tests/test_gp50_statement_binding.py` |
| Runner freshness used file modification times | Content-hash stamps | `tests/test_gp50_runner_freshness.py` |
| 3b claims bypassed the merge guard | `gp_ledger3 --guard` runs the Kernel's `resolve` | `tests/test_gp50_merge_guard_3b.py` |
| Coverage hid the 62 EMPTY exclusions | Coverage is reported by kind of conclusion; 57 of 62 EMPTY claims now pass Comparator | [Track E report](reports/TRACK-E-REPORT.md#coverage-by-kind-of-conclusion) |
| R1a's non-vacuity rested on private records | Exact gadget embeddings are Lean theorems in the rope | `ropes/r1a/UDGRope/Embeds.lean` |
| Standard-axiom status was asserted, not checked | A CI axiom audit of every theorem GUARANTEES cites, with a negative control | `tests/test_gp50_axiom_audit.py` |
| The docs mixed history with current limits | GUARANTEES, a current LIMITS and a TCB summary; history kept in `HISTORY/` | [GUARANTEES.md](GUARANTEES.md), [LIMITS.md](LIMITS.md), [TCB.md](TCB.md) |
| Hard to use outside this repo | A usage guide with a replayed worked example, a compatibility statement, and an outside-repo test | [docs/USING-GP.md](docs/USING-GP.md) |

## Questions for review

- **The goal rules.** Do `realize`, `spine` and `decide` admit exactly what `fold_held_goal` needs? Is "a cover is held only by an exhaustive list" the right bar?
- **The remaining Python.** `TCB.md` says the Python now only serialises claims, proposes rule instances and renders fold results. Is anything it still decides missing from that list?
- **EMPTY warrants.** Does `GPEmpty.frame4` (frame normalization) faithfully reduce "no field in scope realizes M" to the framed system?
- **The compatibility promise.** Is the `gp-ledger/v1` statement in USING-GP something we can keep?

## Known limits

See [LIMITS.md](LIMITS.md):
- ℝ only, not every real closed field;
- number fields of degree ≤ 3;
- 5 EMPTY claims without a warrant (their certificates are too large);
- no `≥ 0` sign atom;
- no Gram↔coordinate map rule;
- no withdrawal of refused claims.

No published result has yet been independently re-established outright.

## Reproduction

See the release notes. Tests: `python -m pytest -q -k gp50 tests/`. R1a: `cd ropes/r1a && bash REPRODUCE`.
