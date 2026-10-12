# Phase 5 cost log (prospective)

Builder, 2026-10-09. Authority:
- post-G2 handoff §6: "Prospective cost-log schema written before the u(22) slice starts";
- rev 3 §9 (Phase 5 and gate G5);
- post-G4 §8 (arm (b) is Lean plus Comparator; 12 home and 6 foreign incidents).

Schema: [`campaigns/schemas/cost-log.schema.json`](../campaigns/schemas/cost-log.schema.json) (`gp-cost-log/v2`, a superset of v1), checked by `tools/check-campaign-logs.py`.

## What is logged, and when

One JSON line per task, written **when the task ends and before its result is compared with anything**. That is what makes the log prospective. An entry is never edited afterwards; a correction is a new line whose `notes` names the entry it corrects.

| Stage | Task | Extra fields |
| --- | --- | --- |
| `tutorial` | the fifteen-minute tutorial campaign (rev 3 §9.2) | none |
| `u22` | each u(22) slice task (a family of graphs, an exclusion, a realization) | `time_to_first_held_seconds`, `obligations_resolved` |
| `arm` | one incident run through one arm | `arm`, `incident`, `incident_set`, `outcome`, `time_to_first_held_seconds`, `obligations_resolved` (all required) |

Every entry also has the v1 fields:
- wall time;
- agent turns;
- tokens, where the harness reports them;
- `catches`: real errors stopped, each with its claim;
- `false_refusals`: sound claims refused, each also logged in the friction log;
- `near_misses`: errors that nearly got through, or cost a lot to avoid, each with its cost.

## Arms

- **(a) `gp`:** the core.
- **(b) `lean-comparator`:** every claim is written as a Comparator challenge and checked with stock `comparator`.
- **(c) `notebook`:** notebook plus checker scripts plus CI, the DK-style baseline.

Rules:
- Each arm runs each incident with a **separate agent**. No agent sees another arm's log or result.
- Home incidents (12, from `INCIDENT-INVENTORY.md`, stratified by class) and foreign incidents (6, from the frozen `reports/FOREIGN-SET.json`) are logged the same way and **reported separately**.

## How G5's thresholds read off the log

Per arm, over the 18 `arm` entries:
- **Catches:** the count of `outcome = caught`.
- **Effort:** the sum of `wall_seconds` and of `agent_turns`. Tokens are reported where present, but no threshold uses them, because not every harness reports them.

The thresholds:
- **Beats the notebook (c):**
  - catches(a) ≥ catches(c) + 2 with effort(a) ≤ 1.5 × effort(c), or
  - equal catches with effort(a) ≤ 0.75 × effort(c).
- **Not dominated by Lean (b):** catches(a) ≥ catches(b) − 1.
- **Beats Lean (b) on workability:**
  - median `time_to_first_held_seconds` is lower for (a);
  - Σ`agent_turns` / Σ`obligations_resolved` is lower for (a).

The combined 18 decide the thresholds. If (a) does worse than (c) on the foreign six, that is reported prominently even when the combined thresholds pass (post-G3a §7).

## Definitions

- **A catch** is an incident error the arm stops before anything rests on it: a refusal, a failed check, or a flagged premise. Noticing the error afterwards is not a catch.
- **An obligation is resolved** when it is held, or refused with a recorded reason. Merely OPEN obligations do not count.
- **Time to first held claim** runs from the task's `started` to the first claim the arm's own checker accepts.
