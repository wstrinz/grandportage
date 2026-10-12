# Rope checklist

Builder, 2026-10-09, from the [fixed-ropes handoff](GP-0.50-FIXED-ROPES-HANDOFF.md) §1, with Will's four amendments (DECISIONS 2026-10-09). Ropes are assembled by hand from this list. There is no packaging tool before G5.

A rope is a directory `ropes/<id>/` that anyone can check without trusting GP. Tick every box before calling it delivered.

## Contents of the directory

- [ ] A Lake package with its own `lean-toolchain` and `lake-manifest.json`. It is pinned to the current Mathlib release, or to the counterpart's pin when it discharges one of their hypotheses. Never pinned to GP's.
- [ ] `README.md`, at most 600 words:
  - the tier;
  - the main theorem, verbatim;
  - each hypothesis and what would discharge it;
  - the independence line;
  - the provenance;
  - what was **not** checked.
- [ ] `formalization.yaml` (mathlib-initiative schema): the source, and how faithfully the statement tracks it.
- [ ] `FIDELITY.md`: the M5 pitfall list run against the statement (below).
- [ ] `MANIFEST`: SHA-256 of every input file and certificate.
- [ ] `REPRODUCE`: one command from a clean machine. It may fetch the Mathlib cache.
- [ ] A CI job that runs stock Comparator.

## 1. Statement

- [ ] The main theorem uses Mathlib vocabulary.
- [ ] Where formal-conjectures or another public source states the result, the rope uses that statement verbatim, or proves an equivalence to it inside the rope.
- [ ] At most 40 lines of definitions beyond Mathlib. If it needs more, stop and ask Will.

## 2. Check

- [ ] Stock `comparator`, built for the rope's own toolchain, accepts the challenge against the solution. Log any Comparator or lean4export build as `rope-port` friction.
- [ ] `#print axioms` on the main theorem shows exactly `propext`, `Classical.choice` and `Quot.sound`.
- [ ] The dependency cone has no `sorry`, no `native_decide` and no `ofReduceBool`.
- [ ] The controls are refused by Comparator: a `sorry` solution, a weakened statement, and a redefined constant.
- [ ] Each control counts as refused only when Comparator prints *that control's expected reason*: illegal `sorryAx`, statement mismatch, or const mismatch. A missing "okay" alone is not enough, since a crashed run must fail (GR1 finding, 2026-10-09).
- [ ] `REPRODUCE` runs preflight checks for its tools and prints progress per step.

## 3. Hypotheses

- [ ] Everything not proved is a named `Prop` hypothesis of the main theorem, never an `axiom`.
- [ ] Each hypothesis is listed in the README with its discharge route.

## 4. External certificates

- [ ] SAT or enumeration evidence enters in one of two ways:
  - **(a) Kernel-checked** in Lean. This route is T1.
  - **(b) The T1x route:** one UNSAT hypothesis, whose CNF encoding is proved correct in Lean and whose LRAT is checked by a named verified external checker (cake_lpr). The certificate hash goes in `MANIFEST`.
  - **(c) A named hypothesis** under item 3. This route is T2.
- [ ] An unproved encoding is a hypothesis, never a footnote.
- [ ] **Census-style checks** (rule-generated lists): the checker is a small pure function over plain lists, evaluated by kernel `decide` in shards under a memory cap. If that is infeasible, use route (c), never `native_decide`.

## 5. Fidelity (`FIDELITY.md`)

Each item gets a line saying how it was checked:
- [ ] ordered versus unordered pairs;
- [ ] metric: `EuclideanSpace`, never `Fin 2 → ℝ` or `ℝ × ℝ`;
- [ ] injectivity and distinctness;
- [ ] faithful versus non-faithful embeddings;
- [ ] `sSup` junk values (`BddAbove`);
- [ ] ℕ subtraction and division;
- [ ] vacuous or contradictory hypotheses.
- [ ] A non-builder agent reviews `FIDELITY.md`. This is required at GR1.

## 6. Reproduction

- [ ] A fresh agent, given only the README, reproduces the result: in at most 15 minutes for GR1, plus the Mathlib cache download.

## 7. Provenance and independence

- [ ] The README states which parts were produced by AI agents, with which models and tools.
- [ ] The independence line names what is shared with the result being checked (code, method, lemmas, premises, model family) and what is not.
- [ ] "Independent verification" is used only for what that line covers. Human review is named as absent until it happens.

## Tier, last

| Tier | Requires |
|---|---|
| **T0** | merged into Mathlib or FC |
| **T1** | sections 1–7 hold, with no hypotheses |
| **T1x** | as T1, except for one UNSAT hypothesis under 4(b) |
| **T2** | sections 1–7 hold; named hypotheses, each with a discharge route |
| **T3** | a replay with manifests only; an input to a T1/T2 rope, never delivered alone |

- [ ] The tier is stated. The rope is described no higher than its tier.
- [ ] `ropes/README.md` is updated.
- [ ] Custody rules apply (post-G3a §8).
