# R1a fidelity note

This note checks the nine main statements of rope R1a against the M5 pitfall list. The vocabulary is `UDGRope/Defs.lean`, which every challenge repeats verbatim. Each item below says how it was checked.

## Sources

- **formal-conjectures (FC) at `b3f26411f06b0b0ec1923da80b62585f23288d39`.**
  - `unitDistNum` comes from `FormalConjecturesForMathlib/Geometry/Metric.lean` (SHA-256 `c08edfee…`).
  - `unitDistanceCounts` and `maxUnitDistances` come from `FormalConjectures/ErdosProblems/90.lean` (`901c9b77…`).
  - `ℝ²` is FC's notation (`2d.lean`, `4d6886a9…`).
  - The bodies are copied character for character. FC's `variable {X : Type*} [MetricSpace X]` becomes explicit binders.
  - The differences are namespacing and the Mathlib pin. The rope's constants are `UDGRope.*`. In FC, `unitDistNum` is at the root, `unitDistanceCounts` and `maxUnitDistances` are in namespace `Erdos90`, and `ℝ²` is scoped in `EuclideanGeometry`. FC pins Mathlib v4.33.1; the rope uses v4.34.1. FC is not a dependency, so the rope does **not** prove that its constants equal FC's. The match is textual, up to renamed constants. Equality of the elaborated terms across the two Mathlib pins is **not checked**.
- **artwaste `data/tu-gadgets.json`** at `ba1c76fd`, LF bytes `a904487c…`. The gadgets `gadget0`, `gadget1`, `gadget2`, `gadget3` and `gadget5` use the same vertex numbers and edge sets. Gadget 4 is gadget 3's graph with the pair (6, 7). This was checked by script against the JSON (`campaigns/ud22/search/check_patterns.py` reads the same file). The GR1 reviewer matched the six JSON gadgets, with their pairs, to AMP's figure of TU graphs 1–6 by brute-force isomorphism. That mapping is **not** checked inside the rope.
- `gadget4_tu` also follows from `gadget5_tu` and heredity, because gadget 5 is a subgraph of gadget 3. It is proved directly here.
- **artwaste `check/PROOFS.md`** for the rhombus fact and the rhombus combinations that prove the gadgets.

## Pitfalls

| Pitfall | How it was checked |
|---|---|
| Ordered vs unordered pairs | `unitDistNum` counts `s.sym2`, which holds unordered pairs. The diagonal `s(x, x)` has distance 0, so it never counts. `Schade.card_avoid` uses exactly this: a unit pair is two distinct points. |
| Metric | All plane statements use `EuclideanSpace ℝ (Fin 2)`, never `Fin 2 → ℝ` (sup metric) or `ℝ × ℝ`. `dist_eq_one_iff` unfolds `dist` to √(Δx² + Δy²). |
| Injectivity / distinctness | `UnitDistEmbedding` (Mathlib) carries `p : V ↪ E`, so it is injective. `rhombus` additionally asks `a ≠ c` and `b ≠ d` (vertices, not points), and injectivity makes the points distinct. **Controls:** `rhombus_needs_injective` shows the conclusion fails without injectivity. Over ℂ the lemma still **holds** for injective maps (`rhombus_complex`). The genuine ℂ subtlety is `complex_isotropic_pair`: distinct points can have Δx² + Δy² = 0, so in a polynomial frame "squared distance ≠ 0" is stronger than injectivity over ℂ but equivalent over ℝ. The packet's original control, "rhombus fails over ℂ", was false and is not used. |
| Faithful vs non-faithful | `UnitDistEmbedding` constrains edges only. Non-edges may be at distance 1, which is exactly what TU gadgets exploit. Each `gadget*_tu` states `¬ G.Adj a b` together with `dist (f.p a) (f.p b) = 1` for **every** embedding. |
| `sSup` junk values | `maxUnitDistances n = sSup (unitDistanceCounts n)` in ℕ. `unitDistanceCounts_bddAbove` proves boundedness by C(n+1, 2), which is what `le_csSup` needs. The set is nonempty for every `n` (any n-point set), so `schade` speaks about the true maximum and not ℕ's junk `sSup ∅ = 0`. Nonemptiness is not needed by the proof: `csSup_le'` holds in ℕ either way. |
| ℕ subtraction and division | `schade` states `u(n) ≤ n * u(n - 1) / (n - 2)` for `3 ≤ n`. Under that hypothesis `n - 1` and `n - 2` are true differences. The `/` is ℕ floor division, which matches ⌊n·u(n−1)/(n−2)⌋ as used in P8 (⌊22·57/20⌋ = 62). |
| Vacuity | The six gadget lemmas are non-vacuous: each gadget has an embedding. **This is not proved in the rope.** It rests on the PROOFS.md coordinates in ℚ(√3), which the GR1 reviewer checked numerically, and on Grand Portage's internal exact records `P2-gadget*-embeds`, which outsiders cannot inspect. `rhombus` is non-vacuous (a unit square). `schade` has no hypotheses beyond `3 ≤ n`. `heredity_nonempty` takes a `Copy`, which every subgraph inclusion gives. |

## Definitions budget

The statement vocabulary is 21 non-comment lines (`Defs.lean`), within the 40-line rule. `pt`, `heredity`, `unitGraph` and `unitPairs` are proof-internal and appear in no main statement.

## Review

Self-assessed by the assembling agent. At gate GR1 (2026-10-10) a non-builder agent reviewed it and found all nine statements faithful, with no statement defects. Its documentation notes are addressed above. There has been no human review.
