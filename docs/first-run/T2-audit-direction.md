# T2 audit — lens 2: edge DIRECTION

Independent auditor, barred from `FINDINGS.md` / `BRIEF.md`. Went to the primary
source (`1406.0886_GGV3.tex:1700-1890`) to check containments against the
mathematics rather than the graph's own prose.

**Headline: no edge carrying a live inference has its arrow backwards. One edge
is reversed, its damage is latent, and it will fire at exactly the wrong
moment.**

---

## The finding that matters most

### `GE10` is swapped, and its refusal is load-bearing *because* of that

`GE10: GCHART_G4 → GCHART_G4_LEDGER`, currently `UNTYPED`.

`GCHART_G4_LEDGER` is the γ=4 chart **plus** the per-coefficient cap
`deg_y(C_{−k}) ≤ α(k+1)`. Adding a degree cap shrinks the solution set, so
`V(LEDGER) ⊊ V(GCHART_G4)`: **the ledger is the more constrained model and
belongs at `src`.** Compare the γ=3 analogue, where the cap `(a5)` sits *inside*
`GCHART_G3`. The correct topology is `LEDGER → GCHART_G4`.

That is inert today — `UNTYPED` licenses nothing regardless of orientation. But:

> **`GI-G4-CAP-EXTRAPOLATION`'s refusal rests entirely on `GE10` staying
> `UNTYPED`.** The moment α₄ is derived and someone types `GE10`
> `NECESSARY_CONDITION` — the natural move, and the campaign's own stated
> discharge — the recorded path `[GE10, AGAINST]` becomes
> `PREDICATE/AGAINST/NC = yes`, and **the graph licenses precisely the
> extrapolation it exists to forbid.**

With the orientation corrected the same claim must travel `ALONG`, and
`PREDICATE/ALONG/NC = NO` — the refusal then survives any typing short of
`EQUIVALENCE`.

**Reversing `GE10` converts a type-dependent refusal into a structural one.**
A guard that disarms itself at the moment its obligation is discharged is worse
than no guard, because that is the moment nobody is looking.

---

## The finding that concerns the TOOL

### There is no way to express a case-split edge

`GE7`/`GE8`/`GE9` all run `REDUCED_5_20 → GCHART_G{3,2,4}`. But γ is a
*function of the counterexample* (tex:1719-1723), so a reduced pair has exactly
one γ, and a γ=2 pair does not satisfy (a1)–(a6). **`V(src) ⊆ V(dst)` is false
as a total statement.** Only

    V(REDUCED) ∩ {γ = k}  ⊆  V(GCHART_Gk)

holds. The three edges are mutually exclusive **case branches sharing one
source**, and the type system has no vocabulary for that.

Consequences the auditor traced:

* **`GI-G3-KILL-LIFTS` is sound but its prose overstates it.** It delivers "no
  γ=3 reduced pair", not "`REDUCED_5_20` is empty". A full kill needs all three
  branches plus exhaustiveness of γ ∈ {2,3,4} — which the graph deliberately
  does not have.
* **Two currently-unused cells are unsound as declared**, and one is a single
  step away: pushing `GC-A5-DERIVED` (a `PREDICATE` at `GCHART_G3`) back to
  `REDUCED_5_20` via `NC/AGAINST/PREDICATE` would assert `deg_y(C_{−k}) ≤ k+2`
  for γ=2 pairs, whose cap is `(k+3)/4`. **The graph would license it.**

The fix is a **branch condition on the edge** (`holds_on: γ=k`), not a
reversal — and nothing in the current schema can carry one.

---

## Per-edge verdicts

| edge | verdict | why |
|---|---|---|
| `E-G3_ELIM_NO_A5` | **CORRECT** | deleting `1−w·a` shrinks the ideal and enlarges the variety; exhibited point `a=0` is in dst not src. *"the edge where a swap would have been fatal"* — swapped, the negative control's witness would travel ALONG and appear to refute `GC-G3-KILL` |
| `E-G3_ELIM_KILL` | **CORRECT** | GGV3 eliminates `C₋₃..C₋₇`, so the target lives in the smaller coordinate space and cannot be the domain. Two conservative deviations noted: `src` is the domain rather than literally the constructible image, and `dst` keeps only GGV3's single derived relation — both make `V(dst)` *larger*, which strengthens the `AGAINST`/`EMPTY` step |
| `GE7`, `GE8` | **CORRECT** in direction | the source text is an implication in exactly this direction (tex:1739, 1779); det −2 and −3 put the images in proper sublattices the chart conditions never state. See the case-split flag |
| `GE9` | **CORRECT** | δ=1 makes φ₄ an automorphism, so this is closer to an equivalence — but `GCHART_G4` still omits the cap face, so dst is strictly looser. Typing an equivalence `NECESSARY_CONDITION` is **conservative**; nothing is over-licensed |
| `GE10` | **SWAPPED** (latent) | see above |

## Inference paths

All five recorded paths walk their edges correctly cell-by-cell.
`GI-G3-KILL-LIFTS` (`E-G3_ELIM_KILL` AGAINST, then `GE7` AGAINST) is licensed at
both steps. The refusals of `GI-REPLAY-TRANSFER` / `GI-BRIDGE` /
`GI-WINDOW-CONFLATION` hold regardless of direction, since `UNTYPED` licenses
nothing.

**Only `GI-G4-CAP-EXTRAPOLATION` is fragile**, for the reason above.
