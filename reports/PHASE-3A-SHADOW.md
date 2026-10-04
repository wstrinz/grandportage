# Phase 3a shadow slice

Authority: Addendum A §3.6a. Receipt: [PHASE-3A-SHADOW.json](PHASE-3A-SHADOW.json). Theorems are generated from the reach-slice fixtures into `binding/GPBinding/Shadow/`.

## Restated claims

Each held slice claim is a Mathlib theorem, with scope expressed as a `ringChar` hypothesis:

| Claim | Statement | Proof |
|---|---|---|
| A08b | EMPTY in every field | `linear_combination` |
| A08c | NONEMPTY in every field of char ≠ 2 | witness 2⁻¹ |
| X125 | EMPTY in chars ∉ {2, 23} | `linear_combination` with denominators cleared (46 = 0) |
| X15 | the char-2 identity | `add_pow_char` |
| Fano C1 | EMPTY in chars ≠ 2 | `linear_combination`, giving 2 = 0 |
| Fano F₂ | NONEMPTY over `ZMod 2`, with all 21 guards | `decide` |

The refusals become counterexamples:
- **X126:** the point (13, 0) over `ZMod 23`.
- **A04:** x = 1 over `ZMod 3`.
- **A05:** `3·8⁻¹ = 0` in `ZMod 2`. Lean elaborates the char-2 "reduction" with this junk value; GP refuses it as ill-formed.

All ten theorems use only standard axioms.

## Cost (A4)

| Route | Per claim | Notes |
|---|---|---|
| Receipt | under 5 ms | |
| Theorem | 19–25 s | 0.6–5.7 s of proofs plus about 19 s of imports; all within 30 s |

Effort: about 1.5 h for the theorem route, 3 h for the receipt route including its infrastructure. The theorem route reused GP's sympy certificates, so search cost is shared.

## Widening: AutoGeneralization vs. the proposer

AutoGeneralization (`07ed6f9`) built unchanged at our pins. Four `#autogeneralize!` runs took 25 s, each on a claim stated at its requested scope:

| Claim | AutoGeneralization | Proposer (reach) | Same? |
|---|---|---|---|
| A08b `[CharP K 3]` | removed, so every field | every field | yes |
| A08c `[CharP K 3]` | none | char 0, all primes ≠ 2 | no |
| X125 `[CharZero K]` | `Field` → `CommRing`; `CharZero` kept | all chars ∉ {2, 23} | no |
| Fano C1 `[CharZero K]` | → `[NeZero 2]`, `CommRing` | all chars ≠ 2 | yes |

M1 asks whether these describe the same lattice. They don't:
- **AutoGeneralization** moves along the typeclass hierarchy, and its result depends on how the proof is phrased. Fano used `two_ne_zero`, which needs only `NeZero 2`. X125 used `norm_num` on 46 ≠ 0, which needs `CharZero`.
- **The proposer** moves along characteristic sets, computed from the certificate alone.

They coincide only when the proof uses characteristic solely through `NeZero n`. The restated theorems' `ringChar` hypotheses were transcribed from GP's reach: Lean checked them but did not find them.

## Convergence (A5)

- **(a)** 6 of 6 held claims are standard-axiom theorems within budget.
- **(b)** EARNED: A08b, A08c, X125, Fano C1. NONE: X15, Fano F₂. These single-claim cases exercise no custody.
- **(c)** Theorem cost is no obstacle at this size. GP's remaining value is reach: computing widenings that proof-directed generalization misses, and refusing ill-formed restatements that Lean elaborates silently.
