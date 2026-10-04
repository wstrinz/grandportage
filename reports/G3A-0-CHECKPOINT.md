# G3a-0 checkpoint: pivot rule

Authority: Addendum A, amendment 1. The checkpoint comes after the [reach slice](PHASE-3A-SLICE.md) and the [shadow slice](PHASE-3A-SHADOW.md), and before C1–C4 admission, the binder, `GATE-OWNERS.json` and broad corpus runs. Will decides.

## The three conditions

**1. Every reach-slice claim is a standard-axiom Lean theorem within the A4 budget: holds.**
- All six held claims are proved, with 0.6–5.7 s of proof checking on top of about 19 s of imports, under the 30 s budget.
- All four refusals have Lean counterexamples.
- Caveat: the proofs reuse GP's externally found certificates. The theorem route doesn't avoid search.

**2. Typeclass hypotheses or AutoGeneralization reproduce GP's computed reach: does not hold.**
- **Hand-written `ringChar` hypotheses** reproduce the reach for all six claims, but only because I copied them from GP's computation. Choosing them is the reach computation.
- **AutoGeneralization** reproduces 2 of 4 widenings: A08b, and Fano through `NeZero 2`. It finds nothing for A08c. For X125 it keeps `CharZero`, so it misses every F_p with p ∉ {2, 23}.
- **Phrasing dependence:** its result depends on how the proof is worded, not on the certificate.
- **A05:** Lean elaborates an ill-formed char-2 restatement with a junk value (`3·8⁻¹ = 0`), where GP refuses it.

**3. The A5 tags are only CUSTODY or NONE: does not hold.**
- Four of the six held claims are EARNED: widenings the proposer computed and the case did not request.

## Recommendation: continue, with A4 applied

Two of the three conditions fail, so I recommend continuing rather than taking the Lean-native ledger pivot.

The result still sharpens what GP is for. Theorem warrants are cheap at this size, so under A4 the binder should mint them whenever they fit the budget. On this evidence, GP's distinct value is:
- **reach:** computing the characteristic set a certificate actually supports, and the widenings that follow;
- **well-formedness:** refusing statements whose meaning changes under specialization;
- **custody:** the Kernel fold, still to be exercised in 3a.

That is close to the A5 outcome "a custody and reach layer over a Lean environment". The reach part, though, is not something Lean supplies on its own.

## Limits of this evidence

- The slice is small: one or two variables, and a Fano system whose certificate reduces to 2 = 0.
- AutoGeneralization was tried on one phrasing per claim.
- A proof phrased with `NeZero` instances would likely move X125 to "agrees". It would not move A08c, because `CharP K 3` has no typeclass weakening to "char ≠ 2".
- Larger Nullstellensatz certificates may break the 30 s budget. If 3a continues, the A4 measurement for C1–C3 will show where.

## If continuing, next

1. C1–C3 admission: Mathlib soundness theorems through `HexMvPolyMathlib`, the k ≥ 1 bound, and TCB entries.
2. The binder, with theorem warrants minted under A4.
3. `GATE-OWNERS.json`, then broad corpus runs.
