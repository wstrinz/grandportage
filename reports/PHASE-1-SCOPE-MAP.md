# Initial scope vocabulary and statement boundary — G1 proposal
Primary pin: Mathlib520045ab14e26149ee970e2e617ca04b09bde5d6, Lean4.32.1. This is a finite initial map, not a claim that every corpus string has a complete counterpart. No typeclass lookup alone establishes semantic inclusion.

| Mathematical contract | Proposed binding vocabulary | Necessary qualification |
|---|---|---|
| A08b exact integral identity/common-zero emptiness | Ring R; Nontrivial R for emptiness; ZMod3 instance | Specific proof needs no commutative multiplication. General multivariate polynomial/ideal interpretation may require CommRing or commuting variables. Do not map legacy U mechanically to Ring. |
| A05 rational coefficient reduction | Ring R, Nontrivial R, CharP R2; denominator8 not IsUnit | Bare totalized division in F2 gives0, without representing Q's3/8. Other special evaluations/integral rewrites need independent justification. |
| Field/characteristic scopes | Field K with CharZero K or CharP K p | A named extension, algebra map and denominator constraints remain explicit. Characteristic-changing specialization is not a generic inclusion of worlds. |
| Ordered/SOS reach | Appropriate Ring/Field, order and IsOrderedRing/IsStrictOrderedRing structure | Inspect the actual theorem hypotheses; selected signs/roots and positivity certificates need more than an ORDERED tag. |
| No-zero-divisor/ACF reach | NoZeroDivisors with the actual ring assumptions; Field+IsAlgClosed for relevant ACF results | Nontriviality, commutativity, exact sentence/coefficients and field/model maps matter. ACF transfer gives no automatically computed selected-prime cutoff. |
| GRH or conditional arithmetic | Explicit hypothesis in the bound theorem/checker contract | CAS label/proof mode alone supplies no hypothesis discharge; bind effective configuration and full versus partial certification. |
| Selected point/root, geometric region, graph/counting objective | Statement/model identity, including variables, constraints, root/embedding selection, object family and canonicalization convention | These identify what is claimed; ambient quantified assumptions live in scope. DK253versus138 illustrates an objective mismatch that custody cannot correct. |
| Census/SAT completeness | Exact encoded model and statement, with admitted encoding/coverage premises | No standard mathematical field class supplies completeness. LRAT binds the exact CNF; encoding equivalence and split coverage remain separate obligations. |
| Receipt currentness/version/source custody | Kernel identities and admitted replay contracts | Source digest or ready/proved metadata is not a theorem hypothesis or mathematical authority by itself. |

Evidence: actual Binding.lean A08b/A05 signatures and controls; pinned Mathlib Algebra/Ring/Defs.lean, Algebra/CharP/Defs.lean, Algebra/Order/Ring/Defs.lean and FieldTheory/IsAlgClosed/Basic.lean; prior-art transfer/ACF/certification reviews; INCIDENT-INVENTORY and corpus source-pointed cases.

K2's scope implication is universally quantified and polarity-independent; the Phase1 Lean weakening_sound lemma proves that fact. Object-changing inclusion/image/equivalence need profile K3 contracts. This initial map does not settle every model/embedding/scope representation. Worker paper scoring must identify concrete awkward or unexpressible cases, and the packet's scope/region pivot remains active.
