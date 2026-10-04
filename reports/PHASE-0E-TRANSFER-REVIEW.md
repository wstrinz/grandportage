# Phase 0e transfer review — P3 / P4 / P5 / P7

Four provisional reading rows for parent integration. This report neither completes 0e/G0 nor approves a G1 adoption. Only the assigned Markdown and JSON reports were written; no imported source, build, test, prototype, campaign read, contact or shared-file edit occurred.

## Budget and authority

UTC start: **2026-09-30T01:01:09Z**. Primary-source reading endpoint: **2026-09-30T01:10:35Z**. Review/finalization endpoint: **2026-09-30T01:15:01Z**. Actual conservative charge: **15 minutes**, within the 25-minute slice. The charge covers the entire interval, failed fetches and tool latency, plus a 60-second finishing allowance, rounded upward. Prior completed charge remains 26 minutes; after this slice the total is **41/120**. The parent must reconcile this actual charge with its 25-minute reservation; this worker did not change the tracker.

Read the current AGENTS, backbriefs, DECISIONS, revision-3 packet, approved review amendments and completion tracker. Later heartbeat renewal supersedes older cancellation prose, but this assignment changes no scheduling. The operative restrictions remain: replay-only authority, soundness arguments and adversarial controls for every checker, Mathlib outside the kernel, and K2 only narrowing scope. Wider reach requires an admitted sound derivation or evidence admitted at that reach.

## Proposed map

| Row | Provisional proposal | Guarantee piece |
|---|---|---|
| P3 | imitate | No silent overclaims; evidence-backed wider reach only after interpretation and admission. |
| P4 | adopt / imitate / differ (provisional by component) | Sound object-changing carrying; explain missing coverage, predicate preservation and direction. |
| P5 | adopt narrowly (provisional) | Preserve statement meaning when moving cast expressions; refuse unsupported domain widening. |
| P7 | adopt narrowly (provisional) | Earned cross-world consequences within a precisely specified model class; explain insufficient specialization evidence. |

“Adopt” below means a recommendation for future binding-layer reuse, subject to compatibility, meaning and admission checks. It grants no present GP authority.

## P3 — Dedukti / Logipedia: proof dependencies versus semantic reach

The paper studies logical formalisms encoded by declarations and rewrite rules in Dedukti's lambda-Pi calculus modulo theory. It identifies proof fragments that avoid dependent arrow/implication and proof-to-term pi, allowing partial translation from Matita to HOL. This is more than a flat list of mathematical axioms. At the pinned Logipedia implementation, JSON deps are documented as direct item dependencies, not transitive closure. compile.ml excludes encoding modules from those deps and writes theory=[] for declarations, definitions and rewrite-rule items. deps.ml calls Dedukti Api.Dep for item dependencies and offers optional transitive closure for module dependencies. The inspected code does not establish a completed per-proof axiom-support certificate.

**Limits that matter for GP:**

- A dependency graph is syntactic support evidence; it does not prove a GP predicate in every structure satisfying a named scope.
- Dedukti computation/rewrite rules and encoding adequacy must be included in any logical-support interpretation; JSON's filtered deps cannot be treated as a standalone logical dependency closure.
- Export docs require translation into STTfa first; only HOL-to-STTfa is documented as fully automated. Matita translation is described as partial/planned; other logics have no concrete plan in that document.
- Historical exports to Lean are not evidence of compatibility with current Lean 4 or this GP workspace.

**Recommendation.** Imitate proof-specific support accounting, pinned theories and explicit translation restrictions. Differ from converting a displayed theory/axiom list directly into semantic reach. No Dedukti importer or exporter is adopted in this slice.

**Unresolved:**

- Complete axiom/rule dependency accounting and adequacy proofs for a GP-targeted encoding.
- Current end-to-end exporter compatibility, replay contract, licensing for any future copied component and integration cost.

Primary evidence: [src/json/json_types.ml](https://github.com/Deducteam/Logipedia/blob/9da47719a18e3d9995137939e789e7664c71c9e5/src/json/json_types.ml), [src/json/compile.ml](https://github.com/Deducteam/Logipedia/blob/9da47719a18e3d9995137939e789e7664c71c9e5/src/json/compile.ml), [src/core/deps.ml](https://github.com/Deducteam/Logipedia/blob/9da47719a18e3d9995137939e789e7664c71c9e5/src/core/deps.ml), [docs/export/apropos.md](https://github.com/Deducteam/Logipedia/blob/9da47719a18e3d9995137939e789e7664c71c9e5/docs/export/apropos.md), [Logical frameworks; Reverse mathematics; Empirical results](https://arxiv.org/html/2305.00064v1).

## P4 — Trocq; Isabelle Transfer/Lifting; Lean analogue

Trocq uses a product hierarchy of structure on R and its converse: Map0 no data, Map1 a function, Map2a function-graph inclusion in R, Map2b inclusion of R in the function graph, Map3 both, Map4 additional coherence. These are constructive structures, not a trust score or a synonym for two total/surjective flags. Map1_forall uses a related comap for the domain and a forward map for the codomain; stronger displayed function transfer constructions require Funext. The paper distinguishes goal replacement from the implication that justifies it. Isabelle Transfer separates left_total, right_total and bi_total; equality transfer also needs bi_unique. Lifting's Quotient records Abs(Rep a)=a, valid representatives, the domain of the raw relation and its correspondence to abstract equality; Quotient_left_total additionally requires reflexivity of the raw relation.

**Actual Lean analogue.** At the inspected pin, `Mathlib/Logic/Relator.lean` supplies `Relator.LiftFun`, `RightTotal.rel_forall`, `LeftTotal.rel_exists`, `BiTotal.rel_forall` and `BiTotal.rel_exists`. Concrete theorem analogue exists at the pinned Mathlib revision; no compile or GP binding test performed. No current working Lean Trocq port was evidenced by the bounded repo/paper/search inspection. A 2024 primary author excerpt describes an unready partial 2023 transfer prototype; this neither proves a current absence nor establishes a maintained port.

**Direction convention:** R : A -> B -> Prop and forall a b, R a b -> (P a -> Q b); all directions below refer to warranted conclusions, not tactic-goal replacement.

| Warranted conclusion | Needed obligation |
|---|---|
| exists A P -> exists B Q | LeftTotal R plus predicate implication |
| forall A P -> forall B Q | RightTotal R plus predicate implication |
| reverse implications | Converse relation and reversed predicate implication; coverage sides swap |
| forall/exists equivalence | BiTotal R plus predicate iff |

**Limits that matter for GP:**

- A total function's graph is left-total. Surjectivity supplies right-total. Neither supplies predicate preservation automatically.
- For negative existence claims, use a proved reflection direction/contrapositive; do not reverse an existence implication.
- Restriction to Domainp/image is different from a theorem over the entire raw or target domain.
- Trocq README calls the project a Coq-Elpi prototype, supports Rocq/Coq 9.0 and 9.1 and says it is not packaged in Opam/Nix. Its higher structures and any univalence/Funext assumptions cannot be silently transported into Lean.

**Recommendation.** Propose adopting the existing Lean Relator lemmas through the pinned binding layer, imitating Trocq's separate structural obligations and Isabelle's domain restrictions. Differ from making all relation properties universal kernel facts. Keep algebra-profile rules under section 8.4 and D9; no promotion or imported code now.

**Unresolved:**

- Current maintained Lean port, if any; not resolved by this bounded search.
- Which corpus relations require uniqueness, quotient respectfulness, dependent codomain structure or restricted-domain formulations.
- Pinned GP compatibility and elaboration cost remain for separately authorized 0c/G1.

Primary evidence: [std/Hierarchy.v](https://github.com/rocq-community/trocq/blob/a36529e66dfd3d255c51506943dbdac77adbee56/std/Hierarchy.v), [std/Param_forall.v](https://github.com/rocq-community/trocq/blob/a36529e66dfd3d255c51506943dbdac77adbee56/std/Param_forall.v), [src/HOL/Transfer.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/ba26878dc68fce466a51121aa6b0d0c3893084d9/src/HOL/Transfer.thy), [src/HOL/Lifting.thy](https://github.com/isabelle-prover/mirror-isabelle/blob/ba26878dc68fce466a51121aa6b0d0c3893084d9/src/HOL/Lifting.thy), [Mathlib/Logic/Relator.lean](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/Mathlib/Logic/Relator.lean), [README.md](https://github.com/rocq-community/trocq/blob/a36529e66dfd3d255c51506943dbdac77adbee56/README.md), [Sections 2.1, 3.2, Definition 5, Remark 2](https://arxiv.org/html/2310.14022v2), [primary_author_statement_search_excerpt](https://leanprover-community.github.io/archive/stream/217875-Is-there-code-for-X%3F/topic/Equivalences.20preserve.20properties.html).

## P5 — Lean norm_cast: precise cast rules and limits

The inspected Mathlib pin specifies leanprover/lean4:v4.35.0-rc3, resolved to Lean commit 470d5ce1400764999581fd26d5d72b00d990b0f4. Current norm_cast implementation is in Lean core, not the attempted Mathlib/Tactic/NormCast.lean path. Its attribute classifies equality/iff lemmas by coercion occurrence into elim/move/squash; the tactic composes proof-producing simplifications and checks the normalized source and target types for mod_cast. It operates using the registered lemmas and available hypotheses, rather than validating arbitrary ladder transfer.

| Named rule | Exact displayed assumptions | What it provides |
|---|---|---|
| `Nat.cast_mul` | `[NonAssocSemiring alpha]` | cast(m*n) = cast(m)*cast(n) |
| `Nat.cast_inj` | `[AddMonoidWithOne R] [CharZero R]` | (m:R)=(n:R) iff m=n |
| `Int.cast_inj` | `[AddGroupWithOne alpha] [CharZero alpha]` | (m:alpha)=(n:alpha) iff m=n |
| `Rat.cast_inj; cast_add; cast_sub; cast_mul; cast_inv; cast_div` | `[DivisionRing alpha] [CharZero alpha]` | Rational equality reflection and the displayed rational operation-preservation laws |
| `Rat.cast_le; Rat.cast_lt` | `[Field K] [LinearOrder K] [IsStrictOrderedRing K]` | Comparisons between cast rational values iff their comparisons in Q |
| `Nat.cast_sub` | `[AddGroupWithOne R] and h:m<=n` | cast(n-m : N) = cast(n)-cast(m) |

**Limits that matter for GP:**

- Nat subtraction is truncated; its subtraction law has an inequality premise.
- Integer division and natural division are not field division; do not substitute them through casts without the corresponding divisibility/side conditions.
- Equality reflection in finite characteristic is not furnished by the CharZero lemmas.
- Cast inv/div laws use Lean's totalized inverse/division; a GP syntax for partial division would need its own denominator binding/guard.
- Pointwise comparisons or equality of cast source values do not quantify over all elements of a larger codomain. A cast witness may establish existence with all constraints preserved, but nonexistence over Q does not imply nonexistence over R.
- CharZero and CharP R 0 are not interchangeable for arbitrary semirings, as the inspected definition documentation explicitly warns.

**Recommendation.** Propose using norm_cast/mod_cast and individual exact cast lemmas as existing proof tools in the binding layer, with lemma identity, typeclass instances, side conditions and statement mapping retained. Do not call this a generic scope-ladder rule or an admitted GP checker merely because the tactic exists.

**Unresolved:**

- Whether each proposed corpus AST elaboration preserves the theorem's statement and implicit hypotheses.
- Actual GP toolchain compatibility, elaboration costs and theorem-axiom audit; no Lean installation, build or test run.

Primary evidence: [Mathlib/Data/Nat/Cast/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/Mathlib/Data/Nat/Cast/Basic.lean), [Mathlib/Data/Int/Cast/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/Mathlib/Data/Int/Cast/Basic.lean), [Mathlib/Data/Rat/Cast/CharZero.lean](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/Mathlib/Data/Rat/Cast/CharZero.lean), [Mathlib/Data/Rat/Cast/Order.lean](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/Mathlib/Data/Rat/Cast/Order.lean), [lean-toolchain](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/lean-toolchain), [MathlibTest/Tactic/NormCast.lean](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/MathlibTest/Tactic/NormCast.lean), [src/Lean/Elab/Tactic/NormCast.lean](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Lean/Elab/Tactic/NormCast.lean), [src/Lean/Meta/Tactic/NormCast.lean](https://github.com/leanprover/lean4/blob/470d5ce1400764999581fd26d5d72b00d990b0f4/src/Lean/Meta/Tactic/NormCast.lean), [Mathlib/Data/Int/Cast/Lemmas.lean](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/Mathlib/Data/Int/Cast/Lemmas.lean), [Mathlib/Algebra/CharZero/Defs.lean](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/Mathlib/Algebra/CharZero/Defs.lean).

## P7 — Mathlib ACF / Lefschetz: fixed-sentence family transfer

The pinned IsAlgClosed.lean defines FirstOrder.Language.Theory.ACF p over Language.ring. ACF_isComplete requires p prime or p=0. finite_ACF_prime_not_realize_of_ACF_zero_realize takes a ring sentence phi and ACF 0 models phi, and proves finiteness of prime characteristics whose ACF theory does not model phi. Two equivalence theorems identify ACF 0 modeling a fixed sentence with infinitely many prime characteristics modeling it, or with all but finitely many doing so. A concrete algebraically closed field uses Field K, CharP K p, IsAlgClosed K and CompatibleRing K with a ring-language structure (the source recommends compatibleRingOfRing K).

The available names in namespace `FirstOrder.Field` are:

- `ACF_isComplete`: p.Prime or p=0; conclusion: (Theory.ACF p).IsComplete.
- `finite_ACF_prime_not_realize_of_ACF_zero_realize`: phi:Language.ring.Sentence; Theory.ACF 0 models phi; conclusion: Set.Finite {p:Nat.Primes | not Theory.ACF p models phi}.
- `ACF_zero_realize_iff_infinite_ACF_prime_realize`: phi:Language.ring.Sentence; conclusion: Theory.ACF 0 models phi iff Set.Infinite {p:Nat.Primes | Theory.ACF p models phi}.
- `ACF_zero_realize_iff_finite_ACF_prime_not_realize`: phi:Language.ring.Sentence; conclusion: Theory.ACF 0 models phi iff the complement of {p:Nat.Primes | Theory.ACF p models phi} is finite.

**Limits that matter for GP:**

- Quantifies over algebraically closed models, not finite fields F_p themselves, rational fields, ordered fields or arbitrary Lean propositions.
- Sentence has no free parameters. Rational coefficients, chosen roots/embeddings and model constants must be encoded and their meaning/denominator conditions audited, rather than carried as unbound external parameters.
- The finite exceptional set depends on the fixed sentence; this is not one uniform cutoff for every statement.
- The proof uses compactness and Classical.choice. The inspected API gives no computed exceptional-prime list or numerical bound for a selected prime.
- One or finitely many favorable characteristic-p examples do not establish infinitely many theory entailments. No chosen-prime transfer follows merely from calling p large.
- Completeness establishes agreement on ring sentences among models of a fixed ACF theory; it is not agreement for arbitrary formulas with independently chosen parameters.

**Recommendation.** Propose reusing these specific theorems in a pinned model-theory binding for M3 when the profile statement is proved to match the ring sentence and required entailment. For a particular characteristic p, require additional evidence that p is outside an explicit justified exception set (or a separate direct proof). Differ from treating it as a generic large-p certificate specialization rule.

**Unresolved:**

- Corpus-relevant first-order encodings, parameter/denominator handling and an effective bound or exception certificate for concrete-prime use.
- Actual theorem elaboration/axiom auditing, compatibility and timing remain unexecuted future work.

Primary evidence: [Mathlib/ModelTheory/Algebra/Field/IsAlgClosed.lean](https://github.com/leanprover-community/mathlib4/blob/58554a33d40f0f4c33fd0256dfecbc5b706480a3/Mathlib/ModelTheory/Algebra/Field/IsAlgClosed.lean).

## Pins, source handling and verification

| Repository | Inspected revision | Commit UTC |
|---|---|---|
| Logipedia | `9da47719a18e3d9995137939e789e7664c71c9e5` | 2024-11-11T10:38:12Z |
| Trocq | `a36529e66dfd3d255c51506943dbdac77adbee56` | 2026-07-01T00:19:43Z |
| Mathlib | `58554a33d40f0f4c33fd0256dfecbc5b706480a3` | 2026-09-29T23:49:11Z |
| Isabelle_mirror | `ba26878dc68fce466a51121aa6b0d0c3893084d9` | 2026-09-28T13:56:27Z |
| Lean_toolchain | `470d5ce1400764999581fd26d5d72b00d990b0f4` (v4.35.0-rc3) | 2026-09-24T17:35:24Z |

Isabelle is a development mirror pin, not a tested release. Mathlib and its Lean toolchain are research pins, not validated GP dependencies. Mathlib/Lean source headers identify Apache-2.0; inspected Trocq files identify LGPL-3.0. No code was copied or adopted. A future Logipedia code reuse still needs a license check.

27 primary source/metadata entries are indexed in the JSON, with versioned source URLs. The detailed conclusions come from static source text. No source files were downloaded into the workspace; HTTP text was read in memory. Source existence and written proof code are distinguished from successful execution: no Lean/Rocq/Isabelle/GP tests were run.

Failed guessed source paths included the old Mathlib norm_cast path, Nat/Int Cast/CharZero paths, a Logipedia deps path and exporter.mli. The stale output following exporter.mli failure is excluded. Local guessed tracker/review filenames were corrected to the actual files. Some web cache/author PDF/full-page requests failed; recovered primary source text or a clearly dated author search excerpt was used where available. These failures and their latency are charged, and do not establish project absence. The JSON retains the failure details.

## Parent integration boundary

- Replace the broad P3 axiom-label assertion with proof-fragment/encoding analysis plus actual direct-dependency implementation limits.
- P4 has an existing Mathlib Relator analogue; current maintained Trocq port remains unknown, not absent.
- P5 adoption is for theorem-backed cast simplification, not domain widening.
- P7 exists with exact first-order ACF restrictions and no numerical cutoff in the inspected API.
- Reconcile actual charge into the shared tracker; this worker does not modify it.

These four rows establish partial evidence on existing transfer mechanisms. They make no novelty, consumer-demand or complete territory claim. The other 0e rows, three G1 decisions and all Phase 0 prerequisites retain their existing status. Future costs and compatibility experiments belong to separately authorized 0c; no such experiment was performed here.
