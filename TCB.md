# Phase 0c trust observations
This is a feasibility record, not checker admission or a Phase1 kernel contract.

## Installed toolchain
Lean4.32.1, commit f054605aea4b840552cca2e725580bffd1e1b704. Existing C: binaries are read-only. New packages, dependency checkouts, cache downloads, generated artifacts and fixtures live on F:. Executable/library/compiler integrity is assumed when interpreting native runs. Exact file digests are recorded in the spike reports.

## Mathlib-free toy
Spike.lean models natural-number equality and finite named context sets. Its checker compares the actual two naturals; declarations alone cannot hold a claim. Receipts bind claim ID, both operands, exact requested scope, model key/digest and checker digest. Current source registrations override prior registrations. Narrowing requires a held parent and subset contexts; stale parents cannot support children. The bounded recursive lookup rejects cycles by exhaustion.
Source digests are opaque strings in Lean. The Python validation driver hashes actual fixture/case/source bytes; the spike does not implement cryptographic hashing, authenticated source registration, a general statement AST, complete provenance or all K1-K6.
checked_equality proves equality from the actual checked Boolean definition. Its axiom audit is propext only. This is not a proof of the complete custody fold.
Array scans and bounded recursion are toy implementations. Empty scopes are permitted; extra JSON fields are ignored. Resource caps, duplicate JSON-key policy, normalized scope identity, retraction and independent-warrant survival are not settled here.

## Exact univariate rational replay
Spike.Poly uses Lean Rat, finite sparse exponent/coefficient lists, explicit cofactor-count equality and exact coefficient comparison up to the maximum degree in the computed products/target. Duplicate exponent terms are summed; zero denominators and negative/non-natural exponents are refused.
The exact cofactor test is executed, but no theorem relating this implementation to Mathlib Polynomial has been proved. It is not an admitted unit-ideal checker. No multivariate encoding, arbitrary CAS export parser or resource bound is supplied.

## External process
CheckerMain calls the private fraction_checker.py through IO.Process.output with the exact input string on stdin. Acceptance requires exit0, valid=true, exact echoed request bytes (after JSON string decoding), and checker label fraction-cofactor-v1. Hostile output binding/version controls were exercised.
Python/Fraction, its interpreter, script contents, process transport and invocation path are additional TCB for this route. Validation pins script and executable hashes; the Lean wrapper itself does not enforce a pre-execution SHA-256 check or prevent TOCTOU. Echoing input binds a response; it does not establish checker honesty.
Production would need checker admission, executable/version integrity, soundness, resource handling and cryptographic source binding. None is inferred from this successful process experiment.

## Installed LRAT
Std.Tactic.BVDecide.LRAT.check_sound proves successful checking implies UNSAT of its typed CNF. Axiom audit: propext, Classical.choice, Quot.sound.
The spike uses exact typed contradictory unit clauses [(0,true)],[(0,false)] and a parsed text certificate '3 0 1 2 0'. The installed conversion increments zero-based variables to DIMACS numbering and prepends the clause-index sentinel; this mapping was inspected.
Runtime positive, satisfiable-CNF, invalid-hint and malformed-text controls are included. A shortened hint list was genuinely valid for this example; it is not counted as a refusal.
Plain decide, decide +kernel and bounded full-definition import attempts did not reduce the checker at this pin. The preserved failed experiment is reproduction data, not an admitted theorem or a global impossibility result.
The successful native_decide theorem adds nativeCheck._native.native_decide.ax_1_1. Native UNSAT therefore depends on compiler/runtime plus that generated Boolean-result axiom. Module rechecking accepts declared axioms; it does not discharge this axiom.
This is a usable native LRAT evaluation candidate with explicit trust, not an axiom-free LRAT replay claim. Arbitrary DIMACS ingestion, census-to-CNF encoding correctness/completeness, DRAT conversion, large-certificate performance and independent checker admission remain outside this miniature spike.

## Mathlib binding
The separate pinned package formalizes actual GP-A08b/GP-A05 obligations. Its own report records exact Mathlib/dependency pins, theorem hypotheses, positive contrasts, axioms and timings. New module kernel replay does not recheck every imported Mathlib declaration. Cached dependencies are distinguished from a clean dependency build.
Neither a theorem pointer nor matching typeclass names implement GP's statement/input/hypothesis/scope binding. G1 must decide and specify that layer.

## Corpus preservation and performance interpretation
The 459-case-sized load test binds case IDs/digests to deliberately trivial equalities. It measures serialization/fold plumbing, not the mathematical cases or harvested exports. Full oracle replay is unchanged. Unsupported routes/formats remain unsupported.

## Phase 2 native receipt path — 2026-09-30

The Mathlib-free test stub decodes actual univariate rational generators, targets and cofactors, then recomputes coefficient identities. Lean proves receipt acceptance yields the uniquely registered clause’s formal polynomial-span meaning with exact claim/version/binding equality. The receipt-only fold-to-formal-span composition is proved: held claims have registered true formal-span clauses, and warrant-ID uniqueness follows from actual resolution. Generic runtime truth still uses explicit validator and projection contracts; whole-profile scope/rule semantics remain open.

The host adapter must faithfully translate the original fixture contract, select identities, hash the configured data, invoke the pinned compiled executable and interpret its output. Digest strings are compared inside Lean; Lean does not establish their relationship to original bytes or intended meaning. Native execution relies on the Lean compiler/runtime, rational implementation, operating system and executable/input integrity. Independent leanchecker replay checks proof declarations, not those host assumptions.

Raw registry/events reject duplicate keys, malformed fields/types and unknown constructors. Theorem pointers, proof/rule/narrow capabilities are refused in the receipt-only registry. No geometric interpretation, general profile adoption or native LRAT admission is supplied by this formal span stub. Earlier Phase 0 observations above retain their historical scope.

## Phase 2 scoped runner

ScopedSpan derives both replay clauses and semantic clauses from the same decoded rows. Its concrete fold-to-registered-meaning theorem discharges receipt truth through exact Rat replay and narrowing through the actual statement/inclusion checks. Scope IDs denote finite named test contexts; Holds is the formal polynomial-span predicate, independent of context. They do not encode fields or geometric regions. Selected object labels are part of statement equality. Host byte/digest fidelity and intended interpretation remain adapter contracts.

ScopedRunner uses the same admission for held and why-not. Caller claimed keys, obligation links and open IDs affect earned reporting only. Proof and general rule capabilities refuse; conflict detection is not implemented in this stub. The receipt-only runner retains its earlier capability boundary.

## Phase 2 checked cover path

Registry schema 3 adds cover rule names, destinations and ordered premise-claim lists. Actual finite context coverage is recomputed; no caller success flag supplies coverage or branch truth. Runtime resolves exact premise-warrant IDs and proves those premise records belong to the snapshot. The combined receipt/cover/narrowing fold-to-registered-meaning theorem discharges these admission contracts and derives ID uniqueness. This remains the formal Rat/named-context stub; conflict/release handling and faithful translations of conditional geometric fixtures are separate work. Schema 2 continues to refuse general rules.


## Phase 2 release review

Generic Conflict uses the profile's sound contradiction test and an Overlap checker that returns an actual shared context with a proved membership contract. Review pairs supported, exactly bound warrants and preserves the complete runtime state. A confirmed conflict excludes joint semantic truth; unknown overlap does not freeze release. ScopedRunner invokes this review separately from held/why-not/earned. The positive-only rational stub declares no contradictory pairs, so its production findings are empty. Test-only compromised admission exercises the alarm; it is not an admitted checker or a real corpus conflict pass. Full provenance adapters retain mismatches and complete current/stale records; native replay, rather than historical backend descriptors, supplies identity authority.


## Approved conditional fixture harness

A16 uses a separate test-only interpreter with arbitrary parent and branch predicates over every point type. Its explicit theory hypotheses are the supplied branch-emptiness and exhaustive-cover premises. Exact bound assumption warrants are sound within that theory; the checked two-premise rule proves parent emptiness. Lean proves the actual validator and arbitrary-event fold sound, including warrant-ID uniqueness from resolution. Host SHA-256 binds unchanged source bytes to input/scope identity. Native decoding rejects unknown input fields and wrong types. Expected verdict metadata supplies no authority. Conditional corpus passes establish the stated inference under its named premises, without certifying those premises' algebraic truth or adopting a production profile.

Named partition fixtures X183/X184/X186 use the same conditional boundary with explicit parent/left/right predicates. Coverage is a separate assumption warrant, and the actual composition rule requires its exact ID and full record in the dependency list. Missing branch premises produce no records. Held coverage omitted from the argument does not authorize parent emptiness. Actual validator/fold soundness is proved over arbitrary events and interpretations satisfying the named assumptions; no production profile is adopted.

Conditional route fixtures X177/X178 preserve two fixed predicate identities while the existing acceptsNarrow checker restricts loose/side scopes to tight under explicit inclusion hypotheses. The exact join additionally requires both literal routes to be licensed. Its conclusion includes licensing globally, so empty regions cannot erase an absent route. Native execution instantiates Point with Unit; admission_point_independent and native_fold_held_sound transfer the exact executable fold to arbitrary point types. This remains test-only conditional interpretation, with host byte/digest fidelity and no production profile adoption.

Conditional point-route fixtures X179/X180 retain a named exhibited SIDE witness. Its SIDE and TIGHT membership are distinct global statements; K2 cannot change that selected model identity. The supplied universal predicate genuinely narrows through acceptsNarrow. Lean proves the actual validator/fold sound over arbitrary point types under explicit universal truth, SIDE membership and inclusion hypotheses, plus a countermodel with empty TIGHT. Separate accepting controls add TIGHT membership for that same witness, with an inhabited interpretation; they do not validate lifting from inclusion alone. Execution uses the pinned Lean runtime. Direct compilation and independent kernel checking are bound to local dependency, harness and toolchain hashes. This remains conditional test-only interpretation; no underlying algebraic certification or production profile is admitted.

Recorded-use coverage fixtures X193–X198 check finite inventory containment in Lean: construction and conclusion indices are combined separately for each asserted dimension. General checker/missing-set theorems and actual validator/fold soundness prove that held coverage covers those recorded labels. Complete literal serialization and host SHA-256 bind receipts and the two-premise join; expected verdict metadata supplies no authority. Empty recorded uses make this structural obligation vacuous, without establishing discovery of all real uses or sufficiency of represented components. Labels remain exact; infinity and inf are distinct. This is a test-only finite structural contract, with the pinned Lean runtime and independently checked compiled declarations, not mathematical profile adoption.

Conditional admission fixtures A27 (six variants) bind named synthetic admitted-check and successful-check hypotheses for one fixed field and candidate object. Lean proves the actual validator/fold sound under those explicit hypotheses: held targets are the exact full claim, unconditional or restricted to a GRH context, never global truth. GRH_cannot_be_dropped and quotient_does_not_imply_full keep narrowing directional. Heuristic and producer-label variants supply no authority. Complete literal serialization and host SHA-256 bind the claim digest, scope and contract versions; expected verdicts supply no authority. No class-group arithmetic, real checker admission or profile adoption is certified, and frozen oracle observations remain UNSUPPORTED. Compilation and independent kernel checking are bound to the normalized harness, with only standard axioms.

Conditional theorem-transport fixtures X60–X62 bind the pinned authority JC.AUTH.ACTUAL_BLOCK_ONE and consumer edge JC.EDGE.SLICE_TO_BLOCK_ONE_ZERO. Both denote only the conditional statement that their premise statements imply their source-to-target reach; the named theorem is an explicit semantic hypothesis and no premise is discharged. licensed requires exact equality of endpoints and premise records, including status; licensed_sound and transport_sound carry the authority meaning to the edge, and actual validator/fold soundness holds over arbitrary interpretations. Countermodels show an omitted premise or rebound target is not a consequence, and holding the conditional never establishes its target. Complete literal serialization, host SHA-256 and the pinned history ledger bind every statement. No theorem replay or profile adoption is claimed.

Section provenance fixtures X173–X176 bind the pinned v0.37 _section_representation certificate, extracted by AST and embedded verbatim. A held section claim means its stored certificate is valid. Admission requires verify.elimination_section, VERIFIED_SECTION and a stored object byte-identical to the checked one, so bound_section_sound transfers only the named successful check; mutated_certificate_not_covered and missing_object_has_no_meaning show the binding is load-bearing. A rejection of another proposal is a separate claim that neither supplies nor retracts the section; only an explicit targeted retraction removes support. No substitution or cofactor arithmetic is replayed; replacement certificates need separate profile validation.

Context-reach fixtures A01, A08a, X283 and X14 decode four schemas into one contract: an emptiness or nonemptiness fact at a named context. A named source warrant supplies only its own context; the only licensed transport is identity, and identity_transport_sound carries it. context_change_not_transported gives countermodels for base extension to a field family, characteristic specialization, untyped point-universe change and unanchored combinatorial certificates. A separately supplied direct target warrant is its own named hypothesis, and a recorded unanswered step means only that it was recorded (debt_record_not_transport). No field arithmetic, reduction modulo p or point-universe theory is certified.

Open-premise guard fixtures X399, X402 and X403 pass the pinned frozen inference frame to Lean, bound by its manifest LF SHA-256, and check the fixture's stated premises against the selected inference's filled slots. Supplied claims and the inference step are named hypotheses; family-level and model-level facts are distinct predicates. licensed_slots proves that an admitted inference has every slot filled by a model-level claim, so licensed_conclusion_sound applies. open_slot_blocks and family_fact_is_not_model_fact give countermodels for open E5 slots and unbridged family premises. Filled-slot contrasts accept only at their supplied authority. No census completeness or family mathematics is certified.

Unreplayed-evidence fixtures X229 and X65 separate evidence from labels. X229 uses the existing native Span admission: held identities mean formal univariate span membership by fold_held_formalSpan, and unregistered_name_refused shows readable historical execution metadata can never be admitted as a receipt. A small native univariate parser decodes the fixture strings; the host mirror parses independently. X65 binds a named checked verdict to the exact canonical stratum data; name_alone_no_meaning and stale_verdict_not_current give countermodels for a bare certificate name and for mutated generators or guards. The multivariate localized certificate itself is not replayed.

Rule-shape fixtures A14, X04 and X09 decode into supplied atoms, registered one-step rules and a goal. closure_sound proves every atom in the native forward closure holds in any interpretation satisfying the supplied atoms and rules; closed_set_countermodel proves a closed set containing the supplied atoms but not the goal yields an interpretation where all of them hold and the goal fails. Execution reports the closure and checks it is closed. Inclusion edges, the checked exhaustive partition and kind-preserving transport are the only registered rules, plus any explicitly supplied kind-changing rule. No geometric content is certified.

Lifecycle-concern fixtures X149–X163 decode lifecycle-scenario/v1 natively into inert custody events under refuseAll, so nothing is held. Withdrawals retract, replacements supersede, and concerns are evaluated over production custody liveness; routeCleared_sound, untypedCleared_sound, contextCleared_sound and liveRelation_sound reflect each check into its structural statement. annotation_only replacements are admitted only when the computed classification over the pinned v0.37 identifying and licensing field tables is AMEND (amend_sound); the host checks the native tables against the pinned kernel and the lifecycle vocabulary map.

Lifecycle properties are proved over the actual support graph in Tests/LifecycleProperties.lean. retract_reachable_iff shows that after retracting a warrant, an id stays reachable exactly when it has a derivation avoiding that warrant; requirements_not_live ties this to runtime liveness. attempt_requirements and extra_nodes_keep_support show failed or timed-out attempts never revoke support, and no_bootstrap shows circular support without a requirement-free node supports nothing. fold_total, together with a source audit rejecting partial, unsafe, opaque, implemented_by, extern, sorry and native_decide in the kernel, gives totality and determinism.

## Phase 2.5 pins and libraries — 2026-10-02

Every package uses Lean `v4.34.0-rc2`, a release candidate adopted for Hex v0.6.0 (Addendum A2); compiler, runtime and kernel integrity at that toolchain are assumed. `KERNEL-PIN.json` binds the 22 Kernel files and the toolchain. `tools/check-kernel-axioms.py` replays each Kernel module with `leanchecker` and audits every Kernel constant's axioms.

| GP guarantee | Rests on |
|---|---|
| Fold, custody, narrowing, cover and conflict soundness (Kernel) | Lean `v4.34.0-rc2` only; no Mathlib, no Hex |
| Executable profile arithmetic: 3a reach-slice checkers (not yet admitted) | `HexMvPoly`, `HexPoly`, `HexBasic` at v0.6.0; F_p as rational replay with mod-p residuals (A3 deviation, no native externs); Lean `Rat` |
| Field contexts and characteristic scopes (binding spike) | Mathlib `85e3a25e`: `ModelTheory/Bundled`, `ModelTheory/Algebra/Field/Basic`, `Algebra/CharP` |

The §3.6a shadow theorems (`binding/GPBinding/Shadow`) rest on Mathlib `85e3a25e` only; AutoGeneralization `07ed6f9` is used as an untrusted proposer of weaker assumptions, and its outputs are re-elaborated, not trusted. No GP claim yet depends on a Hex theorem. When 3a admits one, it is listed here by exact declaration, not by library status (A6).

## Phase 3a checker admission (C1–C3) — 2026-10-02

`binding/GPBinding/Admission` proves, on standard axioms and replayed by `leanchecker`, that the executable checkers are sound. `check_sound` shows that an accepted receipt check gives the statement in every field `K` with `ringChar K` in the requested scope, where rational coefficients mean their `Rat.cast`. `fold_held_meaning` shows that every claim the Kernel fold holds under `GPProfile.admission` has that meaning (contexts are `FieldCtx`).

3a.1 additions, under the same proofs:
- the `proper` base checker (`reach_proper_sound`);
- COVER split trees (`tree_locus`);
- the bridge rule and R4 by cover;
- R2/R3 for IN_IDEAL and NOT_IN_IDEAL(1).

A context's truth is truth in every field of its characteristic (`means_iff`), so `Means` is unchanged. `contra` for EMPTY vs NOT_IN_IDEAL uses Mathlib's Nullstellensatz (`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`) over `AlgebraicClosure`.

| Guarantee | Rests on |
|---|---|
| Replay arithmetic agrees with Mathlib `MvPolynomial` | `HexMvPolyMathlib` v0.6.0 `toMvPolynomial`, `coeff_toMvPolynomial`, `aeval_apply` (theorems, re-checked) |
| Prime factors are complete | `isPrime_iff`, `mem_primeFactors` (trial division certified at runtime, exhaustive fallback) |
| The proofs describe the executable that runs | Lean compiler and runtime, including GMP-backed `Rat`/`Int` |

Overlapping tool (§1.7): Mathlib's `linear_combination` checks the same identities but computes no reach. The §3.6a shadow slice measured it at 19–25 s per claim. The frontend's infix parser stays untrusted and echoes the canonical form.

## Phase 3a binder and theorem warrants — 2026-10-03

Theorem warrants (A4) are generated for held claims of supported shapes (`tools/gen-warrants.py`: C1 emptiness over Q with integer statement coefficients). Each states `Warranted stmt scope`: the explicit statement holds in every field of the scope. `means_of_warranted` proves, on standard axioms, that this gives the Kernel's `Means` for well-formed statements; it uses `meaning_eq_elabQ`, which relates the Hex meaning to the explicit monomial sum. No Hex code is evaluated in the kernel.

The binder (`binding/GPBinding/Binder/Export.lean`) checks each registry theorem's axioms and the statement's arity and avoided primes, and writes records keyed on the exact canonical statement and scope. The profile's proof validator accepts a theorem warrant only against such a record. Trusted: the binder's export, run in the binding environment, faithfully reporting the registry it was compiled against. This is the theorem-warrant counterpart of the receipt path's trust in the compiled checker.

3a.1 (G3a review §5). The binder holes are closed:
- **(a)** axioms are collected on the `registry` value itself, whose term contains every entry's proof, and each entry's proof must be literally the named theorem;
- **(b)** identities are canonical JSON (`GPProfile.Canonical`), not `repr`;
- **(c)** the receipt (schema `gp-binder/v2`) carries an environment block: toolchain, Mathlib pin, binding commit, and the FNV-1a of `Warrants/Generated.lean`. The runtime drops every record from a different environment and reports `binder_refused`.

In the binding, `fold_held_meaning_rules` takes the binder's guarantee as the explicit hypothesis `RecordsSound`. Warrants are generated at the receipt's widest computed reach.
