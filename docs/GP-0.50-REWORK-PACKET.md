# Grand Portage 0.50 — rework packet: claim / scope / warrant

**Packet date:** 2026-09-27 · **Owner:** Will · **Audience:** local builder agent(s) and math-lane research agents
**Status:** ready to start Phase 0.

**Naming.** The project stays **Grand Portage**. This packet calls the rework **GP 0.50** and the frozen predecessor **GP v0.37**. The label is deliberately pre-1.0. It is 0.50 rather than 0.5 because semver compares minor versions numerically, so 0.5.0 would sort *before* 0.37.0. Sub-components (kernel, profiles, a future pooled platform) are deliberately unnamed for now. Do not invent names for them; use plain descriptive terms.

---

## 0. How to use this packet

Read it all before doing anything. Then write `BACKBRIEF.md` (one page at most) that covers:

- the goal, in your own words;
- the DECIDED items;
- your plan for Phase 0;
- anything unclear or that you think is wrong.

**Stop there until Will approves it.** The back-brief doubles as a reader test of this packet.

Every item in this packet is tagged:

- **DECIDED**: do not change without asking Will.
- **WORKING**: the current best hypothesis. Build on it, but log evidence against it and be ready to pivot.
- **OPEN**: resolve it against the corpus and report back. Don't guess silently.

**Stop and ask Will** whenever any of the following happens:

- you want to change a DECIDED item;
- the kernel wants to exceed its budget (§8);
- a gate fails;
- anything would touch a public repo;
- you find yourself building something on the not-list (§9);
- you are more than a day into plumbing without progress on the phase deliverable.

**Inputs Will supplies before Phase 0b starts:** a filled-in `SWEEP-SOURCES.md` (template in Appendix H) with local paths and access notes for every repo in the sweep.

---

## 1. Why this exists

Grand Portage (GP) v0.37.0 has a sound, small, mostly classical transport kernel. It sits inside roughly 64k lines of Python, 43 CLI subcommands, 35 checker rules and about 75k words of documentation. The domain is narrow (exact affine algebra over fields), and the core concepts were never named at the user level. Its vocabulary grew out of Jacobian-conjecture (JC) campaign incidents.

The campaign record since JC points in a consistent direction:

- **DK** (the (23₄) campaign) succeeded without needing GP. What mattered there was census completeness, replayed exclusions, exact witnesses, a Lean proof and independent replication.
- **Pigeon River** (the Andrews–Curtis challenge) had its certificates checked by an external verifier.
- **Cloquet** built its own receipt contract rather than extending GP.

Every campaign reinvented a local custody layer. That custody layer is the real core. The transport table is one domain's rulebook sitting on top of it.

This is a **full rework**, not an incremental refactor. GP has no users to protect. GP v0.37 is frozen and serves as:

1. an **oracle**, for differential testing;
2. a **fixture source**;
3. a **counterexample library**.

We port knowledge, not code.

---

## 2. North star

> **"Elm for vibe maths."** Stating and running a recreational or open-problem math campaign with LLM agents should be low-error to the point of being fun: constrained but not cramped.

**The one-line job.** The system says what you are entitled to believe right now, and what it would take to be entitled to more.

**Fixed ropes.** An admitted move plus its checker is a fixed rope: something an amateur or an agent can clip into and trust. The per-profile move library is the rope network, and each campaign that leaves behind a newly admitted move extends it.

**Distant stretch.** Pooled campaigns work like an autobattler. Players compose moves against a shared referee (the kernel), the ledger is the replay, and tailings are published with explicit scope. Design so this stays possible, but do not build for it now.

**What it is not:**

- a proof assistant (Lean is);
- a CAS;
- a search engine;
- a publication pipeline;
- a confidence calculus.

---

## 3. Decisions

| # | Decision | Tag |
|---|---|---|
| D1 | The core concept is **claim / scope / warrant**, mechanized. We accept narrower applicability in exchange for being knowable and workable. | DECIDED |
| D2 | **Full rework**, under the Grand Portage name, developed in a fresh private working repo through G4. GP v0.37 is frozen as oracle, fixture source and counterexample library. Knowledge is ported, not code. How GP 0.50 lands publicly (replacing the public repo's main line after a frozen tag, or a new repo) is Will's call at G5. | DECIDED |
| D3 | The **kernel is written in Lean 4**: executable, Mathlib-free, with soundness proved about the actual code. Pivot condition in §6 Phase 0c. | DECIDED (with pivot) |
| D4 | Layering: **kernel → profiles → moves and checkers → adapters → surfaces**. Boundary test and promotion rule in §4.4. | DECIDED |
| D5 | Shape: a **Datalog-shaped kernel** (facts and rules folded to a fixpoint over an append-only log). An **Elm-shaped runtime** handles the agent loop and views. A small declarative **campaign statement** is the user-facing surface. | DECIDED |
| D6 | **LCF discipline**: only admitted checkers and admitted rules mint warrants. Declarations, prose, citations and assertions are visible but never *held*. | DECIDED |
| D7 | A **must-refuse / must-accept corpus is built first**. Nothing in the new kernel is written before that corpus exists. | DECIDED |
| D8 | **Kernel budget**, split: core logic (types, fold, `held`, K1–K6, why-not query) ≤ ~500 lines; log serialization and decoding (also trusted) ≤ ~400 lines; the soundness statement plus the definitions it depends on ≤ ~80 lines; proofs uncapped. **Tripwire:** crossing 1.5× any line means stop and report; there is no quiet growth. Each admitted checker ≤ ~300 lines, or a written justification. (Calibration: HOL Light's LCF kernel is roughly 500 lines of OCaml.) | DECIDED (numbers adjustable by Will) |
| D9 | **Promotion rule**: a concept enters the kernel only after two profiles independently need it. | DECIDED |
| D10 | Profile order: a **minimal algebraic profile first** (it has the oracle), then a **census profile immediately after** (the portability test). | DECIDED |
| D11 | **Log discipline**: strictly append-only. Retraction and supersession are new facts. Merge is concatenation followed by a re-fold. | DECIDED |
| D12 | **Formula languages**: no general-purpose language invented. Each profile has a small, specified statement AST with a Lean elaboration target, and Lean is the gold standard for goal meaning. | WORKING |
| D13 | **Scope is context; region is statement** (see §5.1). | WORKING — the most likely pivot point |

---

## 4. Core concepts

### 4.1 Claim / scope / warrant

A **claim** has three parts:

- **statement**: what is claimed, as a profile AST.
- **scope**: the class of *contexts* across which it is claimed. Examples: every field of characteristic 0; ordered fields; ℝ with a selected embedding; "assuming census completeness receipt R"; "assuming GRH".
- **warrant**: what backs it. One of:
  - `Checked(checker, receipt, inputs)`
  - `Derived(rule, premises)`
  - `Cited(ref)`
  - `Asserted`
  - `Absent(reason)`, which covers timeouts and unfinished runs.

The meaning of a claim is: **for every context c in ⟦scope⟧, the statement holds in c.**

The vocabulary comes from Toulmin (1958), where claim and warrant are his terms and his "qualifier" is our scope. The mechanization comes from LCF-style kernels, proof-carrying code, provenance semirings and build systems. See Appendix G.

### 4.2 Held

A claim is **held** when its warrant is `Checked` or `Derived`, every input hash is current, and the warrant's reach covers the claim's scope.

A claim that is not held is either:

- an **obligation** (the warrant is missing or insufficient), or
- **history** (the warrant was stale or superseded).

Only held claims can be premises of held claims.

### 4.3 Kernel rules (WORKING, the complete list)

- **K1 — Receipt.** An admitted checker validates a receipt for `(φ, S)`, the receipt's reach ⊒ S, and its inputs are fresh ⇒ `(φ, S)` is held.
- **K2 — Weakening.** `(φ, S)` is held and S′ ⊑ S (S′ is narrower) ⇒ `(φ, S′)` is held. This is always sound, because scope is a class of contexts quantified universally. See §5.1 for why this matters.
- **K3 — Admitted derivation.** An admitted rule r, with all premises held at S and r's side-checker validating ⇒ the conclusion is held at S. Case splits and covers ("the branches exhaust the region; each branch is empty ⇒ the region is empty"), statement transports (inclusion, image, equivalence) and conjunction are all instances of K3, with the relevant certificate supplied by a profile checker. There is **no separate cover rule** in the kernel.
- **K4 — Freshness.** A warrant binds its input hashes: statement, scope, model data, and checker id and version. Any mismatch means the claim is not held, while its history is retained.
- **K5 — No minting from `Cited`, `Asserted` or `Absent`.** Ever.
- **K6 — Log.** The log is append-only and the fold is deterministic and total. Retraction is a fact.
- **Finding (not a rule).** If `(φ, S)` and a profile-declared contradiction of φ are both held at overlapping scopes, the kernel reports an **inconsistency** and halts promotion. The usual cause is an unsound checker or wrong inputs.

Everything else lives outside the kernel: frontiers, obligations lists, explanations and tailings are derived surfaces.

### 4.4 Layers and the boundary test

| Layer | Contains | Trust | Change rate |
|---|---|---|---|
| **Kernel** (Lean) | claim/scope/warrant types, `held`, K1–K6, the fold, the soundness theorem | the only global TCB | almost never |
| **Profiles** | statement AST, context and scope types with a decidable ⊑, claim kinds, contradiction relation, statement-level rules | soundness-critical per profile | occasionally |
| **Moves and checkers** | operations and the checkers that admit their output, each declaring its reach | each checker is its own small TCB, admitted individually | often; this is where growth goes |
| **Adapters** | CAS, SAT, nauty, agents, lanes, dispatch | untrusted: can only *submit receipts* | freely |
| **Surfaces** | frontier, `explain`, campaign statement UX, views, tailings export | derived; can never affect `held` | freely |

**Boundary test.** Ask two questions: if this piece had a bug, could a false claim become held, and is it domain-independent?

- Yes and yes → kernel.
- Yes and no → profile or checker.
- No → adapter or surface.

**Promotion rule (D9).** A concept moves into the kernel only when two profiles independently need it. Log every promotion with its justification.

### 4.5 Shape

- **Kernel.** Datalog-shaped: facts (claims and receipts) plus rules (K1–K6 and admitted rules), folded to a fixpoint over the log. "What is missing for the goal?" is a why-not provenance query.
- **Runtime.** Elm-shaped. `update` is the pure kernel fold. Adapters are the runtime, performing *commands* (run this CAS or SAT job, dispatch this lane) whose results come back as *messages* carrying receipts. Nothing an adapter does touches the ledger except through `update`.
- **Campaign statement.** The analogue of Elm's `main`. It names the goal claim, the profile(s), the admitted moves and the done-condition. The kernel derives the frontier, refusals and tailings from it. See the sketch in Appendix E.
- **Move admission.** A new move starts untrusted: its outputs are `Asserted`, visible and weightless. Once its checker is admitted, it can mint held claims. This is the escape hatch and the extension path, and it should stay dignified, never shameful.

### 4.6 Why the rules are what they are (orientation)

Logic and geometry are linked by a dictionary that loses information in a controlled way:

- **V** sends equations to their solution set.
- **I** sends a set to all equations vanishing on it.

Round trips do not return exactly:

- Going points → equations → points yields the **closure**. That is Chevalley and IMAGE_CLOSURE: a closure point need not lift.
- Going equations → points → equations yields the **radical**. That is the nilpotent problem: V(x²) = V(x), but x ≠ 0 in k[x]/(x²).

The same pattern appears for **predicates along a map**, where the ∃-image and ∀-preimage are adjoint, which is where the NONEMPTY/EMPTY variance comes from. It appears again for **axioms ↔ structures**. A certificate's *reach* is the class of structures satisfying the axioms its proof used:

- a Nullstellensatz certificate works in every field;
- a sum-of-squares (SOS) certificate works in ordered fields;
- a rational-point search result is about ℚ only.

Those certificate systems are *complete* for algebraically closed and real closed fields respectively. There is no analogue for ℚ; Hilbert's tenth problem over ℚ is open. That is why refusals cluster at the ℚ/ℝ seam.

The system is bookkeeping for which round-trip losses you have incurred and which claims survive them.

---
## 5. Working hypotheses and open questions

### 5.1 Scope versus statement (WORKING, most likely pivot)

**Hypothesis.** The two roles separate cleanly:

- **Scope is context.** It is the class of structures or assumptions across which a claim is asserted: coefficient field class, point universe, characteristic, selected embedding, encoding assumptions, and conditional hypotheses such as "given census receipt R".
- **Region is statement.** It is *which objects* the claim is about: the ideal and variables, which n, which symmetry sector, which branch of a case split.

**Why separate them.** Scope quantified universally over contexts makes weakening (K2) sound for *every* claim polarity. If region were part of scope, variance would depend on polarity: an existential claim widens safely while a universal one narrows safely. Weakening would then need per-kind rules, and GP's ∃/∀ table would leak back into the kernel. Under this split:

- the transport cells that change *objects* (inclusion, image, equivalence) become K3 statement-level rules certified by relation checkers;
- the cells that change *context* (base extension, specialization) become reach questions under K1 and K2.

This matches GP's own table, where BASE_EXTENSION and SPECIALIZATION behave differently from all the others.

**Evidence to collect.** For each incident in the sweep, record whether it is a scope error or a region error, and whether the split is ever unnatural. Watch in particular for:

- symmetry sectors;
- "up to isomorphism";
- a SAT encoding treated as a context rather than as a different statement;
- conditional claims.

**Pivot trigger.** More than about three real incidents that can't be expressed under the split, or a profile that needs region-dependent weakening. If either happens, stop and report with the examples.

### 5.2 Meaning (OPEN, named blind spot)

Claim/scope/warrant checks *consistency*, not whether a statement means what the campaign needs. JC incidents of this kind include the "window" naming conflation and the imported γ ∈ {2,3} assumption. Working stance:

- each profile's statement AST has a Lean elaboration target;
- every campaign **goal** statement is meaning-audited once, by independent re-derivation from the primary source (M5);
- Lean statements are the gold standard where feasible.

The sweep must **count meaning incidents**. If meaning errors dominate costly incidents, report before building further (G0).

### 5.3 Claim kinds (OPEN)

The working lean is that the kernel knows only statements and a profile-supplied contradiction relation, and profiles own claim kinds:

- the algebraic profile has EMPTY, NONEMPTY (witness or existential), PREDICATE and IDENTITY;
- the census profile has at least EXISTS, NONE, COUNT = k up to isomorphism, and EXHAUSTIVE.

Promote to the kernel only under D9.

### 5.4 Relation transport (OPEN)

The ∃-image/∀-preimage variance (total, surjective) is domain-independent. The working lean is that it lives in the algebraic profile as K3 rules. Promote it to a kernel library if the census profile reimplements it.

### 5.5 Checker admission and versioning (OPEN, propose a policy)

A starting policy:

- A checker is admitted after one of:
  - two independent consumers, or
  - one consumer plus a stated soundness argument (a Lean proof where feasible) plus adversarial controls.
- A checker version bump stales every warrant it minted. Re-checking is cheap because receipts are retained.
- Every admitted checker appears in a **TCB manifest** stating its implementation (Lean-internal, verified external such as cake_lpr, or trusted external such as nauty) and its reach.

### 5.6 External checkers (WORKING)

The kernel may consume receipts from **external admitted checkers**, invoked out of process. Their TCB status is recorded in the manifest and surfaced in `explain`, so the TCB stays visible rather than hidden.

The goal is to port soundness-critical checkers into Lean over time. Search and production are never in the TCB. For example, Gröbner bases are computed externally, and only cofactor identities are replayed.

### 5.7 Mathlib (WORKING)

- The kernel is Mathlib-free; semantics are abstract per profile.
- A profile *may* later tie its semantics to Mathlib in a separate package: for example, mapping reach classes to Mathlib's algebraic hierarchy, or a certificate→Lean emitter.
- `MvPolynomial` is noncomputable, so the executable algebra is its own small sparse-polynomial implementation.

---

## 6. Work plan

Each phase ends with `reports/PHASE-n-REPORT.md` covering:

- what was built;
- each gate item marked PASS or FAIL with evidence;
- surprises;
- evidence for or against WORKING items;
- questions for Will.

### Phase 0 — Groundwork

Four parallel lanes. Nothing in the new kernel is written until 0a and 0b are done.

**0a. Must-refuse / must-accept corpus from GP v0.37**

1. Extract every counterexample, trap, confession and regression from GP's tests, docs (SPEC, DESIGN, REVIEW, the review/ release notes, the lean/ theory ledger) and fixtures.
2. Encode each as a *minimal* case: the situation, the conclusion attempted, the expected verdict (REFUSE or ACCEPT), the reason, and a source pointer (file and line, or test name).
3. Write the cases in a neutral JSON schema, not GP's graph format, so they outlive both systems.
4. Start from the seeds in Appendix A. The target is completeness over GP's history, not a fixed count.
5. Include **must-accept** positive controls, so the new system can't pass by refusing everything.
6. Run each case against the GP v0.37 oracle and record its verdict. Disagreements between GP and the expected verdict are findings; two are already known (Appendix A, items A3 and A8).

**0b. Campaign near-miss sweep and corpus harvest**

1. Follow the protocol in Appendix C.
2. Cover every repo listed in `SWEEP-SOURCES.md` (Appendix H), in its priority order. JC comes first, because the three shipped errors are there. GP's own private workspace comes second: treat the tool itself as a campaign that had incidents.
3. **Do not start this lane until Will has filled in `SWEEP-SOURCES.md`.** Clones are read-only. Private material stays local. `corpus/harvest/` is gitignored and classified private for any future public snapshot.
4. Produce `corpus/incidents/*.json` using the Appendix B schema, plus `INCIDENT-INVENTORY.md` with counts by class and campaign.
5. Harvest verbatim exports and receipts where they exist into `corpus/harvest/<campaign>/`, with a manifest and SHA-256 hashes.
6. **Never backfill or "repair" harvested data.** Recovery or migration products are labelled separately.

**0c. Lean feasibility spike (time-boxed to one token cycle, roughly 2 agent-days)**

1. Pin a Lean 4 toolchain and set up a Lake project.
2. Build an executable that reads a JSONL log (`Lean.Data.Json`) and folds a toy claim set with K1, K2 and K4.
3. Invoke one external checker via `IO.Process` and record it in a TCB manifest.
4. Build one tiny computable sparse polynomial over ℚ with a cofactor-replay check.
5. Report build times, ergonomics, and anything painful.
6. Evaluate whether Lean 4's built-in verified LRAT checker (the one behind `bv_decide`) is usable for census UNSAT receipts.

**Pivot condition for D3.** If Lean plumbing is still blocking progress after one further token cycle beyond the spike, or the fold is impractically slow on the harvested corpus, stop and propose one of two fallbacks: a Python kernel with the Lean spec and soundness proved over a model of it, or a Lean kernel with Python adapters. Will decides.

**0d. GP v0.37 freeze housekeeping. Prepare only; do not push without Will.**

1. Tag v0.37.0 as frozen.
2. Prepare a v0.37.1 **doc-only** patch:
   - fix the 17 mojibake em-dashes (`â€”`) in README.md;
   - fix the SPEC.md status block, which still says graph format 7 / kernel epoch 11 / "eleven live sessions";
   - remove or annotate public links to private files (KILL-CRITERIA.md, HISTORY/);
   - add this banner at the top of README.md, verbatim, with no timeline and no successor name:

     > *Frozen at v0.37.0. This repository remains the reference implementation and fixture source for a successor now in design. No further feature development here.*
3. Record, but do not fix, two known kernel issues as KNOWN-ISSUES:
   - **Containment conflation.** The NOT_BY_IDEAL discharge advises establishing an edge by radical membership. That earns the point cells only, but the IDENTITY cells on NECESSARY_CONDITION/AGAINST and on RESTRICTION need ideal containment. The V(x²)→V(x) probe shows the false licence that following the advice would open.
   - **SPECIALIZATION conservatism mislabelled as a theorem.** A p-integral unit-ideal certificate licenses EMPTY ALONG (char 0 → char p); a p-integral witness licenses NONEMPTY ALONG.

**Gate G0**

- The back-brief is approved.
- The 0a corpus covers GP's history, with every case source-pointed and the oracle verdicts recorded.
- The 0b inventory covers every listed repo, with counts by class.
- The 0c spike report is written.
- **Decision point:** report before Phase 1 if either of these holds (cost classes are defined in Appendix B):
  - MEANING alone is ≥ ~30% of **high-cost** incidents;
  - MEANING plus ADAPTER is ≥ ~40% of high-cost incidents.

  Either would mean the core is aimed at the wrong problem. **Small-n rule:** if the inventory has fewer than ~25 incidents in total, report qualitatively instead of applying percentages.

### Phase 1 — Core spec (mostly thinking)

1. Write `SPEC-CORE.md`, one page: the types from §4.1, `held`, K1–K6, the inconsistency finding, the profile interface, and the scope/region decision with the evidence from 0b.
2. Write the Lean **soundness statement** (Appendix D sketch). It must elaborate; the proof may be `sorry` at this gate.
3. **Paper expressiveness scoring.** For each non-MEANING incident, can the core express the situation, and would it have refused the error? Record the results in the inventory.

**Gate G1**

- The spec fits on one page.
- The soundness statement elaborates.
- At least ~80% of non-MEANING incidents are expressible, **and** every inexpressible *high-cost* incident has a written reason. (Under the small-n rule, report the inexpressible ones qualitatively.)
- The scope/region split holds, or the pivot has been reported.

### Phase 2 — Kernel

1. Implement the kernel in Lean: the log fold, `held`, K1–K6, the inconsistency finding, the TCB manifest, and a why-not query ("what's missing for claim X").
2. Prove soundness with no `sorry`, against the abstract profile interface, under explicit checker-soundness and rule-soundness hypotheses.
3. Add property tests: fold determinism; merge equals concatenation plus re-fold; retraction; staleness.

**Gate G2**

- The D8 budget holds: core logic ≤ ~500 lines, serialization and decoding ≤ ~400, soundness statement plus dependencies ≤ ~80, and no tripwire crossed.
- Soundness is proved.
- The property tests pass.
- Every kernel design choice is traced to a corpus case or an incident.

### Phase 3 — Minimal algebraic profile

1. Define the statement AST: ideals over named variables with ℚ coefficients, claim kinds, and a witness-point form.
2. Define contexts and scopes: field class (ANY_FIELD, CHAR_0, ORDERED, specific fields), point universe, characteristic. These map onto GP's reach vocabulary.
3. Implement checkers, all of them *replay* checkers with search kept external:
   - cofactor replay (membership and unit ideal);
   - witness substitution;
   - ideal-level containment, **kept separate from point-level containment**;
   - SOS contradiction replay (ordered reach);
   - p-integrality (specialization reach);
   - exact image/elimination replay only if the corpus needs it.
4. Implement K3 rules for the object-changing relations (inclusion, image, equivalence), using the ∃/∀ variance.
5. Run the full 0a corpus. Differential-test against the GP oracle on GP's fixtures: JC(2), matroid, gamma_window, the DK retrodiction, and the ARR15 slices.

**Gate G3**

- 100% of must-refuse cases are refused and 100% of must-accept cases are accepted.
- Every disagreement with the oracle is triaged as a GP bug, a core bug, or an expressiveness loss.
- **The corpus is the spec.** If a corpus case itself turns out to be wrong, correcting its expected verdict needs Will's sign-off and a log entry in `corpus/CHANGES.md`. Never edit it quietly to make a gate pass.
- The kernel is unchanged since G2, apart from logged fixes.

### Phase 4 — Census profile (the portability test)

1. Define the statement AST:
   - finite families of combinatorial objects (graphs, incidence structures, point configurations described combinatorially), with explicit size parameters;
   - "up to isomorphism" as an explicit statement construct, not a context.
2. Define claim kinds: at least EXISTS, NONE, COUNT = k up to isomorphism, and EXHAUSTIVE.
3. Implement moves and checkers:
   - isomorphism and automorphism checks (a certificate is a permutation, easy to check);
   - forbidden-substructure exclusion (the witness is an embedding);
   - UNSAT via LRAT (a Lean-internal verified checker or cake_lpr);
   - SAT via model check;
   - **encoding correctness** as the central meaning risk (M4). Options are a small admitted encoder, a Lean-proved encoder, or cross-validation on small cases with a documented TCB;
   - enumeration completeness (M4; see the options there);
   - symmetry-breaking soundness: it preserves existence up to isomorphism, not counts, and only when the breaking predicate is complete.
4. Build a census must-refuse set:
   - timeout read as UNSAT;
   - "none found up to n" read as "none exist";
   - an unsound symmetry break used for counts;
   - a non-exhaustive cover;
   - an unchecked LRAT proof;
   - a floating-point "verification";
   - an encoding without a correctness warrant.
5. Retrodict at least one DK slice. For example, the V4 sector census counts, which were independently matched by Lu's cell counts. That is a natural two-route (+) warrant example.

**Gate G4**

- The census profile lands with **zero kernel changes** (bug fixes excepted, and logged), or with promotions that satisfy D9 and are logged.
- All census must-refuse cases are refused.
- The DK slice retrodiction reproduces the known result.

### Phase 5 — Pilot and comparison

1. Define a minimal campaign statement format (Appendix E) and a derived frontier view.
2. **Tutorial campaign.** Write a fifteen-minute campaign in one profile. An agent makes a classic overclaim, gets one good refusal, fixes it, and lands a small honest result plus a tailing. Write it as the Elm-guide-style first page of the future README.
3. **u(22) slice.** Run a real, bounded slice of the Highway 61 campaign on the new core, combining census and realizability.
4. **Comparative arms.** Pick 12 incidents from the inventory, stratified by class. Run each through three arms, using separate agents per arm and recording effort (agent turns, wall time, and tokens where available):
   - (a) the new core;
   - (b) Lean plus blueprint (every claim a Lean statement, tagged axioms for external results);
   - (c) notebook plus checker scripts plus CI (the DK-style baseline).

**Gate G5**

- A fresh agent can run the tutorial from the campaign statement alone.
- **The Elm test:** Will reads the u(22) ledger cold and can state what is held, open and refused in under 10 minutes.
- **Comparative result.** With 12 incidents this is directional, not statistical.
  - **Beats the notebook (c):** catches at least 2 more of the 12 at no more than 1.5× the effort, *or* the same number at no more than 0.75× the effort.
  - **Not dominated by Lean (b) on errors:** catches no more than 1 fewer than arm (b).
  - **Beats Lean (b) on workability:** better on time to first held claim, and on agent turns per resolved obligation.

**If the core does not beat the notebook baseline, stop and reconsider. Do not add features to rescue it.**

---

## 7. Math lanes

These can run in parallel with the build, with research agents or deep-research passes. Each produces a short note, plus Lean where feasible, and has its own stop condition.

- **M1 — Scope semantics.**
  - Formalize scope as a class of contexts with a decidable, sound ⊑.
  - State kernel soundness in that form.
  - Stress-test the scope/region split (§5.1) on algebraic, census and real-realizability examples, including conditional hypotheses.
  - *Stop* when either the split survives about 10 hard examples, or a counterexample is written up.

- **M2 — Reach and requirement profiles.**
  - Map GP's reach vocabulary (U = nontrivial ring, O = ordered/SOS, Z = no zero divisors, CHAR_0, ORDERED, and specific fields) to classes of contexts.
  - Identify the corresponding Mathlib typeclasses for a future Mathlib-backed semantics package.
  - Record which reach facts are completeness theorems (Nullstellensatz, Positivstellensatz) and which are merely sufficient.
  - *Stop* at a table with sources.

- **M3 — Specialization reach.**
  - p-integral certificates and witnesses give conditional EMPTY and NONEMPTY transport from char 0 to char p. Build must-accept fixtures, including a demonstration that any ℚ-certificate of Fano emptiness must carry a 2 in a denominator.
  - Hensel-type lifting sends smooth F_p points to ℚ_p points, not ℚ points, which is a point-universe question.
  - The Lefschetz-style "empty for infinitely many p ⇒ empty over ℚ̄" is a family claim, not an edge, but it is useful context for census and matroid work.
  - *Stop* at fixtures plus a short note.

- **M4 — Census semantics.**
  - Soundness conditions for symmetry breaking: existence versus counts; lex-leader completeness.
  - Enumeration-completeness warrants. Options: a trusted generator (nauty/geng) with a TCB label; independent double enumeration agreeing on counts (the DK E5 bridge pattern); orderly-generation certificates. Rank them by trust and cost.
  - Encoding correctness: how a CNF is warranted to mean the combinatorial statement.
  - LRAT reach = "this encoding".
  - *Stop* at a ranked options memo that the Phase 4 builder can implement from.

- **M5 — Meaning audit protocol.**
  - Design the independent re-derivation of a campaign goal statement from its primary source: blind to the campaign's own formalization, then compared against it.
  - Include Lean goal statements.
  - Pilot it on the DK goal, the Cloquet goal and the u(22) goal.
  - Count how many historical incidents it would have caught.
  - *Stop* at a protocol plus the three pilots.

---
## 8. Gates and kill criteria (pre-registered)

| Gate | Pass condition | On failure |
|---|---|---|
| G0 | Back-brief approved; 0a corpus complete and source-pointed; 0b inventory covers all repos in `SWEEP-SOURCES.md`; 0c spike report written | Report. Re-scope before Phase 1 if MEANING ≥ ~30% of high-cost incidents, or MEANING + ADAPTER ≥ ~40%. Under ~25 incidents: qualitative report instead |
| G1 | One-page spec; soundness statement elaborates; ≥ ~80% of non-MEANING incidents expressible, and every inexpressible high-cost incident explained | Report the inexpressible incidents; possible pivot on §5.1 |
| G2 | D8 budget held (logic ≤ ~500, serialization ≤ ~400, soundness statement ≤ ~80; no 1.5× tripwire); soundness proved with no `sorry`; property tests pass | Budget overrun → move logic to a profile or stop and rethink. Never quietly grow the kernel |
| G3 | 100% must-refuse refused, 100% must-accept accepted; every oracle disagreement triaged; corpus corrections signed off and logged | Fix, or report an expressiveness loss |
| G4 | Census profile needs zero kernel changes (bug fixes excepted and logged, or D9-justified promotions); census traps refused; DK slice reproduced | A kernel change without D9 justification means the abstraction leaks: report and stop |
| G5 | Tutorial runs from the campaign statement; Will's cold read under 10 minutes; comparative thresholds in Phase 5 met (beats notebook, not dominated by Lean on errors, beats Lean on workability) | **Kill or rethink.** Do not add features to rescue it |

Numbers marked "~" are Will's to adjust. Record the actual values in the phase reports.

---

## 9. Not-list

GP 0.50 will not:

- use confidence scores, probabilities or "trust levels" as authority;
- grant authority from declarations, prose, citations or tags;
- include a CAS, SAT solver, enumerator or search engine in the TCB. Search is never authoritative; only replay is;
- include publication, release, dossier or packet machinery in the core. These are surfaces, and only after G5;
- add edge types, claim kinds or kernel concepts without the D9 two-profile rule;
- depend on Mathlib in the kernel;
- load checkers dynamically without admission and a TCB manifest entry;
- invent a general-purpose formula language. Profile ASTs are small and specified, with Lean elaboration targets;
- migrate old GP graphs. Fixtures are converted into the neutral corpus instead;
- include visualization, 3D explorers or MCP/hook enforcement before G5. The hook comes back as an adapter later;
- mix "we refuse this soundly", "we refuse this out of caution" and "we license this knowing better". The last must stay empty, and conservatisms are registered as data.

---

## 10. Repo layout and conventions (proposal)

```
grandportage-0.50/        # private working repo through G4 (D2)
  BACKBRIEF.md            # Phase 0 reader test
  SPEC-CORE.md            # one page, Phase 1
  TCB.md                  # admitted checkers, implementation, reach
  PROMOTIONS.md           # D9 log
  KNOWN-CONSERVATISM.md   # refused-more-strictly-than-truth register (data)
  kernel/                 # Lean 4, Mathlib-free: types, fold, held, K1–K6, soundness
  profiles/algebraic/     # AST, contexts/scopes, checkers, K3 rules
  profiles/census/
  adapters/               # CAS/SAT/nauty/agent runners: untrusted, submit receipts only
  surfaces/               # frontier, explain, campaign-statement tooling
  corpus/
    must/                 # must-refuse / must-accept cases (neutral JSON)
    incidents/            # Appendix B records
    harvest/<campaign>/   # verbatim exports + manifest + SHA-256, never backfilled
  corpus/CHANGES.md         # signed-off corrections to expected verdicts (G3)
  SWEEP-SOURCES.md          # Will's sweep manifest (Appendix H)
  reports/PHASE-n-REPORT.md
  oracle/                 # pinned GP v0.37.0 checkout or submodule, read-only
```

Conventions:

- Every claim about the math cites a source: a corpus case, an incident id, a paper, or GP's file and line.
- Reports distinguish *verified here*, *reproduced from source* and *asserted*.
- Keep prose short. The GP docs grew by confession, so write the confession as a corpus case instead.

---

## Appendix A — Corpus seeds (from GP v0.37; extract the complete set)

Verdicts are for the new core. Where the "Oracle" column is left out, GP v0.37 agrees. A **Known issue** entry means GP v0.37 disagrees or gives misleading advice.

| ID | Situation | Attempted conclusion | Expected |
|---|---|---|---|
| A1 | Nonsquare-class emptiness certificate over ℚ(√17) (the JC C08 residue) | Empty over every char-0 field | REFUSE: reach is that field only |
| A2 | x² + 1 = (x + i)(x − i) valid over ℚ(i) | Same identity over ℚ | REFUSE: not expressible over ℚ |
| A3 | Models (x²) and (x) over ℚ; point containment holds via the radical | (a) identity x = 0 pulled back to ℚ[x]/(x²); (b) witness 0 at (x²) pushed to (x) | (a) REFUSE even with radical containment; (b) ACCEPT. **Known issue:** the oracle's NOT_BY_IDEAL discharge advises the radical route, which would open (a) |
| A4 | A = ℤ₍ₚ₎[x]/(px): x = 0 holds on the generic fibre | x = 0 mod p | REFUSE: the derivation uses 1/p |
| A5 | d₂ = h₂ − (3/8)h₁² | Reduce mod 2 | REFUSE: not 2-integral |
| A6 | Nodal cubic y² = x²(x − 1): real points Zariski-dense, restricted region an isolated point | Predicate "vanishes on the region" carried to the whole curve | REFUSE; identities are decided by membership, not density |
| A7 | Projection of xy = 1 to the x-axis; 0 lies in the closure but not the image | (a) witness at 0 lifts; (b) existential nonemptiness of the closure ⇒ image nonempty | (a) REFUSE (Chevalley); (b) ACCEPT |
| A8 | Fano: empty over ℚ, nonempty over F₂; non-Fano the reverse | (a) unconditional transport across char 0 ↔ char 2; (b) EMPTY char 0 → char p with a p-integral unit-ideal certificate; (c) a p-integral ℚ-witness reduced mod p | (a) REFUSE; (b) and (c) ACCEPT. **Known issue:** the oracle refuses (b) and (c) and calls the refusal a theorem |
| A9 | xy = 1 on the hyperbola | Identity carried to k[x] after elimination | REFUSE: inexpressible there |
| A10 | SOS certificate 1 + x² ≠ 0 witnessing emptiness of x² + 1 = 0 | Empty over ℝ and ℚ; empty over ℂ | ACCEPT for ℝ and ℚ; REFUSE for ℂ. Equality replay alone ≠ contradiction |
| A11 | Selected real root; a nontrivial automorphism (w ↦ −7 − w, x ↦ −x) | Sign predicate copied unchanged | REFUSE; identities via a checked substitution ACCEPT |
| A12 | Saturation declared "solutions unchanged" (point equivalence) | Identity transported | REFUSE unless ring isomorphism is verified (both pullbacks and both compositions) |
| A13 | Relaxation (dropping equations), transporting an identity from the tight side to the loose side | AMBIENT identity vs one DERIVED from the tight ideal | AMBIENT ACCEPT; DERIVED REFUSE |
| A14 | Fano control routed across the non-Fano saturation edge over F₂ | Any conclusion | REFUSE: the path is disconnected (wrong object) |
| A15 | Two computations sharing no variable, joined by a sentence (GI-BRIDGE) | The joined conclusion | REFUSE: no admitted rule |
| A16 | Partition with a missing branch, all listed branches empty | Parent empty | REFUSE; ACCEPT only with a checked exhaustive cover |
| A17 | Latest verification attempt timed out or was UNVERIFIED | Any authority | REFUSE; retry remains possible |
| A18 | Model edited after its evidence was produced | The evidence still counts | REFUSE: stale |
| A19 | Adapter: CAS program declares `poly g0` shadowing ring variable g0, giving false UNIT verdicts | Accept the backend verdict | REFUSE at the adapter; replay catches it anyway |
| A20 | Polynomial quotient with a nonconstant divisor (the remainder is discarded) | Rational identity | REFUSE; the constant-denominator restatement ACCEPT |
| A21 | Laurent rows 7–8: 6y²G and −3y²G² replaced by 0 while G is symbolic | Depressed row | REFUSE: the legal instance G = y⁻⁵ breaks it |
| A22 | Coefficient cap: dm2 = 1, d2 = y satisfy the scalar target but need dm4 = −y/2 | Lift with cap(dm4) = 0 | REFUSE: selected coefficients are necessary only |
| A23 | Localized unit ideal on an open model | Parent empty | REFUSE: open-model EMPTY is ACCEPTED; transport to the parent is refused |
| A24 | Cloquet K₂,₂,₂ collapsed placement | "No realization" from an unguarded Gröbner computation | REFUSE: nondegeneracy guards are required, and collapsed solutions always exist |
| A25 | Merge: the same id redeclared with a different normalization; the same object under two ids | Silent merge or inferred identity | REFUSE; aliasing requires an explicit audit |
| A26 | Historical record with misleading booleans or an unknown certificate name | Reach granted | REFUSE: reach is earned by a current receipt |

**Must-accept controls to include at minimum:**

- An exact rational unit-ideal certificate carries EMPTY across base extension within its reach.
- A witness point carries NONEMPTY along an inclusion.
- EMPTY carries back along a checked ideal containment.
- A cover with a checked exhaustive partition and all branches held empty carries EMPTY to the parent.
- A verified ring isomorphism carries identities.
- An existential across an image closure carries NONEMPTY (A7b).
- The p-integral cases (A8b, A8c).

Census traps are listed in Phase 4.

---

## Appendix B — Incident schema

```json
{
  "id": "DK-0007",
  "campaign": "DK",
  "origin": "own | literature | tool",
  "source": {"repo": "cfg23", "ref": "<commit or path:line>", "date": "2026-08-30"},
  "claimed": "what was asserted or consumed, in one or two sentences",
  "problem": "what was wrong or nearly wrong",
  "class": "SCOPE | WARRANT | COVER | BINDING | JOIN | MEANING | ADAPTER | OTHER",
  "scope_or_region": "SCOPE | REGION | BOTH | N/A",
  "discovered_by": "self-review | checker | independent replication | external | GP | unknown",
  "cost": "low | medium | high",
  "cost_note": "time lost, retractions, public errata",
  "shipped": false,
  "gp_v037_would_catch": "yes | no | partial | n/a",
  "core_expressible": null,
  "core_would_refuse": null,
  "notes": ""
}
```

Class meanings:

- **SCOPE**: a claim used beyond its warrant's reach.
- **WARRANT**: an insufficient warrant treated as held (timeout, float, search miss, citation, assertion).
- **COVER**: a non-exhaustive case split, or an unsound symmetry or reduction.
- **BINDING**: stale evidence, or evidence for a different object or model.
- **JOIN**: two results combined with no admitted connecting rule.
- **MEANING**: the statement doesn't mean what it is used for (conflated names, wrong formalization, imported assumption).
- **ADAPTER**: a tool gave a false answer (parser, shadowing, backend bug).

`origin` separates the campaign's own errors (`own`) from errors found in published work (`literature`, e.g. the Kurz LP row discrepancy Cloquet found) and defects in the tooling itself (`tool`). Literature incidents count: other people's errors are free training data.

Cost classes:

- **low**: under an hour lost, no rework;
- **medium**: hours to a day lost, or an internal claim retracted;
- **high**: more than a day lost, or a public erratum, or a wrong claim that shipped.

`core_expressible` and `core_would_refuse` stay null until Phase 1.

---

## Appendix C — Sweep protocol (0b)

For each repo:

1. **Read the campaign's own summaries first:** charter, handoffs, checkpoints, errata, review packets, retrodiction reports.
2. **Mine history.** Look for commits and messages mentioning fix, wrong, retract, erratum, actually, revert, supersede, stale, timeout, mismatch, "not what", conflat*, scope, and any reported TIMEOUT or UNKNOWN handling.
3. **Fill one Appendix B record per incident.** Near-misses caught before shipping count, and so do errors the campaign found in the literature (`origin: literature`). Record the smallest true description; don't editorialize, and quote only short fragments with a pointer.
4. **List the custody machinery the campaign invented locally:** receipt formats, scope labels, dispatch rules, ledgers, kill criteria. These are candidate profile features.
5. **Harvest** retained receipts, exports and certificates verbatim, with a manifest (path, SHA-256, provenance). Label anything regenerated as a recovery product.
6. **Close out each repo** with a one-paragraph summary: the top three incident classes, what the campaign actually relied on for trust, and anything that doesn't fit the schema.

Budget roughly by repo size. Report gaps (missing history, inaccessible data) rather than filling them.

---

## Appendix D — Lean kernel sketch (illustrative; the builder owns the design)

```lean
-- One profile's interface. Semantics may be noncomputable; checking must be computable.
structure Profile where
  Ctx      : Type                      -- one context: a field, point universe, encoding assumptions, …
  Scope    : Type                      -- a finitely described class of contexts
  mem      : Ctx → Scope → Prop        -- c ∈ ⟦S⟧
  le       : Scope → Scope → Bool      -- S' ⊑ S, decidable
  le_sound : ∀ S' S c, le S' S = true → mem c S' → mem c S
  Stmt     : Type
  Holds    : Stmt → Ctx → Prop         -- intended meaning
  contra   : Stmt → Stmt → Bool        -- declared contradiction (for the inconsistency finding)

def Means (P : Profile) (φ : P.Stmt) (S : P.Scope) : Prop :=
  ∀ c, P.mem c S → P.Holds φ c

inductive Warrant
  | checked  (checker : CheckerId) (receipt : Hash) (inputs : List Hash)
  | derived  (rule : RuleId) (premises : List ClaimId)
  | cited    (ref : String)
  | asserted
  | absent   (reason : String)

-- A checker is sound for its reach: a valid receipt means the statement holds on the scope.
def CheckerSound (P : Profile) (k : Checker P) : Prop :=
  ∀ φ S r, k.valid φ S r = true → P.le S (k.reach r) = true → Means P φ S

-- Target theorem (Phase 1: statement elaborates; Phase 2: proved):
theorem held_sound (P : Profile) (log : Log P)
    (hk : ∀ k ∈ admittedCheckers log, CheckerSound P k)
    (hr : ∀ r ∈ admittedRules log, RuleSound P r) :
    ∀ cl ∈ heldClaims (fold log), Means P cl.stmt cl.scope := by
  sorry
```

The conceptual point to preserve: **K2 (weakening) is sound for every statement because `Means` quantifies universally over contexts.** Anything polarity-dependent belongs in a profile's statement-level rules (K3).

---

## Appendix E — Campaign statement sketch (u(22) / Highway 61)

```
campaign HW61
  profiles  census + exact_real
  goal      EXISTS: 22 points in ℝ² with ≥ 61 unit-distance pairs
  scope     { ℝ² }                                  -- context; nothing to vary here
  moves
    enumerate_candidates    -- graphs on 22 vertices, ≥ 61 edges, K₂,₃-free;
                            --   warrant: enumeration-completeness receipt (M4)
    exclude_by_subgraph     -- witness: embedding of a known non-unit-distance subgraph
    exclude_by_relaxation   -- complex/real realizability certificate (necessary-condition relation)
    realize                 -- exact coordinates in a number field; distances replayed exactly
  done
    held(goal)
    or held(EXHAUSTIVE(candidates)) ∧ ∀ branch ∈ candidates: held(NONE(branch))
```

The kernel derives:

- **the frontier:** which candidates are neither realized nor excluded, and which warrants are missing;
- **the refusals:** a timeout doesn't exclude a branch; a numeric near-realization isn't a realization; an exclusion without a completeness receipt doesn't close the cover;
- **the tailings:** every held NONE(branch), with its scope and warrant, is a publishable negative.

---

## Appendix F — Glossary

- **Claim**: a statement plus a scope plus a warrant.
- **Scope**: a class of contexts, read universally.
- **Region**: which objects the statement is about. It is part of the statement.
- **Warrant**: what backs a claim.
- **Held**: the warrant checks, its inputs are fresh, and its reach covers the scope.
- **Reach**: the class of contexts in which a checker's receipt is valid. For a certificate, the models of the axioms its proof uses.
- **Move**: an operation that produces a claim.
- **Checker**: validates a move's receipt and mints the warrant; it is admitted individually.
- **Profile**: a domain vocabulary (statement AST, contexts and scopes, claim kinds, statement-level rules).
- **TCB**: the trusted computing base — kernel plus admitted checkers.
- **Obligation**: a claim that is not held but is needed.
- **Tailing**: a held negative with explicit scope, publishable.
- **Oracle**: the frozen GP v0.37.
- **Fixed rope**: an admitted move and checker that others can clip into.

---

## Appendix G — References

- S. Toulmin, *The Uses of Argument* (1958): claim / warrant / qualifier.
- R. Milner et al., LCF (1970s): kernel-minted theorems as an abstract type.
- G. Necula, "Proof-Carrying Code", POPL 1997.
- T. J. Green, G. Karvounarakis, V. Tannen, "Provenance Semirings", PODS 2007: warrant composition (× joint use, + independent routes).
- A. Mokhov, N. Mitchell, S. Peyton Jones, "Build Systems à la Carte", ICFP 2018: freshness and traces.
- DRAT/LRAT proof formats, and cake_lpr (a verified LRAT/LPR checker in CakeML): census UNSAT warrants.
- T. Tao et al., Equational Theories Project (2024–25): a pooled, provenance-tracked implication graph with Lean as arbiter. The nearest precedent for the stretch vision.
- Lean blueprint (leanblueprint): a dependency-and-status graph for formalization campaigns.
- LMFDB reliability labels: scope labelling (proven / conditional / heuristic) in a shared mathematical database.
- GP v0.37: SPEC.md, DESIGN.md, REVIEW.md, lean/THEORY.md, docs/ATLAS-MAPPING-V0.md, docs/PRESERVATION-ATLAS-PROGRAM.md, docs/FOUNDATIONS-PRIOR-ART.md.

---

## Appendix H — `SWEEP-SOURCES.md` template (Will fills in)

Priorities are proposals. Reorder freely, and remove rows that don't exist or are out of scope.

```markdown
# SWEEP-SOURCES

Host(s): <local / Mac mini / other>  ·  Access: read-only clones
Private material stays local; corpus/harvest/ is gitignored.

| Pri | Campaign | Repo / path | Public? | Read first | Notes |
|---|---|---|---|---|---|
| 1 | JC | <path to math-stuff> ; github.com/wstrinz/grandportage-jc-campaign | mixed | d2_plane_72_108/, whetstone/, MODELLING_GAPS.md, SESSION_HANDOFF.md, F2_TOWER.md | origin of GP; three shipped errors |
| 2 | GP (tool as campaign) | <path to private GP workspace> | private | HISTORY/, KILL-CRITERIA.md, EXPERIMENT-B.md, HANDOFF.md, TESTPLAN.md, T1–T5 reports | EXPERIMENT-B: 57 hand-typed edges, 88% accurate |
| 3 | DK | github.com/wstrinz/cfg23 ; github.com/wstrinz/configuration-23-4 ; <T1 DK retrodiction report path> | public + <private?> | checkpoints, errata, E5 bridge, exclusion replay | Lu comparison = independent-route data, not an incident |
| 4 | Cloquet | <path to match4> ; gpcqread.md ; cqscouting.md | private | CHARTER, CHECKPOINT, receipts/verdict schemas | literature incidents: Kurz LP row, K₂,₂,₂ collapse |
| 5 | ARR15 | <path> | <?> | <handoffs / reports> | |
| 6 | Pigeon River | <path to ac-2gen> | private | epoch reports, verifier rejections | |
| 7 | u(22) / Highway 61 | <path to UD22-PACKET.md> | private | packet only | no incidents expected; M5 meaning-audit pilot |
| 8 | LSEM / SCOUT probes / other | <paths or "skip"> | | | Will to decide scope |

Anything the agent must NOT read or harvest: <list, or "none">
```
