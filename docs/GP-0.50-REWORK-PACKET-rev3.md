# Grand Portage 0.50 — rework packet, revision 3: honest carrying between worlds

**Packet date:** 2026-09-28 · **Owner:** Will · **Audience:** local builder agent(s) and math-lane research agents
**Status:** Phase 0a is in progress. This revision **supersedes revisions 1 and 2** (`GP-0.50-REWORK-PACKET.md`, `GP-0.50-REWORK-PACKET-rev2.md`) **and Addendum A** (`GP-0.50-ADDENDUM-A-REGIMES.md`, folded in since revision 2). Keep the earlier revisions alongside to diff against. §R lists what changed.

**Naming.** The project stays **Grand Portage**. This packet calls the rework **GP 0.50** and the frozen predecessor **GP v0.37**. The label is deliberately pre-1.0; it is 0.50 rather than 0.5 because semver compares minor versions numerically, so 0.5.0 would sort *before* 0.37.0. Sub-components (the kernel, profiles, a future pooled platform) are deliberately unnamed for now: use plain descriptive terms and do not invent names. The term "profile" is itself under review; "domain" is the leading alternative. Use "profile" until Will decides.

---

## 0. How to use this packet

**If you have not yet written a back-brief,** read everything first, then write `BACKBRIEF.md` (one page at most) covering: the goal in your own words, the DECIDED items, your plan for Phase 0, and anything unclear or that you think is wrong.

**If you already wrote one for an earlier revision,** write `BACKBRIEF-REV3.md` instead (half a page at most). It should cover:

- what changes for work already in flight;
- anything in 0a/0b that now needs redoing (expected answer: nothing, apart from one new corpus seed, A27; see §R);
- your reading of the core statement (§2), the three G1 adoption decisions (§7.3), and the interoperability default (D18, §7.5).

**Either way, stop there until Will approves.** The back-brief doubles as a reader test of this packet.

**Tags.** Every item is tagged:

- **DECIDED**: do not change without asking Will.
- **WORKING**: the best current hypothesis. Build on it, log evidence against it, and be ready to pivot.
- **OPEN**: resolve it against the corpus and report. Never guess silently.

**Stop and ask Will** if any of these happen:

- you want to change a DECIDED item;
- the kernel wants to exceed its budget (D8);
- a gate fails;
- anything would touch a public repo;
- you find yourself building something on the not-list (§12);
- you are about to build something the adopt/imitate map (§7) says should be adopted;
- you are more than a day into plumbing without progress on the phase deliverable.

**Inputs Will supplies** before Phase 0b starts: a filled-in `SWEEP-SOURCES.md` (template in Appendix H).

---

## R. Changes

### Changes in revision 3

1. **Interoperability by default (new D18).** Wherever a community format or tool exists for a boundary, GP reads and writes it rather than inventing its own. Interop lives in adapters, surfaces and the binding layer, never in the kernel. Adoption still has to serve the §2 guarantee (D15); this is not amalgamation for its own sake.
2. **§7.1 landscape updated** from a prior-art pass:
   - **LMFDB's** source / reliability / completeness pages, and its 2026 effort to bridge LMFDB data to Lean;
   - **Magma's** rigor tiers and **PARI's** below-GRH default bound;
   - **Formal Conjectures** as a source of goal statements;
   - more precise descriptions of **Trocq** and **Logipedia**;
   - **MathKernel** as a cautionary example of scope sprawl.
3. **Correction.** The statement-comparing reviewer belongs to **LeanMarathon**, which uses LeanArchitect's metadata format. It is not part of LeanArchitect itself. Fixed in §7.1, §7.2 and M5.
4. **New §7.5, interop surfaces:** the formats GP should consume and produce.
5. **0e reading list: P16–P18 added** (LMFDB reliability/completeness and the Lean-bridging effort; the Magma rigor taxonomy; Formal Conjectures). The questions for P1, P4 and P10 are sharpened.
6. **New corpus seed A27:** PARI's default class-group bound treated as GRH-conditional or unconditional. It is the arithmetic regime's canonical silent-scope trap.
7. **M5** uses Formal Conjectures statements as a first-choice goal source when one exists.
8. **Phase 5** exports tailings in an LMFDB-compatible source / reliability / completeness shape.
9. **G0 territory check** now also asks which community would want GP as a *component*.
10. **Not-list:** no GP-specific format at a boundary where a community format exists, without a written reason; no rival-platform ambitions.

### Changes in revision 2 (from revision 1)

1. **New core statement** (§2). The Elm-style guarantee, and its positive twin, "earned but unclaimed" implications, are now the organizing idea. Claim/scope/warrant is the mechanism that delivers them.
2. **Addendum A folded in.** The regime map, the positive/negative asymmetry, the checkability line and "the ladder is not the scope order" are now §3–§4. Real algebraic numbers are §8.8. Validated numerics is math lane M6.
3. **Adopt-before-build** (§7). This revision adds a map of what to adopt from existing, expert-built work and what to imitate, plus a list of things not to bolt on. It also frames three adoption decisions for G1:
   - warrant form;
   - the MathEvidence checker layer;
   - the Mathlib hierarchy as scope vocabulary.
4. **New Phase 0 lane, 0e: a prior-art review.** It is time-boxed and ends in `PRIOR-ART.md`.
5. **Decisions added:** D14–D17. **Decision changed:** D12 now names Mathlib alignment for statement ASTs.
6. **Math lanes.** M2 is refocused on mapping reach to the Mathlib hierarchy. M6 (validated numerics) is added, scheduled after G5.
7. **Gates.** G1 now includes the three adoption decisions. No other thresholds changed.
8. **Not-list extended:** no trust ladders, no user-facing institution machinery, no general computer algebra reimplemented in Lean.
9. **No change to Phase 0a or 0b.** The must-refuse corpus and the incident sweep are valid whatever the outcome of these decisions. They are what will *test* the core.

---

## 1. Why this exists

GP v0.37.0 has a sound, small, mostly classical transport kernel. It is wrapped in roughly 64k lines of Python, 43 CLI subcommands, 35 checker rules and about 75k words of documentation. Its domain is narrow (exact affine algebra over fields), and its core concepts were never named at the user level; its vocabulary grew out of the Jacobian-conjecture (JC) campaign's incidents.

The campaign record since then:

- **DK** succeeded without GP. What mattered there was census completeness, replayed exclusions, exact witnesses, a Lean proof and independent replication.
- **Pigeon River**'s certificates were checked by an external verifier.
- **Cloquet** built its own receipt contract rather than extending GP.

Every campaign reinvented a custody layer, and that custody layer is the real core. The transport table is one domain's rulebook on top of it.

The wider field is also moving, from several directions at once. On the engineering side: MathEvidence, MathKernel, and LeanArchitect/LeanMarathon. From mathematicians: Formal Conjectures, and the LMFDB's 2026 effort to give its data Lean-backed reasons to trust it (see §7 and Appendix G). GP 0.50 should interoperate with them by default (D18), adopt or imitate their good parts rather than rebuild them, and put its own effort into the part that still appears unoccupied.

This is a **full rework**; GP has no users to protect. GP v0.37 is frozen and serves as:

1. an **oracle** for differential testing;
2. a **fixture source**;
3. a **counterexample library**.

We port knowledge, not code.

---

## 2. The core (WORKING: the organizing statement; the corpus is expected to push on it)

### 2.1 The guarantee

> **If GP says a claim holds in a world, it does. When a result can be carried to another world, GP carries it for you. When it can't, GP says exactly why.**

A **world** is a class of contexts: every field of characteristic 0, ordered fields, ℝ with a selected root, finite graphs up to isomorphism, "assuming census receipt R". **Carrying** means moving a result between worlds, or between objects within a world, along a relation whose soundness is known.

This is a portage in the literal sense. You carry what can be carried overland between waters, and you say plainly what has to be left behind or rebuilt on the other side. There is no clever compression: GP is honest about what transfers and automates the boring, error-prone parts.

### 2.2 Elm as the model

| Elm | GP |
|---|---|
| Runtime exception | A false claim believed, or a claim used outside its scope |
| "No runtime exceptions" | The kernel soundness theorem: held ⇒ true throughout its scope, given admitted checkers (Appendix D) |
| Chosen domain (browser apps) | Chosen regimes (§3) |
| `Maybe` instead of null | `Absent` warrants: timeouts and failed searches cannot pose as answers |
| Exhaustive `case` | A cover must be checked exhaustive before its parent claim is held |
| Friendly compiler errors | Refusals that say what would make the claim hold |
| Ports (the escape hatch) | `Asserted`: visible, never trusted, and never shameful |

### 2.3 Two duals

- **No silent overclaims.** Nothing becomes held without a warrant whose reach covers its scope.
- **No missed implications.** GP surfaces what you have *already earned but not claimed*. Examples:
  - "This certificate used only ring axioms, so it holds over every field, not just the ℚ you asked about."
  - "This held NONE at n = 22 also settles these subcases."
  - Eventually, across campaigns: "a tailing from campaign X discharges this obligation in Y."

  The kernel's fixpoint computes these consequences under admitted rules. Surfaces present them without flooding the user; §6.5 covers this.

### 2.4 One-line job and north star

- **One-line job.** Say what you are entitled to believe right now, and what it would take to be entitled to more.
- **North star.** "Elm for vibe maths": stating and running a recreational or open-problem campaign with LLM agents should be low-error to the point of being fun. Constrained, but not cramped.
- **Fixed ropes.** An admitted move plus its checker is a fixed rope, something an amateur or an agent can clip into and trust. The move library is the rope network. Every campaign that leaves behind an admitted move extends it.
- **Distant stretch.** Pooled campaigns work like an autobattler: players compose moves against a shared referee (the kernel), the ledger is the replay, and tailings are published with explicit scope. Keep this possible; do not build for it now.

**GP is not** a proof assistant (Lean is), a CAS, a search engine, a publication pipeline, or a confidence calculus.

---

## 3. Regimes: where GP can be strong (DECIDED as framing; the characterization text is WORKING)

### 3.1 The rationals are the workbench, not the subject

Exact computation happens in ℚ, in finite extensions of it (such as ℚ(√17)), and in finite fields F_p. Almost no campaign's *question* is about ℚ:

- configuration and matchstick realizability ask about ℝ;
- varieties ask about ℂ;
- census questions ask about finite objects.

**GP's job is the gap between where you can compute and where the question lives.** Describe GP to users in those terms, never as "a rational-arithmetic tool".

### 3.2 Positive and negative claims are asymmetric

Positive claims ("here is a solution") are checkable in every regime by substitution. Negative claims ("no solution") need certificates, and *complete* certificate systems exist only in some regimes. "Complete" means a certificate always exists when the claim is true.

| Regime | Negatives settled by | Complete? |
|---|---|---|
| Finite (census, SAT, bounded search) | Exhaustive enumeration with a completeness receipt; LRAT UNSAT proofs | Yes in principle; cost is the limit |
| Algebraically closed fields (ℂ-like) | Nullstellensatz certificates (unit-ideal cofactors) | Yes |
| Real closed fields (ℝ-like), polynomial problems | Positivstellensatz / SOS certificates | Yes |
| Rational and integer points (arithmetic) | Only special certificate types (local obstructions, descent, …) | **No.** Undecidable over ℤ; open over ℚ |

So GP is *nearly complete* in the first three regimes and *sound but partial* in arithmetic. In arithmetic, many true negatives will never be held. That is correct behaviour, and GP must say so.

### 3.3 Honest characterization (use it in the SPEC-CORE preamble, the tutorial and the README)

> **GP holds what can be re-checked, and tracks exactly how far each check reaches.**
>
> - **Strong:** finite combinatorics (census, SAT, isomorphism); geometry over algebraically closed fields; real algebraic geometry.
> - **Sound but partial:** arithmetic (rational and integer points). Existence is checkable; nonexistence rarely is.
> - **Outside for now:** floating-point results (until validated-numerics checkers exist, M6); analysis and limits; infinite combinatorics.

### 3.4 The ladder is not the scope order

ℤ ⊂ ℚ ⊂ ℝ ⊂ ℂ orders number systems by *which numbers exist*. Scopes are ordered by *which rules a proof relied on*: every field, ordered fields, algebraically closed fields, characteristic 0, fields where 2 ≠ 0.

These orders do not align. ℚ and ℝ are both ordered, so an SOS certificate reaches both, while ℂ lies outside that scope despite sitting "above" them on the ladder. Characteristic is a separate axis: ordinary versus wraparound arithmetic.

**Documentation rule:** never present the ladder as the scope picture. The correct one-liner is: *a warrant reaches every world where the rules it used are true.*

---

## 4. The checkability line (DECIDED)

**GP's boundary is drawn by checkability, not by topic.**

- Search anywhere, with any tool: CAS, SAT, numerics, LLM guesses.
- Hold only what an admitted checker can replay.
- Everything else stays visible as `Asserted`. It is part of the frontier, never the foundation.

**Ambition grows by admitting checkers, not by widening what the kernel trusts.** The growth order below ranks by real work unlocked per unit of checker complexity:

1. census (Phase 4);
2. real algebraic numbers (§8.8);
3. validated numerics (M6, after G5);
4. selected arithmetic certificate types, much later and only if a campaign needs them.

---

## 5. Decisions

| # | Decision | Tag |
|---|---|---|
| D1 | The core concept is **claim / scope / warrant**, mechanized to deliver the §2 guarantee. We accept narrower applicability in exchange for being knowable and workable. | DECIDED |
| D2 | **Full rework** under the Grand Portage name, developed in a fresh private working repo through G4. GP v0.37 is frozen as oracle, fixture source and counterexample library. Knowledge is ported, not code. How GP 0.50 lands publicly is Will's call at G5. | DECIDED |
| D3 | The **kernel is written in Lean 4**: executable, Mathlib-free, with soundness proved about the actual code. The pivot condition is in Phase 0c. | DECIDED (with pivot) |
| D4 | Layering: **kernel → profiles → moves and checkers → adapters → surfaces**. The boundary test and promotion rule are in §6.4. | DECIDED |
| D5 | Shape: a **Datalog-shaped kernel** (facts and rules folded to a fixpoint over an append-only log), an **Elm-shaped runtime**, and a small declarative **campaign statement** as the user-facing surface. | DECIDED |
| D6 | **LCF discipline:** only admitted checkers and admitted rules mint warrants. Declarations, prose, citations and assertions are visible but never held. | DECIDED |
| D7 | The **must-refuse / must-accept corpus comes first**; no kernel code is written before it. | DECIDED |
| D8 | **Kernel budget**, split three ways: core logic (types, fold, `held`, K1–K6, why-not query) ≤ ~500 lines; log serialization and decoding (also trusted) ≤ ~400; soundness statement plus its definitions ≤ ~80; proofs uncapped. **Tripwire:** crossing 1.5× any line means stop and report; the kernel never grows quietly. Each admitted checker ≤ ~300 lines or a written justification. (For calibration, HOL Light's LCF kernel is about 500 lines of OCaml.) | DECIDED (numbers adjustable by Will) |
| D9 | **Promotion rule:** a concept enters the kernel only after two profiles need it independently. | DECIDED |
| D10 | Profile order: a **minimal algebraic profile first** (the oracle covers it), then a **census profile immediately after** (the portability test). | DECIDED |
| D11 | **Log discipline:** strictly append-only; retraction and supersession are new facts; merge is concatenation plus re-fold. | DECIDED |
| D12 | **Statement languages:** no general-purpose formula language is invented. Each profile has a small, specified statement AST with a Lean elaboration target, **aligned with Mathlib definitions wherever one exists**. Lean is the gold standard for goal meaning. | WORKING |
| D13 | **Scope is context; region is statement** (§8.1). | WORKING (the most likely pivot point) |
| D14 | **Checkability line** (§4): hold only what an admitted checker replays; ambition grows by admitting checkers. | DECIDED |
| D15 | **Adopt before build.** For any component in the §7 map marked *adopt*, building our own requires a written reason in `PRIOR-ART.md` or a phase report. Adoption is never automatic either: each adoption must fit the core and the not-list. | DECIDED |
| D16 | **Mathlib coupling stays one layer up.** The kernel never imports Mathlib. Any Mathlib-backed scope vocabulary, statement elaboration or Lean-proved warrant lives in a binding layer with pinned versions. | DECIDED |
| D17 | **Earned-but-unclaimed implications** are computed by the kernel fixpoint and presented by surfaces. The kernel adds no rule for them; they are consequences of K2 and K3. | WORKING |
| D18 | **Interoperability by default.** At every boundary (goal statements in, warrants in, results out), GP reads and writes existing community formats and uses existing tools, rather than inventing its own. Interop is implemented in adapters, surfaces and the binding layer, never in the kernel. Each interop target must serve a §2 guarantee piece (D15). GP aims to be a good *component* of others' efforts, not a rival platform. | DECIDED |

---
## 6. Core concepts

### 6.1 Claim / scope / warrant

A **claim** has three parts:

- **statement**: what is claimed, as a profile AST.
- **scope**: the class of *contexts* (the world) across which it is claimed. Examples: every field of characteristic 0; ordered fields; ℝ with a selected root; "assuming census receipt R"; "assuming GRH".
- **warrant**: what backs it. One of:
  - `Checked(checker, receipt, inputs)`
  - `Derived(rule, premises)`
  - `Cited(ref)`
  - `Asserted`
  - `Absent(reason)` (timeouts, unfinished runs)

**Meaning:** for every context c in ⟦scope⟧, the statement holds in c.

`Checked` covers both admitted external checkers and, if G1 decides so, Lean-proved theorems. A Lean theorem is simply a checker whose reach is read from the theorem's hypotheses (§7.3, decision 1).

Vocabulary lineage: Toulmin (claim, warrant; his "qualifier" is our scope). Mechanization lineage: LCF kernels, proof-carrying code, provenance semirings, build systems (Appendix G).

### 6.2 Held

A claim is **held** when three conditions are met:

- its warrant is `Checked` or `Derived`;
- every input hash is current;
- the warrant's reach covers the claim's scope.

A claim that is not held is either an **obligation** (warrant missing or insufficient) or **history** (stale or superseded). Only held claims can serve as premises of held claims.

### 6.3 Kernel rules (WORKING; the complete list)

- **K1 — Receipt.** An admitted checker validates a receipt for `(φ, S)`, the receipt's reach ⊒ S, and the inputs are fresh ⇒ `(φ, S)` is held.
- **K2 — Weakening.** `(φ, S)` held and S′ ⊑ S ⇒ `(φ, S′)` held. This is sound for every statement because scope quantifies universally over contexts (§8.1).
- **K3 — Admitted derivation.** Admitted rule r, premises held at S, and r's side-checker validates ⇒ the conclusion is held at S. Covers, case splits, statement transports (inclusion, image, equivalence) and conjunction are all K3 instances; the certificates for them are supplied by profile checkers. There is no separate cover rule.
- **K4 — Freshness.** A warrant binds input hashes: statement, scope, model data, and checker id and version. Any mismatch means not held, with history retained.
- **K5 — No minting from `Cited`, `Asserted` or `Absent`.** Ever.
- **K6 — Log.** The log is append-only; the fold is deterministic and total; retraction is a fact.
- **Inconsistency (a finding, not a rule).** If `(φ, S)` and a profile-declared contradiction of φ are both held at overlapping scopes, the kernel reports an inconsistency and halts promotion. The usual causes are an unsound checker or wrong inputs.

Everything else is derived surface: frontiers, obligations, explanations, tailings and earned-but-unclaimed lists.

### 6.4 Layers and the boundary test

| Layer | Contains | Trust | Change rate |
|---|---|---|---|
| **Kernel** (Lean, Mathlib-free) | claim/scope/warrant types, `held`, K1–K6, fold, soundness theorem | the only global TCB | almost never |
| **Binding layer** (Lean + pinned Mathlib; D16) | Mathlib-backed scope vocabulary, statement elaboration, Lean-proved warrants, if adopted at G1 | soundness-critical; reviewed as a unit | rarely |
| **Profiles** | statement AST, context/scope types with a decidable ⊑, claim kinds, contradiction relation, statement-level rules | soundness-critical per profile | occasionally |
| **Moves and checkers** | operations plus the checkers that admit their output, each declaring its reach | each checker is its own small TCB, admitted individually | often; this is where growth happens |
| **Adapters** | CAS, SAT, nauty, numerics, agents, lanes, dispatch | untrusted; can only *submit receipts* | freely |
| **Surfaces** | frontier, `explain`, campaign statement, earned-but-unclaimed, tailings export | derived; can never affect `held` | freely |

**Boundary test.** Ask two questions: if this had a bug, could a false claim become held? And is it domain-independent?

- yes and yes → kernel;
- yes and no → binding layer, profile, or checker;
- no → adapter or surface.

**Promotion rule (D9).** A concept moves into the kernel only when two profiles need it independently. Log each promotion in `PROMOTIONS.md`.

### 6.5 Shape

- **Kernel.** Datalog-shaped: facts plus rules folded to a fixpoint over the log. "What is missing for the goal?" is a why-not provenance query. "What have I earned that I didn't claim?" is the same fixpoint read the other way.
- **Runtime.** Elm-shaped. `update` is the pure kernel fold. Adapters perform *commands* (run this CAS or SAT job, dispatch this lane) whose results return as *messages* carrying receipts. Nothing reaches the ledger except through `update`.
- **Campaign statement.** The analogue of Elm's `main`: goal claim, profiles, admitted moves, done-condition. The frontier, refusals, tailings and earned-but-unclaimed lists are derived from it (Appendix E).
- **Earned-but-unclaimed (D17).** Surfaces list consequences that are held but were never claimed, subject to two rules:
  - rank them by relevance to open obligations and the goal;
  - cap them by default.

  The failure mode to avoid is flooding. A consequence nobody asked about is noise unless it discharges something.
- **Move admission.** A new move starts untrusted: its outputs are `Asserted`. Once its checker is admitted, it can mint held claims. This is both the escape hatch and the extension path, and it should be dignified.
- **Obligation tagging** (surface). Each open obligation is marked either **closable in principle** (a complete certificate system exists in its regime, §3.2, so more compute could settle it) or **no complete method** (arithmetic-type negatives). This tells the user whether to spend compute or change approach.

### 6.6 Why the rules are what they are (orientation)

Logic and geometry are linked by a dictionary that loses information in a controlled way. V sends equations to their solution set. I sends a set to all equations vanishing on it. Round trips drift in two ways:

- **points → equations → points** gives the **closure**. Polynomials cannot see holes, and a closure point need not lift (Chevalley; the IMAGE_CLOSURE refusal).
- **equations → points → equations** gives the **radical**. Points cannot see multiplicity: V(x²) = V(x), yet x ≠ 0 in k[x]/(x²).

The same shape appears for predicates along a map (∃-image and ∀-preimage are adjoint, which is where the NONEMPTY/EMPTY variance comes from) and for axioms ↔ structures. A certificate's reach is the class of structures satisfying the axioms its proof used. Nullstellensatz certificates are complete over algebraically closed fields and Positivstellensatz certificates over real closed fields; no such system exists for ℚ. The system is bookkeeping for which round-trip losses you have incurred and which claims survive them.

---

## 7. Adopt, imitate, don't bolt on

### 7.1 Where GP sits (WORKING; 0e confirms or corrects)

No existing project combines the §2 guarantee, multiple worlds, campaign-scale pre-formal state and automated carrying. Each neighbour holds a piece, and several of them were built by working mathematicians:

- **LMFDB** (professional number theorists). Every section has *source*, *reliability* and *completeness* pages covering how the data was computed, which conjectures or heuristics it assumed, and which finite subset of an infinite family it covers. It distinguishes provably determined "Rational points" from merely "Known rational points". A June 2026 talk, *Bridging Lean and the LMFDB* (Roe), sets the goal of giving users reasons to trust data. It notes that there is currently no uniform standard across sections, hopes for per-page Lean downloads proving a subset of the claims, and names **completeness claims as a challenge**. This is claim/scope/warrant, wanted by mathematicians and currently done by hand. It is the most credible fellow-traveller community.
- **Magma** has explicit rigor tiers for class-group computations: formalizable, rigorous, GRH-conditional and heuristic. Proven results are the default, and conditional ones are opt-in. **PARI** is the counter-example: by default it uses a class-group bound *below* even the GRH-proven one, which its developers call "Bach constant cheating". Scope honesty exists in computer algebra systems, but it is per function and easy to miss (corpus seed A27).
- **Lean/Mathlib** has an Elm-grade guarantee, but only in one world at a time and only after full formalization. Its typeclass hypotheses already encode reach.
- **MathEvidence** (2026) checks external solver results one claim at a time: narrow capability contracts, candidate binding, fail-closed behaviour, and "no witness found" never proves universality. It has no worlds and no campaign state. It is the closest neighbour for the warrant layer.
- **MathKernel** (2026) is a multi-engine runtime with provenance. It assigns trust *levels*, capped by the weakest evidence used. It is a cautionary example: a very broad surface with minimal adoption. Imitate its evidence bundles, never its trust ladder or its scope sprawl.
- **Logipedia/Dedukti** labels each proof with the theories, and hence the proof systems, in which it can be used, by tracking which axioms it relies on. That is reach, but over proof systems rather than number systems, and it is not operational.
- **Trocq** (Coq) builds a hierarchy of algebraic structures on relations, so a transport step records how much structure it needs. It works with relations that are not isomorphisms and unifies several earlier proof-transfer tools. **Isabelle Transfer** and Lean's **`norm_cast`** are more everyday versions. Together they are the model for GP's relation rules.
- **Formal Conjectures** (Google DeepMind) is a Lean library of open-problem statements: about 2,600 problems, over 1,000 of them open. It explicitly flags misformalization risk and invites fixes. Its `@[formal_proof]` attribute records where a solution lives: in the repo, elsewhere in Lean, or in another proof system.
- **Lean blueprint / LeanArchitect** (ITP 2026) builds campaign graphs by extracting blueprint data directly from Lean, and has surfaced latent inconsistencies in existing blueprints. It covers only claims headed for full formalization. **LeanMarathon** (2026) builds on LeanArchitect's metadata format and adds a reviewer that compares the canonical statement, the prose statement and the Lean type.

**GP's claimed territory** is two claims, both to be tested:

1. warrants carry *where* (a scope), not *how much* (a level);
2. campaign-level, mostly pre-formal state, with automated, honest carrying between worlds, *including completeness and cover claims*.

LMFDB's own naming of completeness as the hard part suggests claim 2 is both open and wanted.

If 0e finds either claim already covered, contribute to that project rather than rebuild (D15, D18). Either way, identify which communities would want GP's output as a component.

### 7.2 Map

| Core piece | Adopt (expert-built) | Imitate (pattern, not code) |
|---|---|---|
| Trust discipline | Lean's kernel | LCF: only checkers mint warrants |
| Scope vocabulary | Mathlib's typeclass hierarchy (fields, `CharZero`, `CharP K p`, `IsAlgClosed`, ordered-field classes). *Pending G1 decision 3.* | — |
| Algebra warrants | Mathlib tactics as checkers: `linear_combination` for ideal-membership certificates; the `polyrith` pattern (external search, Lean check). Possibly MathEvidence's checkers. *Pending G1 decision 2.* | MathEvidence's candidate binding and fail-closed policy |
| Carrying across worlds | Mathlib transfer theorems (e.g. Lefschetz-style char 0 ↔ large-p results in its model theory); `norm_cast` for ℕ→ℤ→ℚ→ℝ | Trocq / Isabelle Transfer: relations annotated with which direction is sound |
| Census warrants | Lean's verified LRAT checker (the one behind `bv_decide`) or cake_lpr; nauty for generation | The empty-hexagon verification: prove the encoding correct, check the UNSAT proof |
| Exact reals | The Isabelle AFP algebraic-numbers development as a reference implementation | Polynomial plus isolating-interval receipts (§8.8) |
| Freshness | Possibly Lake's own build hashing | "Build Systems à la Carte" traces |
| Campaign surface | Lean blueprint / LeanArchitect conventions where compatible | The ETP's pooled implication graph |
| Goal statements | Formal Conjectures statements, when one exists for the campaign's problem | Its misformalization-fix process |
| Meaning audit (M5) | — | LeanMarathon's reviewer comparing canonical statement, prose statement and Lean type |
| Relation rules (K3) | Mathlib's transfer lemmas and `norm_cast` | Trocq's hierarchy of relation structure |
| Result export / tailings | LMFDB-style source / reliability / completeness pages as the target shape | Magma's rigor tiers as the vocabulary for conditional results (mapped to scopes, never used as a trust ladder) |
| Earned-but-unclaimed | — | ETP-style implication closure; Datalog fixpoints |
| Validated numerics (M6, later) | alphaCertified; verified interval libraries | — |

### 7.3 Three adoption decisions for G1 (OPEN; 0e produces the evidence)

1. **Warrant form.** Is a warrant (a) a Lean theorem whose typeclass hypotheses *are* its scope, (b) an admitted-checker receipt with checker-declared reach, or (c) both, with one scope language?
   - The working lean is (c). Receipts can be upgraded to Lean theorems over time; the certificate→Lean emitter belongs here.
   - Evidence needed: the Lean elaboration cost on corpus cases, and the share of incidents whose warrants are naturally Lean-provable versus receipt-only.
2. **Checker layer.** For exact algebra and linear algebra, do we *adopt* MathEvidence's capability checkers, *imitate* its contract and binding discipline, or *build*?
   - Evidence needed: licence (it is Apache-2.0); fit with our reach and scope model; Lean version compatibility (it pins an older toolchain); maturity; whether its fail-closed scope matches our corpus; and willingness to coordinate with its author.
3. **Scope vocabulary.** Do we use Mathlib's hierarchy as the canonical names for scopes and reach, retiring GP's hand-built requirement profiles (U/O/Z, CHAR_0, ORDERED)?
   - The working lean is yes, via the binding layer (D16).
   - Evidence needed: M2's mapping table, and whether every corpus scope has a clean Mathlib counterpart.

### 7.4 Don't bolt on

- **Trust ladders** (e.g. MathKernel's formal > exact > interval > numeric > heuristic). They answer "how much should I believe this?" GP's question is "where does this hold?" A trust ladder may inform `explain` wording, but it never feeds `held`.
- **Institution machinery** (Hets) as anything user-facing. It is fine for M1; it is hopeless as UX.
- **CAS results inside the TCB.** Search stays external; only replay is trusted.
- **General computer algebra reimplemented in Lean.** Replay checkers only.
- **Anything adopted only because it is impressive.** Every adoption answers "which part of the §2 guarantee does this serve?"

**Risk flag: Mathlib coupling.** Mathlib changes constantly. Pin versions in the binding layer, keep the kernel Mathlib-free (D16), and treat a Mathlib upgrade as a checker version bump. That stales warrants per K4, and re-checking should be cheap.

### 7.5 Interop surfaces (WORKING; D18)

The formats GP should **consume**:

- Lean/Mathlib statements and theorems (via the binding layer);
- Formal Conjectures goal statements and `@[formal_proof]` pointers;
- LRAT / DRAT proofs;
- MathEvidence evidence bundles, if G1 decision 2 adopts or imitates it;
- nauty / graph6 canonical forms for census objects.

The formats GP should **produce**:

- Lean statements, plus proofs where a warrant is Lean-proved;
- LRAT for census negatives;
- tailings as LMFDB-style records with *source* (moves and checkers used), *reliability* (the scope, including conditional hypotheses such as GRH, and the TCB), and *completeness* (the cover and its receipt);
- blueprint-compatible dependency data where it is cheap (LeanArchitect conventions).

**Rule.** Interop code lives in adapters, surfaces or the binding layer. The kernel never learns a foreign format.

**Rule.** A GP-specific format at a boundary where a community format exists needs a written reason in `PRIOR-ART.md`.

---

## 8. Working hypotheses and open questions

### 8.1 Scope versus statement (WORKING; most likely pivot)

- **Scope is context:** the class of structures or assumptions across which a claim is asserted. This covers coefficient field class, point universe, characteristic, selected embedding, encoding assumptions, and conditional hypotheses.
- **Region is statement:** which objects the claim is about. This covers the ideal and variables, which n, which symmetry sector, and which branch of a case split.

**Why.** Scope quantified universally makes K2 sound for every claim polarity. If region lived in scope, weakening would need per-kind variance rules, and GP's ∃/∀ table would leak into the kernel. Under the split:

- object-changing transports (inclusion, image, equivalence) are K3 rules certified by relation checkers;
- context-changing ones (base extension, specialization) are reach questions under K1 and K2.

This matches GP v0.37's own table, where BASE_EXTENSION and SPECIALIZATION behave differently from every other row.

If G1 decision 3 goes to Mathlib, a scope is concretely a typeclass context (for example, "K is a field of characteristic 0"), and the split becomes "hypotheses vs. conclusion", which is a natural fit.

**Evidence to collect.** For each incident, record whether it is a scope error or a region error, and note unnatural cases. Watch especially for symmetry sectors, "up to isomorphism", SAT encodings, and conditional claims.

**Pivot trigger.** More than about three real incidents that cannot be expressed under the split, or a profile that needs region-dependent weakening. Stop and report with examples.

### 8.2 Meaning (OPEN; named blind spot)

Claim/scope/warrant checks consistency, not whether a statement means what the campaign needs. JC examples: the "window" naming conflation, and the imported γ ∈ {2,3} assumption. A 2026 audit of Lean-formalized AI results makes the general point: a kernel check establishes the encoded proposition, and humans must still establish its intended meaning.

Stance:

- statement ASTs have Lean elaboration targets (D12);
- every campaign goal is meaning-audited once (M5): use a Formal Conjectures statement when one exists, and imitate LeanMarathon's reviewer;
- the sweep **counts meaning incidents** (G0).

### 8.3 Claim kinds (OPEN)

The working lean is that the kernel knows statements and a profile-supplied contradiction relation, and profiles own the claim kinds:

- algebraic: EMPTY, NONEMPTY (witness or existential), PREDICATE, IDENTITY;
- census: EXISTS, NONE, COUNT = k up to isomorphism, EXHAUSTIVE.

Promote only under D9.

### 8.4 Relation transport (OPEN)

The ∃/∀ variance under a relation (total, surjective) is domain-independent. The working lean is to keep it as algebraic-profile K3 rules, imitating Trocq/Transfer's direction-annotated relations. Promote it if census reimplements it.

### 8.5 Checker admission and versioning (OPEN; propose a policy)

Starting policy:

- **Admission** requires either two independent consumers, or one consumer plus a stated soundness argument (a Lean proof where feasible) plus adversarial controls.
- **Version bumps** (including a Mathlib bump for binding-layer checkers) stale every warrant the checker minted.
- **`TCB.md`** records each checker's implementation (Lean-internal, verified external such as cake_lpr, or trusted external such as nauty) and its reach.

### 8.6 External checkers (WORKING)

Receipts from admitted external checkers run out of process. Their TCB status is visible in the manifest and in `explain`. Over time, soundness-critical checkers are ported into Lean or replaced by adopted Lean tactics. Search and production are never in the TCB: Gröbner bases are computed externally, and only cofactor identities are replayed.

### 8.7 The profile term (OPEN; Will decides)

"Profile" is defensible (in standards language it means a framework specialized to a domain) but says nothing about what's inside. The leading alternative is "domain"; GP's old `coefficient_domain` field would need renaming. Use "profile" until Will decides.

### 8.8 Exact reals are real algebraic numbers (WORKING; affects Phase 3 and the u(22) slice)

Arbitrary reals cannot be stored exactly. What can be stored is a pair: **(a polynomial with rational coefficients, an isolating interval with rational endpoints)**. For example, √2 is "the root of x² − 2 in (1, 2)". This covers everything polynomial problems produce. It excludes π, e, analysis, and floats.

The checker replays three facts:

1. the polynomial has a root in the interval;
2. the interval isolates exactly one root;
3. the claimed equations hold at the point, checked by exact arithmetic in the number field.

The selected root is part of the **statement**, not the scope (§8.1). This is Cloquet's proposed selected-real point receipt. Use the Isabelle AFP algebraic-numbers development as the reference for algorithms and pitfalls.

---
## 9. Work plan

Each phase ends with `reports/PHASE-n-REPORT.md` covering:

- what was built;
- each gate item marked PASS or FAIL, with evidence;
- surprises;
- evidence for or against WORKING items;
- questions for Will.

### Phase 0 — Groundwork (in progress)

Five lanes. Lanes 0a–0d are unchanged from revision 1; 0e is new. No kernel code is written until 0a and 0b are done.

**0a. Must-refuse / must-accept corpus from GP v0.37** (unchanged)

1. Extract every counterexample, trap, confession and regression from GP's tests, its docs (SPEC, DESIGN, REVIEW, the review/ release notes, the lean/ theory ledger) and its fixtures.
2. Encode each as a *minimal* case with five fields: situation, attempted conclusion, expected verdict (REFUSE/ACCEPT), reason, and source pointer (file:line or test name).
3. Use a neutral JSON schema, not GP's graph format, so the corpus outlives both systems.
4. Start from the Appendix A seeds. Aim for completeness over GP's history.
5. Include **must-accept** positive controls, so that refusing everything cannot pass.
6. Run each case against the v0.37 oracle and record its verdict. Two disagreements are already known: A3 and A8.
7. *(New in rev 2, optional.)* Where a case has a natural "earned-but-unclaimed" consequence (for example, a certificate whose reach is wider than the claim), note it in an `also_earned` field. These seed tests for D17.

**0b. Campaign near-miss sweep and corpus harvest** (unchanged)

1. Follow the protocol in Appendix C.
2. Cover every repo in `SWEEP-SOURCES.md` (Appendix H), in priority order. JC is first (the three shipped errors); GP's own private workspace is second (the tool as a campaign that had incidents).
3. **Do not start until Will has filled in `SWEEP-SOURCES.md`.** Clones are read-only. Private material stays local. `corpus/harvest/` is gitignored and classified private for any public snapshot.
4. Produce `corpus/incidents/*.json` (Appendix B schema) and `INCIDENT-INVENTORY.md` with counts by class, origin and campaign.
5. Harvest verbatim exports and receipts into `corpus/harvest/<campaign>/`, with a manifest and SHA-256 hashes.
6. **Never backfill or "repair" harvested data.** Recovery products are labelled separately.

**0c. Lean feasibility spike** (time-boxed to one token cycle, roughly 2 agent-days)

1. Pin a Lean 4 toolchain and create a Lake project.
2. Build an executable that reads a JSONL log (`Lean.Data.Json`) and folds a toy claim set with K1, K2 and K4.
3. Invoke one external checker via `IO.Process` and record it in `TCB.md`.
4. Implement one tiny computable sparse polynomial over ℚ with a cofactor-replay check.
5. Report build times, ergonomics and pain points.
6. Evaluate whether Lean 4's built-in verified LRAT checker (the one behind `bv_decide`) is usable for census UNSAT receipts.
7. *(New in rev 2.)* In a **separate** Lake package that depends on pinned Mathlib, elaborate two corpus cases as Mathlib-stated lemmas (for example, a unit-ideal emptiness over `[Field K] [CharZero K]`). Record elaboration and check times. This is evidence for G1 decisions 1 and 3; it is not a commitment to either.

**Pivot for D3.** If Lean plumbing is still blocking progress after one further token cycle beyond the spike, or the fold is impractically slow on the harvested corpus, stop and propose one of two fallbacks: a Python kernel with the spec and soundness proof in Lean over a model of it, or a Lean kernel with Python adapters. Will decides.

**0d. GP v0.37 freeze housekeeping** (unchanged; prepare only, do not push without Will)

1. Tag v0.37.0 as frozen.
2. Prepare a v0.37.1 **doc-only** patch:
   - fix the 17 mojibake em-dashes (`â€”`) in README.md;
   - fix the SPEC.md status block (it still says graph format 7 / kernel epoch 11 / "eleven live sessions");
   - remove or annotate public links to private files (KILL-CRITERIA.md, HISTORY/);
   - add this banner, verbatim, at the top of README.md:

     > *Frozen at v0.37.0. This repository remains the reference implementation and fixture source for a successor now in design. No further feature development here.*
3. Record, but do not fix, two known kernel issues as KNOWN-ISSUES:
   - **Containment conflation.** The NOT_BY_IDEAL discharge advises establishing an edge by radical membership. That earns the point cells only; the IDENTITY cells on NECESSARY_CONDITION/AGAINST and RESTRICTION need ideal containment. The V(x²)→V(x) probe shows the false licence that following the advice would open.
   - **SPECIALIZATION conservatism mislabelled as a theorem.** A p-integral unit-ideal certificate licenses EMPTY ALONG (char 0 → char p), and a p-integral witness licenses NONEMPTY ALONG.

**0e. Prior-art review** (new; time-boxed to one token cycle; can run in parallel with 0a and 0b)

1. Work through the reading list in Appendix G.2. For each item, answer its stated question with primary sources: the repos, papers and docs themselves.
2. Produce `PRIOR-ART.md` containing:
   - a table with one row per item: **adopt / imitate / differ / ignore**, a one-line reason, and the §2 guarantee piece it serves;
   - a recommendation, with evidence, on each of the three G1 decisions (§7.3);
   - a check of GP's two territory claims (§7.1): **covered / partly covered / not found**, with citations;
   - any project whose author seems worth contacting (MathEvidence is the obvious candidate). Will makes any contact.
3. **Never copy code** without recording its licence in `PRIOR-ART.md`.

**Gate G0**

- The back-brief (or the latest BACKBRIEF-REVn) is approved.
- The 0a corpus covers GP's history, source-pointed, with oracle verdicts recorded.
- The 0b inventory covers every repo in `SWEEP-SOURCES.md`.
- The 0c spike report is written, including the Mathlib elaboration timing.
- `PRIOR-ART.md` from 0e is written.
- **Decision point.** Report before Phase 1 if MEANING alone accounts for ≥ ~30% of **high-cost** incidents, or MEANING plus ADAPTER for ≥ ~40% (cost classes are defined in Appendix B); either result would mean the core is aimed at the wrong problem. **Small-n rule:** with fewer than ~25 incidents in total, report qualitatively instead.
- **Territory check.** If 0e finds both §7.1 claims already covered, report before Phase 1: contributing elsewhere may beat building. In every case, `PRIOR-ART.md` names which communities would want GP's output as a component (LMFDB is the leading candidate) and what format they would need.

### Phase 1 — Core spec and adoption decisions (mostly thinking)

1. Write `SPEC-CORE.md`, one page:
   - open with the §2.1 guarantee and the §3.3 characterization;
   - then the types (§6.1), `held`, K1–K6, the inconsistency finding, the profile interface, and the scope/region decision with evidence from 0b.
2. Write the Lean **soundness statement** (Appendix D). It must elaborate; the proof may still be `sorry` at this gate.
3. **Decide the three G1 adoption questions** (§7.3). Write one paragraph each with evidence from 0c and 0e. Will signs off.
4. **Paper expressiveness scoring.** For each non-MEANING incident, record whether the core can express the situation and whether it would have refused the error. Also record, where relevant, what the earned-but-unclaimed view would have surfaced.

**Gate G1**

- The spec fits on one page and opens with the guarantee.
- The soundness statement elaborates.
- At least ~80% of non-MEANING incidents are expressible, and every inexpressible *high-cost* incident has a written reason (report qualitatively under the small-n rule).
- The scope/region split holds, or the pivot is reported.
- The three adoption decisions are made, evidenced, and signed off.

### Phase 2 — Kernel

1. Implement in Lean, Mathlib-free:
   - the log fold, `held`, K1–K6 and the inconsistency finding;
   - `TCB.md` integration;
   - the why-not query ("what's missing for claim X");
   - the earned query ("what is held that no one claimed, ranked by the obligations it touches").
2. Prove soundness with no `sorry`, against the abstract profile interface, under explicit checker-soundness and rule-soundness hypotheses.
3. Write property tests for fold determinism, merge = concatenation + re-fold, retraction, and staleness.

**Gate G2**

- The D8 budget holds: logic ≤ ~500 lines, serialization and decoding ≤ ~400, soundness statement plus dependencies ≤ ~80, and no tripwire crossed.
- Soundness is proved.
- Property tests pass.
- Every kernel design choice traces to a corpus case or an incident.

### Phase 3 — Minimal algebraic profile

1. Define the statement AST: ideals over named variables with ℚ coefficients, claim kinds, and a witness-point form. Align with Mathlib definitions per D12.
2. Define contexts and scopes: field classes, point universe, characteristic. Name them per the G1 decision 3 outcome, mapped to Mathlib classes if adopted.
3. Build checkers. All are *replay* checkers; search stays external. **Per D15, adopt first:** Mathlib tactics or MathEvidence checkers where G1 chose them, and build only with a reason.
   - cofactor replay (membership, unit ideal);
   - witness substitution;
   - ideal-level containment, **kept separate from point-level containment**;
   - SOS contradiction replay (ordered reach);
   - p-integrality (specialization reach);
   - selected real algebraic points (§8.8), if the corpus or the u(22) slice needs them;
   - exact image/elimination replay only if the corpus needs it.
4. Build K3 rules for object-changing relations (inclusion, image, equivalence), with direction annotations in the style of Trocq and Transfer.
5. Run the full 0a corpus, including any `also_earned` expectations. Differential-test against the oracle on GP's fixtures: JC(2), matroid, gamma_window, the DK retrodiction, and the ARR15 slices.

**Gate G3**

- 100% of must-refuse cases are refused; 100% of must-accept cases are accepted.
- Every oracle disagreement is triaged as a GP bug, a core bug, or an expressiveness loss.
- **The corpus is the spec.** Correcting an expected verdict needs Will's sign-off and an entry in `corpus/CHANGES.md`; never edit it quietly.
- The kernel is unchanged since G2 apart from logged fixes.

### Phase 4 — Census profile (the portability test)

1. Define the statement AST:
   - finite families of combinatorial objects (graphs, incidence structures, combinatorially described configurations) with explicit size parameters;
   - "up to isomorphism" as an explicit statement construct, not a context.
2. Define claim kinds: at least EXISTS, NONE, COUNT = k up to isomorphism, and EXHAUSTIVE.
3. Build moves and checkers, following the §7.2 census row:
   - isomorphism and automorphism checks (a permutation is the certificate);
   - forbidden-substructure exclusion (an embedding is the witness);
   - UNSAT via LRAT (Lean-internal verified checker or cake_lpr);
   - SAT via model check;
   - **encoding correctness** as the central meaning risk (M4). Imitate the empty-hexagon approach: prove the encoding correct, or cross-validate on small cases with a documented TCB;
   - enumeration completeness (M4 options);
   - symmetry-breaking soundness: it preserves existence up to isomorphism, not counts, and only when the breaking predicate is complete.
4. Build a census must-refuse set covering:
   - a timeout read as UNSAT;
   - "none found up to n" read as "none exist";
   - an unsound symmetry break used for counts;
   - a non-exhaustive cover;
   - an unchecked LRAT proof;
   - a floating-point "verification";
   - an encoding without a correctness warrant.
5. Retrodict at least one DK slice, such as the V4-sector census counts that Lu's cell counts matched independently. This is a natural two-route (+) warrant example.

**Gate G4**

- The census profile lands with **zero kernel changes** (bug fixes excepted and logged) or only D9-justified, logged promotions.
- All census traps are refused.
- The DK slice reproduces.

### Phase 5 — Pilot and comparison

1. Define a minimal campaign statement format (Appendix E) plus derived views:
   - the frontier, with obligation tagging (§6.5);
   - the earned-but-unclaimed list (ranked and capped);
   - a tailings export in the §7.5 LMFDB-style shape (source / reliability / completeness).
2. **Tutorial campaign.** A fifteen-minute campaign in one profile:
   - an agent makes a classic overclaim;
   - it gets one good refusal, fixes it, and lands a small honest result plus a tailing;
   - it is shown one earned-but-unclaimed consequence.

   Write it as the Elm-guide-style first page of the future README, stating §3.3 plainly.
3. **u(22) slice.** Run a real, bounded slice of the Highway 61 campaign on the new core (census + real algebraic).
4. **Comparative arms.** Twelve incidents from the inventory, stratified by class, each run through three arms with separate agents. Record effort (agent turns, wall time, tokens where available).
   - (a) the new core;
   - (b) Lean plus blueprint (every claim a Lean statement, tagged axioms for external results);
   - (c) notebook plus checker scripts plus CI (the DK-style baseline).

**Gate G5**

- A fresh agent runs the tutorial from the campaign statement alone.
- **The Elm test:** Will reads the u(22) ledger cold and states what is held, open, refused and earned-but-unclaimed in under 10 minutes.
- **Comparative results** (directional, not statistical, at n = 12):
  - **Beats the notebook (c):** at least 2 more catches of the 12 at ≤ 1.5× the effort, *or* equal catches at ≤ 0.75× the effort.
  - **Not dominated by Lean (b) on errors:** no more than 1 fewer catch than (b).
  - **Beats Lean (b) on workability:** time to first held claim, and agent turns per resolved obligation.

**If the core does not beat the notebook baseline, stop and reconsider. Do not add features to rescue it.**

---

## 10. Math lanes

These run in parallel with the build (research agents or deep-research passes). Each produces a short note, plus Lean where feasible, and has its own stop condition.

- **M1 — Scope semantics.** Formalize scope as a class of contexts with a decidable, sound ⊑, and state kernel soundness that way. Stress-test the scope/region split (§8.1) on algebraic, census, real-realizability and conditional examples. Use institution theory as a check, not as a design.
  - *Stop* when the split survives ~10 hard examples, or a counterexample is written up.
- **M2 — Reach in Mathlib's vocabulary** (refocused). Map GP's reach vocabulary (U = nontrivial ring, O = ordered/SOS, Z = no zero divisors, CHAR_0, ORDERED, specific fields) to Mathlib typeclasses. Record which reach facts are *completeness* theorems (Nullstellensatz, Positivstellensatz) and which are merely sufficient. Flag any GP scope with no clean Mathlib counterpart. This is the evidence for G1 decision 3.
  - *Stop* at a table with sources.
- **M3 — Specialization reach.**
  - p-integral certificates and witnesses give conditional EMPTY/NONEMPTY transport from char 0 to char p. Build must-accept fixtures, including the demonstration that any ℚ-certificate of Fano emptiness needs a 2 in a denominator.
  - Hensel-type lifting reaches ℚ_p, not ℚ.
  - Record the Lefschetz-style family transfer as it exists in Mathlib, if it does, as an adoptable carrying rule.
  - *Stop* at fixtures plus a short note.
- **M4 — Census semantics.**
  - Symmetry-breaking soundness: existence versus counts; lex-leader completeness.
  - Enumeration-completeness warrants: trusted generator with a TCB label; independent double enumeration (the DK E5 pattern); orderly-generation certificates. Rank these by trust and cost.
  - Encoding correctness (study the empty-hexagon verification).
  - LRAT reach is "this encoding".
  - *Stop* at a ranked memo the Phase 4 builder can implement from.
- **M5 — Meaning audit protocol.** Design independent re-derivation of a goal statement from its primary source, blind to the campaign's own formalization and compared against it afterwards. **First check Formal Conjectures:** if it has the problem, use its statement, compare it against the campaign's goal, and report any misformalization upstream through their process. Imitate LeanMarathon's three-way comparison (canonical statement, prose statement, Lean type). Pilot it on the DK, Cloquet and u(22) goals, and count how many historical incidents it would have caught.
  - *Stop* at a protocol plus the three pilots.
- **M6 — Validated numerics** (new; **schedule after G5**). Interval Newton/Krawczyk and Smale's α-theory (alphaCertified) turn a float that looks like a solution into a checkable existence claim: "a real solution exists, uniquely, in this box." Such a checker is an ordinary admitted existence checker and needs no kernel change. Cautions:
  - rounding is soundness-critical: use rational intervals, or outward rounding with a documented TCB;
  - a box is not an exact point (use §8.8 when exactness matters);
  - certification says nothing about nonexistence elsewhere.
  - *Stop* at a ranked memo plus a checker spec for the Cloquet and u(22) realization moves.

---

## 11. Gates and kill criteria (pre-registered)

| Gate | Pass condition | On failure |
|---|---|---|
| G0 | Back-brief approved; 0a corpus complete and source-pointed; 0b inventory covers `SWEEP-SOURCES.md`; 0c spike report (incl. Mathlib timing); 0e `PRIOR-ART.md` | Report. Re-scope before Phase 1 if MEANING ≥ ~30% of high-cost incidents, or MEANING + ADAPTER ≥ ~40%. Under ~25 incidents, report qualitatively. If both territory claims are covered, report: contributing may beat building. Always name the candidate consumer communities |
| G1 | One-page spec opening with the guarantee; soundness statement elaborates; ≥ ~80% of non-MEANING incidents expressible, with every inexpressible high-cost incident explained; the three adoption decisions made and signed off | Report the inexpressible incidents; possible pivot on §8.1 |
| G2 | D8 budget held (logic ≤ ~500, serialization ≤ ~400, soundness statement ≤ ~80, no 1.5× tripwire); soundness proved with no `sorry`; property tests pass | Budget overrun → move logic to a profile or the binding layer, or stop and rethink. Never quietly grow the kernel |
| G3 | 100% must-refuse refused and 100% must-accept accepted; oracle disagreements triaged; corpus corrections signed off and logged | Fix, or report an expressiveness loss |
| G4 | Census profile needs zero kernel changes (bug fixes excepted and logged, or D9 promotions); census traps refused; DK slice reproduced | An unjustified kernel change means the abstraction leaks: report and stop |
| G5 | Tutorial runs from the campaign statement; Will's cold read under 10 minutes; comparative thresholds met | **Kill or rethink.** Do not add features to rescue it |

Numbers marked "~" are Will's to adjust. Record the actual values in phase reports.

---

## 12. Not-list

GP 0.50 will not:

- use confidence scores, probabilities, trust levels or trust ladders as authority;
- grant authority from declarations, prose, citations or tags;
- put a CAS, SAT solver, enumerator or search engine in the TCB (search is never authoritative; only replay is);
- reimplement general computer algebra in Lean (replay checkers only);
- build a component the §7 map says to adopt, without a written reason (D15);
- adopt anything that serves no part of the §2 guarantee;
- import Mathlib into the kernel (D16);
- expose institution-theoretic machinery to users;
- include publication, release, dossier or packet machinery in the core (these are surfaces, and only after G5);
- add edge types, claim kinds or kernel concepts without the D9 two-profile rule;
- load checkers dynamically without admission and a `TCB.md` entry;
- invent a general-purpose formula language;
- migrate old GP graphs (fixtures are converted into the neutral corpus instead);
- ship visualization, 3D explorers or MCP/hook enforcement before G5 (the hook returns later as an adapter);
- flood users with earned-but-unclaimed consequences (rank and cap by default);
- invent a GP-specific format at a boundary where a community format exists, without a written reason (D18);
- aim to become a rival platform to LMFDB, Formal Conjectures, blueprints or Mathlib. GP is meant to be a component;
- copy MathKernel-style breadth: new domains arrive as profiles through D9 and the checkability line, never by surface expansion;
- mix "we refuse this soundly", "we refuse this out of caution" and "we license this knowing better". The last category must stay empty; conservatisms are registered as data in `KNOWN-CONSERVATISM.md`.

---

## 13. Repo layout and conventions (proposal)

```
grandportage-0.50/          # private working repo through G4 (D2)
  BACKBRIEF.md / BACKBRIEF-REVn.md
  SPEC-CORE.md              # one page, Phase 1
  PRIOR-ART.md              # 0e output
  TCB.md                    # admitted checkers: implementation, reach, version
  PROMOTIONS.md             # D9 log
  KNOWN-CONSERVATISM.md     # refused-more-strictly-than-truth register (data)
  SWEEP-SOURCES.md          # Will's sweep manifest (Appendix H)
  kernel/                   # Lean 4, Mathlib-free: types, fold, held, K1–K6, soundness
  binding/                  # Lean + pinned Mathlib: scope vocabulary, elaboration, Lean-proved warrants (if adopted)
  profiles/algebraic/       # AST, contexts/scopes, checkers, K3 rules
  profiles/census/
  adapters/                 # CAS/SAT/nauty/numerics/agent runners: untrusted, submit receipts only
  surfaces/                 # frontier, explain, earned-but-unclaimed, campaign-statement tooling
  corpus/
    must/                   # must-refuse / must-accept cases (neutral JSON)
    incidents/              # Appendix B records
    harvest/<campaign>/     # verbatim exports + manifest + SHA-256; never backfilled; gitignored
    CHANGES.md              # signed-off corrections to expected verdicts
  reports/PHASE-n-REPORT.md
  oracle/                   # pinned GP v0.37.0 checkout or submodule, read-only
```

**Conventions**

- Every claim about the math cites a source: a corpus case, an incident id, a paper, or GP's file and line.
- Reports distinguish three levels: *verified here*, *reproduced from source*, and *asserted*.
- Keep prose short. GP's docs grew by confession; write the confession as a corpus case instead.

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
| A27 | Class group computed with PARI's default bound (below the GRH-proven Bach bound) | (a) Treated as unconditional; (b) treated as GRH-conditional; (c) after `bnfcertify`, or a Magma computation run with the default Proof setting | (a) and (b) REFUSE: the default bound is heuristic even under GRH. (c) ACCEPT unconditional. A GRH-proven bound would ACCEPT with scope "assuming GRH" |

**Must-accept controls to include at minimum:**

- An exact rational unit-ideal certificate carries EMPTY across base extension within its reach.
- A witness point carries NONEMPTY along an inclusion.
- EMPTY carries back along a checked ideal containment.
- A cover with a checked exhaustive partition and all branches held empty carries EMPTY to the parent.
- A verified ring isomorphism carries identities.
- An existential across an image closure carries NONEMPTY (A7b).
- The p-integral cases (A8b, A8c).

Census traps are listed in Phase 4.

**Earned-but-unclaimed seeds (optional `also_earned` field, D17):**

- A1-style certificate: if the replayed certificate uses only ring axioms, a claim made only for ℚ is also earned for every field.
- A8b: a p-integral unit-ideal certificate also earns EMPTY in characteristic p for every prime p that divides no denominator.
- A cover whose branches are all held NONE: each branch-level NONE also settles every sub-case listed under it.

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
-- The kernel is Mathlib-free (D16). If G1 adopts Mathlib's hierarchy as scope vocabulary,
-- the binding layer instantiates `Scope`/`mem` with typeclass contexts; the kernel doesn't know.
structure Profile where
  Ctx      : Type                      -- one context: a field, point universe, encoding assumptions, …
  Scope    : Type                      -- a finitely described class of contexts (a "world")
  mem      : Ctx → Scope → Prop        -- c ∈ ⟦S⟧
  le       : Scope → Scope → Bool      -- S' ⊑ S, decidable
  le_sound : ∀ S' S c, le S' S = true → mem c S' → mem c S
  Stmt     : Type
  Holds    : Stmt → Ctx → Prop         -- intended meaning
  contra   : Stmt → Stmt → Bool        -- declared contradiction (inconsistency finding)

def Means (P : Profile) (φ : P.Stmt) (S : P.Scope) : Prop :=
  ∀ c, P.mem c S → P.Holds φ c

inductive Warrant
  | checked  (checker : CheckerId) (receipt : Hash) (inputs : List Hash)   -- incl. Lean-proved, if adopted
  | derived  (rule : RuleId) (premises : List ClaimId)
  | cited    (ref : String)
  | asserted
  | absent   (reason : String)

-- A checker is sound for its reach: a valid receipt means the statement holds on the scope.
def CheckerSound (P : Profile) (k : Checker P) : Prop :=
  ∀ φ S r, k.valid φ S r = true → P.le S (k.reach r) = true → Means P φ S

-- The "no runtime errors" theorem (Phase 1: statement elaborates; Phase 2: proved):
theorem held_sound (P : Profile) (log : Log P)
    (hk : ∀ k ∈ admittedCheckers log, CheckerSound P k)
    (hr : ∀ r ∈ admittedRules log, RuleSound P r) :
    ∀ cl ∈ heldClaims (fold log), Means P cl.stmt cl.scope := by
  sorry
```

The conceptual point to preserve is that **K2 (weakening) is sound for every statement, because `Means` quantifies universally over contexts.** Anything polarity-dependent belongs in a profile's statement-level rules (K3).

Earned-but-unclaimed (D17) needs no extra theorem. Every earned claim is a held claim, so `held_sound` already covers it.

---

## Appendix E — Campaign statement sketch (u(22) / Highway 61)

```
campaign HW61
  profiles  census + exact_real
  goal      EXISTS: 22 points in ℝ² with ≥ 61 unit-distance pairs
  scope     { ℝ² }                                  -- the world; nothing to vary here
  moves
    enumerate_candidates    -- graphs on 22 vertices, ≥ 61 edges, K₂,₃-free;
                            --   warrant: enumeration-completeness receipt (M4)
    exclude_by_subgraph     -- witness: embedding of a known non-unit-distance subgraph
    exclude_by_relaxation   -- complex/real realizability certificate (necessary-condition relation)
    realize                 -- selected real algebraic coordinates (§8.8); distances replayed exactly
  done
    held(goal)
    or held(EXHAUSTIVE(candidates)) ∧ ∀ branch ∈ candidates: held(NONE(branch))
```

From this statement the kernel derives four views:

- **Frontier:** which candidates are neither realized nor excluded, and which warrants are missing. Each open obligation is tagged *closable in principle* here, because this is a finite regime.
- **Refusals:** a timeout does not exclude a branch; a numeric near-realization is not a realization (until M6, and even then only existence in a box); an exclusion without a completeness receipt does not close the cover.
- **Earned but unclaimed:** for example, "this relaxation certificate also excludes every candidate containing subgraph S, which covers 14 more branches." Ranked by how many open obligations it closes; capped by default.
- **Tailings:** every held NONE(branch), with its scope and warrant, is a publishable negative.

---

## Appendix F — Glossary

- **World**: a class of contexts; the scope of a claim.
- **Carry**: move a result between worlds, or between objects within a world, along a relation whose soundness is known.
- **Claim**: statement + scope + warrant.
- **Scope**: a world, read universally.
- **Region**: which objects the statement is about; part of the statement.
- **Warrant**: what backs a claim.
- **Held**: the warrant checks, its inputs are fresh, and its reach covers the scope.
- **Reach**: the world in which a checker's receipt is valid. For a certificate, the models of the axioms its proof uses. For a Lean theorem, its hypotheses.
- **Earned but unclaimed**: a held consequence that no one explicitly claimed.
- **Move**: an operation that produces a claim.
- **Checker**: validates a move's receipt and mints the warrant; admitted individually.
- **Profile**: a domain vocabulary (statement AST, contexts/scopes, claim kinds, statement-level rules). The term is under review; the leading alternative is "domain".
- **Binding layer**: Lean + pinned Mathlib code that ties profiles to Mathlib's vocabulary and proofs (D16).
- **TCB**: the trusted computing base, meaning the kernel, the binding layer and the admitted checkers.
- **Obligation**: a claim that is needed but not held. Tagged *closable in principle* or *no complete method*.
- **Tailing**: a held negative with explicit scope, suitable for publishing.
- **Oracle**: frozen GP v0.37.
- **Fixed rope**: an admitted move and checker that others can clip into.

---

## Appendix G — References and prior-art reading list

### G.1 Foundations

- S. Toulmin, *The Uses of Argument* (1958): claim / warrant / qualifier.
- R. Milner et al., LCF (1970s): kernel-minted theorems as an abstract type.
- G. Necula, "Proof-Carrying Code", POPL 1997.
- T. J. Green, G. Karvounarakis, V. Tannen, "Provenance Semirings", PODS 2007: warrant composition (× joint use, + independent routes).
- A. Mokhov, N. Mitchell, S. Peyton Jones, "Build Systems à la Carte", ICFP 2018: freshness and traces.
- R. McConnell, K. Mehlhorn, S. Näher, P. Schweitzer, "Certifying Algorithms", Computer Science Review 2011: outputs with checkable witnesses.
- J. Goguen, R. Burstall, institutions: the exact mathematical notion of "profile" (for M1 only).
- GP v0.37 docs: SPEC.md, DESIGN.md, REVIEW.md, lean/THEORY.md, docs/ATLAS-MAPPING-V0.md, docs/PRESERVATION-ATLAS-PROGRAM.md, docs/FOUNDATIONS-PRIOR-ART.md.

### G.2 Prior-art reading list for 0e (each item answers a stated question)

| # | Item | Question to answer |
|---|---|---|
| P1 | **MathEvidence** (github.com/fraware/MathEvidence): capability contracts, candidate binding, fail-closed checkers, untrusted CAS adapters; Apache-2.0 | Can its checkers serve as GP admitted checkers? What is their exact scope? Does its pinned Lean toolchain work with ours? Does it model reach at all? Could GP warrants *be* MathEvidence bundles plus a scope field (D18)? Adopt, imitate, or differ (G1 decision 2)? |
| P2 | **MathKernel** (github.com/Staatsgeheim/MathKernel): multi-engine runtime with per-conclusion evidence bundles and a trust ladder | What is worth imitating in its provenance design, and what exactly makes its trust ladder the wrong primitive for GP (§7.4)? |
| P3 | **Dedukti / Logipedia**: axiom-tracking and export to proof systems supporting those axioms | How does it compute and represent "axioms used"? Is there a clean analogue for GP reach? |
| P4 | **Trocq** (Cohen, Crance, Mahboubi, 2024) and **Isabelle Transfer/Lifting** (Huffman, Kunčar, 2013) | How does Trocq's hierarchy of relation structure line up with GP's per-relation carrying table (the total / surjective properties)? Is there a Lean analogue, or a Lean port in progress? What should GP's K3 relation rules imitate? |
| P5 | **Lean `norm_cast`** (Lewis, Madelaine, 2020) | How does it carry facts along ℕ→ℤ→ℚ→ℝ? Is it adoptable as-is for ladder moves in the binding layer? |
| P6 | **Mathlib certificate tactics**: `linear_combination`, the `polyrith` pattern, `bv_decide`'s LRAT checker | Which can be adopted directly as admitted checkers, and at what cost per check? |
| P7 | **Mathlib model theory**: algebraically closed fields and Lefschetz-style transfer | Which cross-world carrying rules exist as theorems, ready to adopt (with M3)? |
| P8 | **Empty-hexagon formal verification** (Subercaseaux, Nawrocki, Gallicchio, Codel, Carneiro, Heule, ITP 2024) | How was encoding correctness proved? What does Phase 4 imitate? |
| P9 | **Flyspeck** (Hales et al., Forum of Math Pi 2017) | Where did bridging computation to formal proof cost most? Which lessons carry over? |
| P10 | **Lean blueprint**; **LeanArchitect / LeanMarathon** (2026) | Which campaign-graph conventions should GP's surfaces share, so a GP campaign can emit blueprint-compatible data? How does LeanMarathon's statement reviewer work (for M5)? |
| P11 | **Equational Theories Project** (Tao et al., 2024–25) | How was implication closure computed and presented? This is the model for earned-but-unclaimed and for pooling. |
| P12 | **LMFDB reliability labels** | How do they word scope honestly for users? |
| P13 | **Hets** (Mossakowski et al., 2007) | For M1 only: anything in heterogeneous specification that sharpens the scope semantics? |
| P14 | **Isabelle AFP algebraic numbers** (Thiemann, Yamada, Joosten) | Which algorithms and pitfalls apply to §8.8 receipts? |
| P15 | **alphaCertified** (Hauenstein, Sottile) and verified interval libraries | For M6, after G5: record only, no deep dive now. |
| P16 | **LMFDB** source / reliability / completeness pages (lmfdb.org, per section) and Roe, *Bridging Lean and the LMFDB* (June 2026 talk and workshop) | What exact fields and wording do reliability and completeness pages use? Could GP warrants populate them uniformly? What is the state of the Lean-bridging effort, and who is working on it? This is the most likely consumer of GP output. |
| P17 | **Magma's paper on computing class groups and unit groups** (rigor tiers: formalizable / rigorous / GRH-conditional / heuristic); PARI `bnfinit` / `bnfcertify` docs | How do the tiers map onto GP scopes and warrants? Which conditional hypotheses need first-class scope support? Confirm the A27 seed from primary sources. |
| P18 | **Formal Conjectures** (github.com/google-deepmind/formal-conjectures; the 2026 paper) | Can its statements serve directly as GP goal statements? How do `@[formal_proof]` modes map to GP warrants? What does its misformalization-fix process teach M5? Does it cover any of Will's campaign problems? |

**Stop condition for 0e:** every row has an adopt / imitate / differ / ignore verdict with a primary-source citation; the three G1 recommendations are written; and the §7.5 interop lists are confirmed or corrected. Do not start implementing anything during 0e, and do not contact anyone. Will makes all contact.

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