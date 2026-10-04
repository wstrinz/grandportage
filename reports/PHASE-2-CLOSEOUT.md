# Phase 2 closeout

2026-10-02. Will ratified G2. This page records what Phase 2 leaves for later; [STATUS.md](../STATUS.md) remains the current summary.

## Gate evidence

| Criterion | Evidence |
|---|---|
| Slice | [PHASE-2-SLICE.md](PHASE-2-SLICE.md), all required behaviors |
| Corpus | 79/79 kernel cases in [PHASE-2-SLICE.json](PHASE-2-SLICE.json) |
| Proofs | Fold soundness, completeness and order independence (GP50); [lifecycle properties and totality](PHASE-2-LIFECYCLE-PROPERTIES.json) |
| Budget | Logic 636/750, decoder 263/600, statement 26/120; Markdown under 15,000 |
| Validation | One fresh full run: 377 tests, 1,077 subtests; 459-case legacy replay unchanged |

## Deferred

**Phase 3 (minimal algebraic profile).**
- Univariate cofactor replay only. Multivariate certificates are bound by verdict, not replayed: the X173–X176 section map and the X65 localized unit ideal.
- Secondary profile duties stay recorded in `corpus/LAYER-TAGS.json`, for example validating a replacement section certificate (X175).
- Add the handoff's `carry_kind` to every K3 rule. Decide signature morphisms against A1/A2.
- Native LRAT remains a candidate checker, not admitted.

**Policies open to revision.**
- Theorem transport licenses only exact premise records (DECISIONS, 2026-10-01). Set equality or sound weakening would flip only refusing controls.
- Conditional harnesses assume named premises. Each report states its hypotheses.

**Math lane.**
- The handoff §3.4 M1 note (Profile as an institution fragment, checked against the Lean definitions, one corpus example per carry kind) is not started.
- Meaning (M5) remains the named blind spot.

**Corpus layers not gated by G2.** Profile 239, adapter 94, surface 17 and host 30 cases are reported, not executed natively; later gates own them.

**Carried unchanged.** Seven unresolved Phase 1 owners; prospective cost logging from Phase 5; LMFDB contact is Will's.

**Housekeeping.**
- Harnesses hard-code the local Lean 4.32.1 toolchain path, so the 0.50 suite runs on this host, not CI. Master's CI runs only the v0.37 suite.
- The slice report sits at its 500-word cap; Phase 3 should open its own report.
- Heartbeats remain paused, and the GPB builder chat is retired.
- Workspace master merges `codex/phase-0`. Public integration is a [separate plan](PUBLIC-INTEGRATION-PLAN.md) awaiting Will's gate decision.
