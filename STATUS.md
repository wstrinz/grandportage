# Grand Portage status
Updated 2026-10-04. Authority: [post-G3a handoff](docs/GP-0.50-POST-G3A-HANDOFF.md), which amends the [post-G2 handoff](docs/GP-0.50-POST-G2-HANDOFF.md) and [Addendum A](docs/GP-0.50-POST-G2-ADDENDUM-A.md); [decisions](DECISIONS.md).

**In plain language.**
- Phases 0–3a built a small proved kernel and a real algebraic profile. G3a-0 showed what GP adds over plain Lean: computed reach, refusal of meaning-changing restatements, and custody.
- No live campaign has used 0.50 yet. The post-G3a handoff moves the campaign-shaped parts of Phase 5 forward onto 3a. Phase 3P is a small real campaign on matroid characteristic sets, run by a separate campaign agent from a campaign statement, and Will reads the result cold.
- Phase 4 (census) continues alongside. Phase 3b follows G4 and absorbs the pilot's findings. G5's comparison gains six foreign incidents.

**Gates.**
- G2 ratified 2026-10-02.
- G2.5 ratified 2026-10-02.
- **G3a ratified 2026-10-03** ([report](reports/PHASE-3A-REPORT.md)). All 105 3a-owned cases agree with no losses, and there are zero false ACCEPTs across all 242 profile cases.
- Next gates: G3P (the pilot's cold read) and G4 (census).

**What is proved.**
- The kernel fold is sound, complete, order independent, total and deterministic, on standard axioms only, and pinned by `KERNEL-PIN.json`.
- The 3a profile's checkers and rules are proved sound against Mathlib: every claim the fold holds means its statement in every field of its scope.
- Theorem warrants are generated at each receipt's computed reach.

**Since G3a.**
- The `v0.50.0-alpha` was staged and held in the workspace.
- Every local machine path was removed from tracked files, and a CI ratchet keeps the count at zero.
- Workspace CI builds and tests 0.50 on Linux (`gp50`).
- The M4 census memo was adopted, and Phase 4 opened.
- Will approved alpha publication on 2026-10-04 (handoff decision 1).

**Now (Step 0 of the post-G3a handoff).** Housekeeping and log schemas, the oracle home, alpha publication, and a reviewer brief. Then 3P preparation (checker-gap controls, campaign statement format, matroid encoder, `gp` CLI, warrant emitter) and the Phase 4 build.

**Not claimed.** No census, real, number-field or class-group mathematics is certified yet. OPEN premises stay open.

**Validation.** On 2026-10-04 workspace CI is green on all jobs: the 0.50 suite has 412 passing on Linux, and the v0.37 selection 1,748. Every Kernel module passes `leanchecker`, and the corpus has 462 cases. Heartbeats paused.

- [Phase 3a report](reports/PHASE-3A-REPORT.md)
- [Alpha staging](reports/ALPHA-STAGING.md)
- [Standing limits](LIMITS.md)
