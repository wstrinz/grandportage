# Grand Portage status

Updated 2026-10-11, at the Codex handoff checkpoint. Detail per track: [HANDOFF-2026-10-11](docs/HANDOFF-2026-10-11.md). Rulings: [DECISIONS](DECISIONS.md).

**In plain language.**
- GP is our private **belay**. It is a small proved Kernel with checkers that are sound against Mathlib. It tracks what is held, what rests on OPEN premises, and what is refused.
- What we hand to anyone else is a **rope**: a Lean theorem that stock Comparator checks, needing no trust in GP. See the [fixed-ropes handoff](docs/GP-0.50-FIXED-ROPES-HANDOFF.md).
- Campaigns verify other people's results and climb our own problems. Every claim states its premises. Active campaigns are withheld from public releases until their outreach is done.
- The workspace repo has been private since 2026-10-10.

**Gates.** G2, G2.5, G3a, G3P, G4 and GK are ratified. G3b ratified 2026-10-09, then GE on 2026-10-10.
- R1a meets GR1, and Will's GR1 calls are open.
- An own-climb campaign has cleared its retrodiction gate.

**Now.**
- **A verification campaign** (withheld until outreach) has a conditional verdict filed in GP. Its rope is Comparator-checked under named hypotheses. `gp status` on its ledger takes 30–60 s, down from 58 min, through proved-equal speedups.
- **Ropes.** R1a (unit-distance lemmas: the rhombus lemma, TU gadgets, Schade averaging) is public and meets GR1. Further ropes are in preparation.
- **An own-climb campaign** has reproduced its predecessor result with exact certificates. It is withheld until its gates.

**Not claimed.**
- No published result is independently re-established outright.
- Campaign results are conditional or belay-only where labelled.
- OPEN premises stay open.

**Validation.** CI on master: gp50 570 passed at `2973083`. Comparator passes all 33 3P shards and R1a, and the in-preparation ropes pass on a fresh runner. Every Kernel module passes `leanchecker`. Heartbeats are paused.

**Earlier milestones.** `v0.50.0-alpha` was published 2026-10-04 on the public `wstrinz/grandportage` ([receipt](reports/ALPHA-PUBLICATION.json)). 3P holds χ for 493 matroids ([F2 report](campaigns/3p-matroids/F2-REPORT.md)). The census profile holds the DK slice ([receipt](reports/DK-V4-RECEIPT.json)).

- [Standing limits](LIMITS.md)
- [Rope checklist](docs/ROPE-CHECKLIST.md)
- [Review guide](REVIEW.md)
