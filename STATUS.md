# Grand Portage status

Updated 2026-10-17: **v0.54.0** (Lane P fixes and speed; [notes](reports/RELEASE-NOTES-v0.54.0.md)) follows **v0.50.0, the first stable release**, published on public `wstrinz/grandportage` ([release](https://github.com/wstrinz/grandportage/releases/tag/v0.50.0), [receipt](reports/STABLE-PUBLICATION.json)). **Now:** trials stage 1 is done except one paper ledger; 0.51 has started (Lean rc3, Hex v0.9). Rulings: [DECISIONS](DECISIONS.md).

**In plain language.**
- GP is our private **belay**. It is a small proved Kernel with checkers that are sound against Mathlib. It tracks what is held, what rests on OPEN premises, and what is refused.
- What we hand to anyone else is a **rope**: a Lean theorem that stock Comparator checks, needing no trust in GP. See the [fixed-ropes handoff](docs/GP-0.50-FIXED-ROPES-HANDOFF.md).
- Campaigns verify other people's results and climb our own problems. Every claim states its premises. Active campaigns are withheld from public releases until their outreach is done.
- The workspace repo has been private since 2026-10-10.

**Gates.** G2, G2.5, G3a, G3P, G4 and GK are ratified. G3b ratified 2026-10-09, then GE on 2026-10-10.

**Now.**
- **A verification campaign** (withheld) has a conditional verdict in GP and a Comparator-checked rope under named hypotheses.
- **An own-climb campaign** has reproduced its predecessor result with exact certificates; withheld until its gates.
- **Ropes.** R1a is public and meets GR1; others are in preparation.

**Not claimed.**
- No published result is independently re-established outright.
- Campaign results are conditional or belay-only where labelled.
- OPEN premises stay open.

**Validation.** The gp50 suite passes locally (231 tests in the targeted run, including the axiom audit). Comparator passes all 3P shards, including 57 of 62 EMPTY claims, and R1a. Every Kernel module passes `leanchecker`. Heartbeats are paused.

**Earlier milestones.** `v0.50.0-alpha.2` was published 2026-10-11. `v0.50.0-alpha` was published 2026-10-04 on the public `wstrinz/grandportage` ([receipt](reports/ALPHA-PUBLICATION.json)). 3P holds χ for 493 matroids ([F2 report](campaigns/3p-matroids/F2-REPORT.md)). The census profile holds the DK slice ([receipt](reports/DK-V4-RECEIPT.json)).

- [Standing limits](LIMITS.md)
- [Rope checklist](docs/ROPE-CHECKLIST.md)
- [Review guide](REVIEW.md)
