# Expected-verdict changes

No corrections to existing expected verdicts have been made.
Initial batch: Appendix A seeds plus source-grounded controls and registered conservatisms.
Future corrections require Will's sign-off and an entry here; oracle disagreement alone is not a reason to change the expected verdict.

2026-09-29: Added X408 REFUSE/X409 ACCEPT exact-contraction and valid-evaluation-lift contrast; both oracle observations explicitly UNSUPPORTED. No existing expectation or case bytes changed. See reports/PHASE-0A-CONTRACTION-LIFT-INTEGRATION.json.

2026-09-30: Added X410/X411 REFUSE and X412 ACCEPT ordinary-point guard cases. Three actual pinned decision-branch diagnostics; native verdicts remain null. No existing expectations or case bytes changed. See reports/PHASE-0A-ORDINARY-POINT-GUARD-INTEGRATION.json.

2026-10-03 (PROPOSED, pending Will sign-off): intake of three Fano realization cases authorized by post-G2 §1.13 and §3.6, currently slice fixtures profile/slice/fano-c1-char0.json (ACCEPT), fano-c1-char2.json (REFUSE) and fano-witness-f2.json (ACCEPT). Intake needs case.schema.json to accept source repository "post-g2-handoff" and the provisional ids (or new GP-X ids). No existing expectation or case bytes change.

2026-10-03 (signed: Will adopted G3a review ruling 6; X49 by Will's ruling on the 3a.1 step-4 report): instantiation fixtures in corpus/INSTANTIATIONS.json for GP-A11b, GP-A12, GP-A23, GP-C02 and GP-X59, as the review proposes them, and for GP-X49 (an unrecognized verifier version as the proposed change). Each fixture is keyed by case id and the FNV-1a of the case bytes, and the runner refuses a stale fixture. No case bytes or expected verdicts change.

2026-10-03 (signed: Will, review ruling 7): Fano intake. The proposal above is done. GP-X413 (ACCEPT), GP-X414 (REFUSE) and GP-X415 (ACCEPT) are the former reach-slice fixtures GP-FANO-C1, GP-FANO-C1-CHAR2 and GP-FANO-F2, sourced to post-G2 handoff §3.6. case.schema.json accepts the source repository "post-g2-handoff". No existing expectation or case bytes change.

2026-10-03 (signed: Will, ruling on the ambiguous-case residue): instantiation fixtures for GP-X121, GP-X51, GP-X52, GP-A22 (explicit surface) and GP-X73, GP-X74, GP-X75, GP-X76, GP-X77, GP-X78, GP-X79, GP-X80 and GP-X81 (compiled by the v0.37 ladder and depth-6 adapters, with the v0.37 tests' mutations as data; depth-6 instances omit two passenger generators that do not involve c7_5). GP-X76 and GP-X81 are the stated exception to a false conclusion: their lesson is that corrupt evidence is unverified, not refuted. No case bytes or expected verdicts change.
