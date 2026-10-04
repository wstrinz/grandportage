# Packet revision 3 review — approved amendments

Approval: Will approved this review and BACKBRIEF-REV3.md on 2026-09-29. Proposed amendments below are operative under DECISIONS.md; later G1 selections remain open.

2026-09-29. Read the entire 1,045-line supplied packet. Preserved it verbatim as `docs/GP-0.50-REWORK-PACKET-rev3.md`; earlier packet and approved decisions remain unchanged. This review does not close a phase or change case expectations.

Source attachment: `$HOME/.codex/attachments/1f13aad9-a9f4-4902-aa9b-c0663ad2737e/Pasted text.txt`.

- Revision 3 SHA-256: `c718b9f2905520da658ba5cd9accc957fa3f5d4407419b10de68833de0118983`
- Retained revision 1 SHA-256: `949cc271a0a353e593961974349aa99711d2dd7bde1b26a51a5e8260ed1c2110`
- Direct comparison: retained revision 1 → revision 3, in `reports/PACKET-REV1-REV3.diff`. Revision 2 and Addendum A were not found among retained packet files; their individual changes are described by revision 3 §R, not independently diffed here.

## Read and actual changes

The revised direction is worth adopting with the corrections below. The user benefit is clearer, and adopt-before-build plus interoperability can reduce implementation work. The main cost risk is turning the landscape review into another exhaustive investigation.

| Area | Revision 1 → revision 3 | Effect on this workspace |
|---|---|---|
| Core | Claim/scope/warrant becomes the mechanism for honest carrying and earned consequences; regimes/checkability become explicit | Better framing; constrain completeness language below |
| Architecture | D14–D18, pinned Mathlib binding layer, Mathlib-aligned statements, adoption and interop defaults | Preserve small Mathlib-free kernel; evaluate components before building |
| 0a/0b | Existing method preserved; A27 and optional `also_earned` added | No redo; preserve 408 cases and immutable replays; correct A27 before adding it |
| 0c | Adds two timed Mathlib elaborations in a separate Lake package | A real addition despite the blanket statement that 0a–0d are unchanged |
| 0e/G0 | Adds 18-row primary-source review, territory/consumer check and PRIOR-ART.md | New required deliverable; keep it bounded |
| G1 | Explicit warrant-form, checker-layer and scope-vocabulary decisions | Evidence-backed recommendations followed by Will's sign-off |
| Later work | Selected algebraic points, Formal Conjectures/meaning audit, blueprint/LMFDB-style exports, M6 after G5 | Future profile/binding/surface work; no implementation now |

Numeric gate thresholds and kernel budgets remain; G0/G1 requirements grow. Prior-art coverage can support “not found in this review,” not prove that no competing project exists. A community's apparent fit is a candidate-consumer hypothesis, not confirmed demand.

## Amend before treating the packet as operative

### 1. Correct A27; preserve the lesson about conditional authority

The packet's present-tense description of PARI defaults is contradicted by PARI's current stable manual. It says `bnfinit` adjusts initial bounds until generation is justified under GRH; a smaller bound than classical Bach does not itself mean unjustified. `bnfcertify(bnf,0)` returning 1 supports full certification; flag 1 only certifies a quotient/subgroup relation. These are documentation checks, not an executed computation or audited implementation. [PARI manual, bnfinit and bnfcertify](https://pari.math.u-bordeaux.fr/dochtml/html-stable/General_number_fields.html).

The historical “Bach constant cheating” account is real, but dated December 2003; it cannot establish current defaults. [Developer archive](https://pari.math.u-bordeaux.fr/archives/pari-users-0312/msg00020.html).

Magma has a second trap: `Proof := "Full"` uses the global class-group bound. After `SetClassGroupBounds("GRH")`, that same option is conditional. Capture effective configuration, not just the local option name. [Magma ClassGroup handbook](https://magma.maths.usyd.edu.au/magma/handbook/text/416).

**Proposed replacement:** one bounded A27 family distinguishing an explicitly heuristic result, a GRH-conditional result, and fully certified evidence. Refuse unconditional promotion of conditional evidence and full-group promotion from partial certification. A positive control must bind the actual input, version, effective configuration, successful check and admitted authority. Pin any historical heuristic example to a release. Do not implement number theory to create this seed. Do not treat a CAS output or its “Proof” label as a GP warrant: mathematical rigor and GP checker admission are separate requirements. No A27 expectations have been written or changed here.

### 2. Narrow the promises to what the contract can establish

- **§3.2/§6.6:** replace “no such system exists for ℚ” with “no general complete effective method is known over ℚ.” The rational decision problem remains open; the integer undecidability result is different. [Research paper on Hilbert's tenth problem over subrings of ℚ](https://arxiv.org/abs/1601.07158). Likewise replace “GP is nearly complete” with a statement about available theoretical certificate systems, not implemented coverage. Full Positivstellensatz completeness does not follow merely from admitting a limited SOS checker.
- **§2/§6.5:** say “consequences reachable under admitted rules within the supported closure domain,” and explain missing admitted evidence rather than claiming the true reason every impossible transfer fails. A capped display does not make infinite closure terminate. Distinguish unknown method from unavailable checker or missing receipt when tagging obligations.
- **D17:** K2 narrows context classes. From a claim held only over ℚ it cannot infer every field. Wider earned scope must come from checking/admitting the receipt at its justified reach under K1, or another sound admitted derivation. Settle finite materialization versus query-based reach at G1; no new rule is automatically necessary.
- **§8.8:** polynomial plus isolating interval represents real algebraic numbers, not every point of a polynomial solution set. For example, `x - y = 0` has transcendental real points. Limit the statement to algebraic witnesses for the specified rational/algebraic polynomial setting. Exact substitution also requires a representable witness and checks of all model constraints.
- **§7.1:** Lean already quantifies over structures via hypotheses. GP's proposed distinction is operational campaign state and accessible evidence handling, not that Lean can express only one world.

### 3. Preserve approved local rules

§8.5 repeats the old two-consumer shortcut. Retain DECISIONS.md #4: **every** checker needs a soundness argument and adversarial controls. M4 still lists trusted generation; retain DECISIONS.md #3: replay-only authority unless Will explicitly approves an exception. Keep the narrowed closure-effort decision, confirmed-manifest gate, measurable spike cap, read-only predecessors, private work and cancelled heartbeats. Submission of a revised packet is not a reason to silently erase these specific approvals.

### 4. Resolve two internal choices explicitly

- **Selected root/embedding:** §2 and §8.1 place selection in context/scope while §8.8 puts the root in the statement. Proposal: bind the particular selected point/root in the statement/model; put ambient field properties and genuinely quantified embedding assumptions in scope. Test the distinction on existing cases at G1 rather than opening another corpus batch.
- **Territory test:** §7.1 says either territory claim being covered implies contributing elsewhere; G0 says report if both are covered. Proposal: adopt overlapping components in either case; report a whole-project pivot if both are covered. No automatic abandonment, contribution or external contact.

## Verification to defer to the bounded 0e/G1 work

Do not run all eighteen investigations just to approve this packet. The three G1 recommendations need pinned primary evidence on MathEvidence contracts/licence/maturity/toolchain, Mathlib hypothesis-to-scope mapping and elaboration costs, and compatible evidence formats. The new tool/community descriptions, counts, adoption claims and 2026 talk details have not all been independently verified in this review; §7 marks the landscape as working pending 0e.

Proposed 0e budget: **two hours of active review**, ending sooner if its deliverable is complete. Keep all 18 rows, combine overlapping P12/P16 reading, mark P13 M1-only and P15 post-G5 as directed, and use explicit unknowns when evidence is missing. No code imports, installations or new integration prototypes in this reading pass. At the cap, report unresolved G1 decisions rather than silently extending research or calling an incomplete gate complete. Build/timing experiments belong in separately capped 0c after 0a/0b.

G1 must also settle sound binding of theorem assumptions/axioms, statement identity and versions; typeclass vocabulary alone is not a scope-entailment proof. Graph6 serialization alone is not canonical labeling; bind the canonicalization procedure. A proof pointer alone supplies no checked theorem. LMFDB-style output is a compatibility target to verify, not an established universal schema. DRAT ingestion needs an admitted validation route. These are boundary checks, not reasons to build new infrastructure now.

Retain the existing G1 question about G3: the entire corpus includes operational and diagnostic cases. Assign each to the responsible core/profile/adapter/surface verification without dropping cases, weakening expectations or pretending every case belongs in the kernel.

## Recommended continuation after approval

Finish parent review of Sol's operational register and grouped 0a dispositions under the existing finite closeout plan. Add only the corrected, bounded A27 family once its semantics are approved. Confirm the complete sweep manifest before 0b. Prepare the bounded 0e recommendations and agree the 0c cap; do not restart heartbeats or launch post-0b implementation. The supplied packet §0 explicitly requires stopping after BACKBRIEF-REV3.md until Will approves, so this turn ends at review and proposed amendments.
