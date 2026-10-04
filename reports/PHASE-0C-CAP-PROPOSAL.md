# Phase 0c proposed bounded feasibility run

2026-09-29 local. Proposal only; not authorized to start. Requires completed 0a/0b and Will's explicit cap approval. Phase 0/G0 remain incomplete until the spike report includes Mathlib timing and any gate uncertainty is reviewed.

Recommend **six shared active agent-hours**, counting coordinator and worker time together, with **at most two additional hours of unattended build/download wait**. Tool latency and debugging while an agent is working count as active time. Reserve and release slices against one ledger; do not reset the budget across chats/turns. Stop when deliverables are complete or the cap is reached. No automatic extension.

## Finite deliverables

1. Up to 90 minutes: pin an installed Lean 4 toolchain, create a Mathlib-free Lake package on F:, parse JSONL, and fold a deliberately tiny claim set with toy K1/K2/K4. Demonstrate malformed-record refusal, source/receipt binding and deterministic concatenation/re-fold. Document precisely which rules and premises are modeled; this is not the Phase 1 kernel spec.
2. Up to 90 minutes: invoke one external checker using IO.Process with bound input/output and explicit TCB; implement one tiny sparse polynomial over Q and exact cofactor replay. Demonstrate valid and tampered candidates. Evaluate the pinned LRAT checker against exact CNF/certificate inputs, separating checker soundness, parsing/encoding and its evaluation trust boundary.
3. Up to 90 minutes: a separate Lake package with immutable compatible Mathlib dependency. Planned obligations: GP-A08b, the integral unit identity specialized to F_3 (with a generic nontrivial-ring comparison), and GP-A05, the obstruction to reducing the coefficient 3/8 in characteristic2. Formalize the actual denominator/invertibility or ring-homomorphism obstruction for the refusal; do not substitute a missing API hypothesis for the mathematical result. Measure clean and warm elaboration/check times separately. Compare exact definitions/assumptions without committing to a scope representation.
4. Up to 90 minutes: parent review, reproducible scripts, build/fold/check timings, TCB.md and a concise feasibility report. Incomplete items remain explicit; no silent gate pass.

Allocations are planning ceilings within the shared six-hour cap; unused time may be reassigned with an entry in the ledger. Setup/download preparation counts. After60active minutes without a usable baseline build, stop setup and report the concrete blocker before spending the remaining budget. Checkpoint after the first three active hours.

## Environment and evidence limits

Existing Lean 4.32.1/Lake ran in the earlier environment inspection; that installed toolchain is a candidate starting point, not a newly verified compatible Mathlib/LRAT pin. Inspect actual installed source/toolchain identity and select a matching immutable Mathlib revision before measurement. Do not silently upgrade to make a test pass. Read existing C: installations if useful; every new package, scratch file, downloaded dependency, cache and build stays on F:.

The 0e review found that the inspected bv_decide/LRAT reflection path uses nativeEqTrue and adds an axiom. The spike must report whether its actual pin follows that path, whether a kernel-reduction route is usable, and the explicit compiler/runtime trust required if native evaluation is used. It cannot equate a proved checker with an axiom-free replay route.

Use positive and hostile miniature fixtures plus an explicitly labeled serialization/load exercise sized to the 459-case corpus. A toy fold/load benchmark is not semantic execution of all 459 cases or validation of every harvested export. List unsupported formats and obligations. No production checker admission, package adoption, campaign theorem repair or complete profile implementation.

## Stop and decision

At completion/cap, deliver measured evidence and recommend proceed/pivot/blocker. Any unfinished required spike item keeps0c/G0open. Any continuation or architecture fallback requires Will's decision. The indeterminate incident-cost pivot screen from 0b remains separately visible for explicit review before Phase 1. G1 adoption decisions are not bundled into cap approval.
