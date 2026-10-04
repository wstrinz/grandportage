# Phase0c core runtime and checker findings
All41 finite controls pass. The Mathlib-free package pins existing Lean4.32.1/f054605aea4b840552cca2e725580bffd1e1b704. No production checker is admitted.

JSONL decoding, finite-context K1/K2/K4 toy folding, exact source/receipt binding, freshness invalidation, concatenation/re-fold determinism and explicit cycle/malformed/duplicate refusal work. checked_equality proves the actual natural-equality checker result, with propext only; complete fold soundness is not claimed.

Exact sparse univariate Rat cofactor replay handles integer and rational coefficients, duplicate terms and hostile mismatch/count/denominator/degree controls. The independent Python Fraction process is invoked through Lean IO.Process. Exact echoed input, checker label and exit status are required; forged-binding/version outputs fail. This tests plumbing, not checker admission.

The installed LRAT checker accepts the parsed tiny certificate and rejects a satisfiable-CNF pairing, invalid hint index and malformed text. Its soundness theorem carries the ordinary Lean axioms; the executable and native_decide route also rely on runtime/compiler evaluation. NativeCheck's generated axiom is printed explicitly. Plain/kernel decide and bounded full-definition imports failed. Equation simplification exposed the next unreduced RUP-check result, without completing a pure-kernel proof. No general impossibility or alternate checker implementation is inferred.

Final clean package build43.10seconds; warm no-change build0.68seconds. New-module kernel rechecks25.86/28.07seconds; these accept declared axioms and reuse imports. They do not recheck all Lean library dependencies or discharge native-result axioms.

Final459-case-sized toy load0.70seconds (an earlier run0.12seconds under a different contention state). This folds1378toy events. It substitutes trivial natural equalities and opaque case digests for actual mathematical cases; no semantic corpus or harvested-format performance claim. Timings are local single observations under concurrent worker activity, not stable benchmarks.

No observed Lean-plumbing blocker or evidence of impractical toy-fold performance. Recommend keeping Lean for the next specification stage, subject to the G0 meaning/adapter-risk review and later G1 sound binding/admission decisions. TCB.md lists source-authentication, parser/resource, statement/scope and unsupported-format limits.

Evidence: PHASE-0C-CORE-BUILD.json, PHASE-0C-CORE-VALIDATION.json, PHASE-0C-LRAT-REDUCTION-ATTEMPT.json, PHASE-0C-PRESERVATION.json. Reproduce with tools/build-lean-spike.py and tools/check-lean-spike.py from the F workspace.
