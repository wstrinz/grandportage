# Phase 0a — explanation authority boundaries

Fully read explain.py, test_explain.py and ExplainChecks.lean; read the complete project_v2.context helper and source graph helper used by the diagnostic. Five tests pass, including actual offline SOS receipt recording, stale/removed receipt gaps, family-context removal, CLI read-only bytes and a missing-corpus sentinel. No live CAS, external campaign read or Lean execution.

A native validated inference with an empty transport path and unverified premise reports runtime_licensed=true and profile_covered=true, but complete=false and child runtime_licensed=false. This agrees with the earlier transport-versus-entailment distinction. The full explanation preserves missing leaf authority; the top-level runtime_licensed label should not stand alone as an earned-conclusion verdict. Proposed clarification: explicitly name conditional runtime/transport admission and preserve child/obligation gaps in downstream views.

The first harness attempt incorrectly supplied derived concludes_at in a native event; the schema refused it. Removing that output-only field produced a native validated graph. No oracle schema was bypassed or modified.

Leaf freshness checks loaded authority membership and current provenance. Ordered SOS reconstruction matches actual verifier/version/representation shape rather than only a certificate tag, while target-law interpretation remains a semantic premise. Paths retain adapter gaps; REIFIED means recovered data, not a proved codec. Legacy partition/family explanation branches do not establish native admission.

Lean test verifies checked-in #check text matches a name dictionary only; no typecheck or kernel feasibility is claimed. Full project_v2 expression and broader consumer review remain open. All 352 corpus cases validate unchanged; no expectations, adapters, frozen source or publication changed. Phase 0 remains active.
