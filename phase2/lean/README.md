# Phase 2 Lean kernel

Mathlib-free package pinned to Lean 4.32.1. From $WORKSPACE:

```powershell
lake -d phase2/lean build
./phase2/lean/.lake/build/bin/gp_events_tests.exe
./phase2/lean/.lake/build/bin/gp_closure_tests.exe
./phase2/lean/.lake/build/bin/gp_completeness_tests.exe
./phase2/lean/.lake/build/bin/gp_order_tests.exe
./phase2/lean/.lake/build/bin/gp_decoder_tests.exe
./phase2/lean/.lake/build/bin/gp_runtime_tests.exe
./phase2/lean/.lake/build/bin/gp_poly_tests.exe
./phase2/lean/.lake/build/bin/gp_bound_tests.exe
./phase2/lean/.lake/build/bin/gp_narrow_tests.exe
./phase2/lean/.lake/build/bin/gp_query_tests.exe
./phase2/lean/.lake/build/bin/gp_cover_tests.exe
./.venv/Scripts/python.exe -B tools/run-phase2-slice.py
./.venv/Scripts/python.exe -B tools/run-phase2-lifecycle-slice.py
lake -d phase2/lean env leanchecker -v GP50.ClosureProofs
lake -d phase2/lean env leanchecker -v GP50.ClosureCompleteness
lake -d phase2/lean env leanchecker -v GP50.ClosureOrderProofs
lake -d phase2/lean env leanchecker -v GP50.RuntimeProofs
lake -d phase2/lean env leanchecker -v GP50.Decoder
lake -d phase2/lean env leanchecker -v GP50.PolyStubProofs
lake -d phase2/lean env leanchecker -v GP50.AdmissionProofs
lake -d phase2/lean env leanchecker -v GP50.BoundReplayProofs
lake -d phase2/lean env leanchecker -v GP50.SpanSoundnessProofs
```

Events resolves complete event lists using explicit versions and targeted retraction/supersession. Decoder validates the typed wire envelope and rejects duplicate keys before typed admission. Installed Lean JSON still normalizes numeric syntax; raw-byte identity is an adapter contract.

Runtime converts current validated warrants into support nodes, computes finite closure and projects held claims. Entry connects raw decode to fold. Admission is a registry of validator functions; the default refuses all evidence. Runtime tests use explicit component seams, with theorem-name pointers refused.

ClosureProofs proves soundness under node semantic contracts. ClosureCompleteness proves exact finite reachability, including repeated IDs. ClosureOrderProofs proves support membership is invariant under equal complete declaration sets. RuntimeProofs proves held equals reachable warrant-backed claims for the actual fold. Whole-kernel semantic soundness and event-order proof remain in STATUS.md.

PolyStub supplies exact univariate rational cofactor replay. Its proof establishes all-exponent coefficient identity; binding and geometric interpretation remain separate.

The package has 538 passing native component controls and 65 compiled proof controls; the earlier suites include 13,122 finite graphs and 3,072 order transformations. These do not count as G2 corpus passes.

BoundReplay binds actual registered clauses/receipts and recomputes rational identities. SpanDecoder and Runner connect strict raw configuration/events to held. AdmissionProofs lifts validator contracts through the actual runtime; BoundReplayProofs establishes unique registered clause meaning on receipt acceptance. The real corpus slice currently executes seven cases; see reports/PHASE-2-SLICE.md.

SpanSoundnessProofs composes receipt admission with the actual resolver/fold/held. Successful folding and a held bit imply registration and formal polynomial-span meaning, with warrant ID uniqueness proved from resolution. The host fixture/digest contract remains separate.

LifecycleRunner exports full resolved identities/bindings and successor links. X144/X145/X146 run in both branch orders under refuseAll admission. Their ACCEPT verdicts answer operational record/link questions; held remains empty.

Semantics supplies the typed statement/model/scope contract. Narrowing checks registered exact statements and custody identities plus sound scope inclusion. Its local and fold-to-profile semantic theorems are kernel-checked; the concrete ScopedSpan instantiation discharges receipt soundness from actual exact replay. Scopes denote named Nat test contexts, with selected objects and actual polynomial data in statements.

ScopedRunner accepts strict registry schema 2 (rows contain algebra, object and scope), the existing event schema, and query schema 1 (why_not, claimed, links and open_obligations). Run gp_scoped_runner with registry.json, events.json and queries.json paths. It returns state, why_not and earned using the same admission registry. Query annotations never mint authority. Tests/test_phase2_scoped_wire.py supplies executable examples and malformed-input controls.

CoveredSpan admits named cover rules with exact destination/premise-claim lists, bound clauses and actual finite-list coverage. ScopedRunner registry schema 3 adds rules (name, destination, branches); schema 2 retains its receipt/narrowing path. CoverAdmissionProofs proves actual combined fold-to-registered-meaning soundness. Rule contracts use snapshot premise membership proved from runtime lookup, so rule soundness is applied to resolved premise records. Tests/test_phase2_cover_wire.py exercises the production route; Tests/Cover.lean separately labels its runtime seam.
