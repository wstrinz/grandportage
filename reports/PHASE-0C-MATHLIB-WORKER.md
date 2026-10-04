# Phase 0c Mathlib worker — bounded private spike
Completed 2026-09-30. Owned only spikes/mathlib-binding/ and this report pair. No production adoption, shared gate completion, commits, corpus/adapter/oracle changes, ledger edits or public action.

Final Binding.lean proves GP-A08b's integral identity 1=2*x+(1-2*x), cofactors 1/1, for arbitrary Ring, and emptiness of the common-zero system in every nontrivial Ring, specialized to ZMod 3. Commutative multiplication is not assumed. A ZMod 1 control has a point.

For GP-A05's d2=h2-(3/8)*h1^2, in every nontrivial characteristic-2 Ring, 8=0, 8 is not a unit, and no c satisfies 8*c=3. A unital Q ring hom would map the rational identity 8*(3/8)=3 to an impossible coefficient. ZMod 2 specializes these conclusions. Totalized division gives (3:ZMod 2)/(8:ZMod 2)=0, which is not reduction of the rational coefficient. A characteristic-3 control admits c=0. Refusal concerns unqualified rational coefficient reduction; it does not exclude particular evaluations or separately justified integral rewrites/localizations.

Binding is manual to unchanged JSON bytes, not a general JSON/AST translator, ideal checker, p-integrality algorithm, scope-entailment checker or receipt admission path. Lean parameter quantification does not establish campaign scope-string semantics.

Mathlib immutable commit 520045ab14e26149ee970e2e617ca04b09bde5d6; primary toolchain leanprover/lean4:v4.32.1; Apache-2.0 LICENSE and primary Lake configuration/manifest inspected. All nine dependency heads match lock revisions. Existing read-only C toolchain: Lean 4.32.1 Release x86_64-w64-windows-gnu, commit f054605aea4b840552cca2e725580bffd1e1b704; Lake 5.0.0-src+f054605. New clones/caches/temp/build outputs are in the owned F package. Exact definitions, tool/source/olean/log hashes and dependency URLs/revisions are in JSON provenance.

GP-A08b before/after SHA256: 6a390a0fbd25371e8aca0cf64fb69d892c694cb0a142a21787d4c179abf745bd.
GP-A05 before/after SHA256: 469b5e4060a64295eaaa170e8957d282404d6fc68445408e9255a430fa6170a4.
Corpus git diff against HEAD is empty.
Binding.lean SHA256: e7e274628ed2580b904cd9ca3ac54eedf03a3957b9c7b0f5be757951500167d5.
Binding.olean SHA256: 744c48c69680012896db1d2d705946dab621c40c78aaca7b50cb2976d0cd81a3.

| Final measurement | Wall seconds |
|---|---:|
| Lake update | 86.5504597 |
| Targeted precompiled cache fetch | 142.8273896 |
| Additional ZMod field fetch | 26.2474184 |
| Clean private package build | 39.1768782 |
| Warm no-op build | 14.6170463 |
| Actual warm source elaborations | 38.9124195 / 38.8053758 / 110.2655091 |
| Whole module kernel replay | 118.7292381 |
| A08 fragment elaboration / replay | 39.2723318 / 93.0597038 |
| A05 fragment elaboration / replay | 49.7084397 / 148.5809114 |

All final commands exited zero. Fragment modules contain the same obligation bodies in separate namespaces. Cache executable built locally in 26 jobs; 1171 precompiled files initially downloaded/decompressed; field fetch added one file, 1119 already decompressed. No source-cold Mathlib dependency build was measured. Clean deletes only checked private .lake/build, retaining dependency artifacts/cache. OS filesystem cache was not flushed. Warm no-op replays diagnostics and is not elaboration. Process/Lake startup is included.

Timing variance and host contention are substantial. A read-only snapshot showed an unrelated leanchecker process PID 50224, parent 20956, command suffix leanchecker.exe --help, created 11:45:29 UTC, approximately 4.586 GB working set. Ownership unknown; not modified. No campaign-wide cost inference is justified.

Eleven final axiom reports: propext only for integral_unit_identity, integral_system_empty, denominator_eight_zero, denominator_eight_not_unit, gp_a05_no_coefficient; propext/Classical.choice/Quot.sound for gp_a08b_F3, gp_a05_F2, gp_a05_no_rat_ring_hom, totalized_division_is_zero, char_three_coefficient_exists; propext/Quot.sound for trivial_ring_has_point. No final sorryAx, native evaluation axioms, explicit user axiom declarations, sorry, admit or native_decide. Two unnecessarySimpa style warnings remain.

leanchecker -v replays new module declarations through the same kernel into imported environment. It is not an external independent verifier or fresh replay of all imported Mathlib proofs. Kernel binaries, standard logical axioms, precompiled imports and supply chain remain trusted. No LRAT conclusion belongs to this worker.

Validate.ps1 passed case hashes, dependency heads, all final exits, 11 allowed axiom reports, absence of holes/native axioms, fragment correspondence and empty corpus diff. README provides reproduction; raw logs and exact provenance remain in package.

Failed drafts retained: rewrite ordering/type inference, missing ZMod field import, norm_num finite controls, opaque totalized division with decide. Corrected using explicit ring typing, field module, kernel decide for finite controls and denominator-zero rewrite. Failed recovery logs may print sorryAx and are excluded. Preliminary narrower CommRing source/timings are retained under logs/comm-ring-preliminary and excluded. leanchecker --help initially attempted a nonexistent capitalized package module; final commands explicitly name built modules.

Budget: first recorded start 11:23:14Z; first usable CommRing baseline 11:40:12Z; required Ring baseline 11:48:28Z, within 60 active-minute setup stop. Charge 50 shared ACTIVE minutes, conservatively covering all elapsed setup, network/tool latency, monitored waits, report drafting and final delivery allowance through 12:13:14Z. Excluded unattended wait: zero. Reservation 90, unused 40 minutes. Coordinator owns ledger reconciliation; worker did not edit it. Initial report write hit filesystem sandbox denial and was retried with scoped escalation for these two authorized files.

Bounded spike complete. No adoption/shared gate declared complete. Stop further experiments and await explicit follow-up.