# Private Mathlib binding spike

Lean 4.32.1 is read from the existing C: toolchain; all new package files,
dependencies, artifacts, logs, caches and temporary files are on F:.
Mathlib is fixed to 520045ab14e26149ee970e2e617ca04b09bde5d6 (Apache 2.0).
The generated lake-manifest locks all transitive repository revisions.

Binding.lean manually formalizes the unchanged GP-A08b and GP-A05 statements.
It does not parse GP JSON, prove a JSON-to-Lean translator, implement scope
entailment, or admit a checker. Its generic statements quantify over Ring,
Nontrivial and (where needed) CharP 2, not a chosen field string.

A08Timing.lean and A05Timing.lean contain the same obligation proof text in
separate namespaces for isolated case timing. Binding.lean additionally contains
trivial-ring and characteristic-three controls. Validate.ps1 checks the final
axiom output and the original case hashes. Failed and narrower preliminary
runs are retained in logs and are not final audit evidence.

Run from spikes/mathlib-binding:

```powershell
. ./environment.ps1
lake update
lake exe cache get Mathlib.Algebra.Field.ZMod Mathlib.Tactic.Ring Mathlib.Tactic.NormNum
./Measure.ps1
./MeasureCases.ps1
lake env leanchecker -v Binding
./RecordProvenance.ps1
./Validate.ps1
```

Measure.ps1 removes only this package's resolved .lake/build, after checking its
absolute path and rejecting a reparse point. It keeps dependency builds/cache.
Thus clean-package time is not a cold Mathlib-from-source build. Warm-noop build
replays cached messages; the three warm elaborations really rerun the source.
Leanchecker replays the new module declarations into its imported environment;
it does not independently rebuild/recheck every Mathlib dependency or act as a
separate proof kernel. Kernel replay timing logs were recorded separately.

The Q coefficient obstruction concerns unqualified reduction of 3/8. It does
not exclude every special evaluation or separately justified integral rewrite
of d2=h2-(3/8)*h1^2. Syntactic, totalized F2 division yielding zero is not a
unital-ring-homomorphic image of Q's coefficient.

Parent report/ledger/gates, core package, cases/adapters/oracle, adoption and
production checker admission are outside this package's authority.
