# Private Phase0c Lean experiment
Pin: Lean4.32.1 (f054605aea4b840552cca2e725580bffd1e1b704), no Mathlib imports. This is disposable feasibility code, not the Phase1 kernel.

From $WORKSPACE:
```powershell
./.venv/Scripts/python.exe -B tools/build-lean-spike.py
./.venv/Scripts/python.exe -B tools/check-lean-spike.py
```
Build script cleans only this Lake package's generated outputs, then measures clean package/warm builds and new-module kernel replay into its imported environment. Installed standard libraries are reused; this is not a clean Lean/toolchain build. The test driver creates fixtures under ignored tmp/phase0c and reports every checked outcome.

gp_spike reads JSONL events from a path or stdin. Toy event kinds: source, declare, receipt, narrow. Claims hold only through the actual natural-equality check, exact binding/freshness and finite-context containment. Failed syntax/type decoding and duplicate claim IDs refuse the entire log. There is no production profile AST or receipt authority.

gp_check_spike runs exact univariate Rat cofactor replay, one external Fraction checker via IO.Process, and the installed LRAT checker against two fixed typed CNFs. The wrapper and runtime do not create corpus warrants.

See root TCB.md and reports/PHASE-0C-CORE-VALIDATION.json for limits and controls. G1 must settle source authentication, representations, supported receipt formats and checker admission separately.
