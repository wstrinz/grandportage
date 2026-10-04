# Phase 0 environment observations

Verified locally on 2026-09-27:

- Workspace, oracle copy, virtual environment, uv cache, temporary directories and reports are on F:.
- CPython 3.12.9 is reused as the base interpreter; the new virtual environment is local to this workspace.
- Lean 4.32.1 and Lake 5.0.0-src+f054605 run from the existing C: toolchain installation. The frozen Lean package pins 4.32.1.
- The initial elan shim could not determine ELAN_HOME in this environment; direct installed executables worked. No installation or toolchain download was needed.

Not evaluated: new Lake project, JSONL parsing, process-checker integration, sparse polynomial spike, LRAT reuse, build timing or fold performance. No kernel code has been written. Set a measurable effort cap before starting the deferred spike.

Historical review batch 7 added SymPy 1.14.0 and mpmath 1.3.0 to the F: virtual environment (uv cache also on F:) for the optional defining-formula replay. This is oracle tooling, not the Lean feasibility spike.
