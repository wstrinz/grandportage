# Phase 0a retained-observation adapter validation

**Status:** preparation for parent review; no corpus admission or oracle route changed.

`tools/operational-retained-observation.py` verifies one GP-X370–GP-X398 candidate against `reports/PHASE-0A-OPERATIONAL-EVIDENCE-BINDINGS.json`. The manifest binds the canonical JSON and whole file of each of 29 parent-reviewed candidates, all 50 exact retained JSON pointers across 16 evidence files, and each candidate's frozen primary source file SHA-256, line, and anchor. The two new bounded controls are included through their pointers into the existing conversion report.

The adapter requires the caller to supply a trusted whole-file manifest SHA-256. Current digest:

```text
b262813e6331971cd5bcddc2a100e7958f9940c364c0184932938cf3a176ccad
```

Example:

```powershell
.venv\Scripts\python.exe -B tools/operational-retained-observation.py --candidate GP-X378 --manifest-sha256 b262813e6331971cd5bcddc2a100e7958f9940c364c0184932938cf3a176ccad
```

A verified binding returns `diagnostic_status=RETAINED_DIAGNOSTIC_BINDINGS_VERIFIED`, `observed_verdict=null`, `agreement=null`, and `oracle_called=false`. It does not read the candidate's expected verdict to derive an observation. Missing or changed bindings produce `RETAINED_DIAGNOSTIC_BINDING_FAILED`, the same null verdict fields, and exit code 2. The manifest digest must be pinned by the integrating caller; without an external trusted digest, a replaced manifest could rebind changed content.

Validation: all 29 current candidates and 50 pointers verified locally. `tools/test_operational_retained_observation.py` passed **4 tests**, covering the full valid baseline; changed candidate, evidence, and frozen source files; altered or missing manifest bindings; and CLI failure output for changed bounded-control evidence. Test copies and mutations used F: workspace scratch only. No live CAS, campaign, corpus, route, replay, predecessor source, decision, tracker, or candidate file was changed. No commit was made.
