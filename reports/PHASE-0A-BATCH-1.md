# Phase 0a — first corpus batch

Status: in progress. This is not a G0 pass or a completeness claim.

## Verified here

- 50 neutral cases: 17 must-accept and 33 must-refuse.
- Every Appendix A seed has at least one record; several seeds split into multiple conclusions. This is seed coverage, not full historical coverage.
- JSON Schema, unique identifiers, pinned source anchors and a clean oracle revision validate.
- Oracle revision: ac4155787207e2847d248cffed7be871d5dcd577.
- The latest replay records 42 agreements, 4 known differences, one observed diagnostic defect, and three pending projections.
- Targeted frozen regressions: 89 passed, one live-CAS case deselected; six additional focused regressions passed. These are 95 selected tests, not the full release suite.
- Mechanical discovery indexed 1,198 test functions, 1,856 keyword hits, and 244 historical commits (32 candidate subjects). Index entries remain unreviewed until semantic examination.

## What the observations mean

27 cases exercise conditional rules: their prerequisites are assumed at
the legacy table boundary. Other routes exercise exact receipt replay, reach,
graph diagnostics, binding, declaration checks, or adapter input validation.
An ACCEPT from a transport function is not a checked graph warrant and is never
reported as a GP 0.50 held claim. Corpus inputs stay outside GP's graph format;
legacy projections live separately in oracle/ROUTES.json.

The adapter constructs some fixtures using pinned oracle test helpers. In the
staleness and UNVERIFIED probes, backend descriptors are test data; no actual
backend execution is claimed. One observed detail matters for the new design:
v0.37 can retain an UNVERIFIED entry inside an authority-receipt wrapper. The
wrapper's existence alone does not mean a positive verification occurred.

## Findings

- GP-A03a: pinned containment guidance proposes radical membership while saying
  every licensed cell rests on that containment. Recorded as a diagnostic
  defect; no end-to-end false held claim has been asserted.
- GP-A08b / GP-A08c: the SPECIALIZATION table refuses the two p-integral controls.
  The unit certificate was replayed over Q and modulo 3; the witness was checked
  by exact rational and modular substitution. This is a table expressiveness
  loss, consistent with the packet's known issue.
- GP-X03: empty source to exact image closure is a registered conservative
  refusal in v0.37.
- GP-X08: a derived identity whose target retains its equation is also refused
  by the source-origin table rule. Target ideal membership was independently
  replayed. This does not claim other verifier routes cannot re-establish it.

## Pending and coverage gaps

- GP-A22: the precise coefficient-cap example has a pinned SPEC source; its
  corresponding executable oracle projection still needs extraction.
- GP-A24: Cloquet's collapsed-placement case needs its primary campaign model
  and guards. Packet-only provenance remains visible.
- GP-A25b: the alias-binding case needs an explicit oracle projection.
- GP-A03a remains a diagnostic audit, not an executed false-authority result.
- The remainder of the tests, documentation, Lean ledger, deleted paths and
  history still need semantic review and deduplicated minimal case extraction.
- No campaign incidents have been classified or counted under Phase 0b.

## Reproduce

From the F: workspace, run .venv/Scripts/python.exe -B tools/check-corpus.py
--run-oracle. Results are retained under reports/oracle-runs/; the latest
projection is reports/ORACLE-RESULTS.json. The runner binds each case, the
route map, schema and runner with SHA-256 hashes.

No expected verdict was corrected to make a run pass.
