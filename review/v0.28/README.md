# Grand Portage v0.28 release record

Version: `0.28.0`

Graph format: `5`

Kernel epoch: `10`

Collected checks: `1445`

v0.28 is an extraction and trial release. It adds no graph relation, claim
kind, graph field, evidence schema, graph format, or kernel-epoch change.

## Landed work

- The signed-off JC campaign tree moved to the optional
  `grandportage-jc-campaign` companion. The core retains neutral contract
  fixtures, generic compilers, the adapter conformance harness, and a narrow
  public-snapshot re-accretion gate.
- A genuinely cold ARR15 packet trial ran once. Its standard outcome is
  `PACKET_DEFECT`: useful work returned, but one declared source digest was
  wrong. The exact report and failure matrix are in this directory.
- Campaign packet compilation now verifies every declared source path and
  LF-normalized digest before emitting a packet.
- `CertificateScope.lean` now proves named stability decisions for every
  runtime builtin certificate. The runtime registry binds all eight names to
  their Lean decision and derived `SCHEME` or `FIELD_RELATIVE` scope.
- Authorized live Singular differential fuzz is restored and reports the
  checked case count and deterministic seed.
- The compact projection was exercised on the 452-record ARR15 graph. It is a
  useful content-addressed digest index, but not yet a semantic review model;
  the separate dogfood memo records that limit.

## Validation

- Core ordinary gate: `1395 passed, 50 deselected` in 44.65 seconds.
- Core live WSL/Singular gate: `50 passed, 1395 deselected` in 358.89
  seconds after the expected sandbox refusal and approved identical rerun.
- Lean: 27 jobs built with no `sorry`; only pre-existing linter warnings.
- Live reference differential: 22 checked cases in 10 seconds with seed
  `270027`, zero divergence. This is bounded fuzz, not exhaustive proof.
- Extracted companion: `357 passed, 9 skipped, 2 deselected` in 248.46 seconds.
- Companion adapter conformance: 14 adapters and 42 mutation controls pass.
- Public-snapshot and neutral Stacks custody controls: 17 pass.

No replay or exhaustive tests remain in the core after campaign extraction;
those lanes belong to the companion.

## Check-count reconciliation

v0.27 collected 1,752 checks. Exactly 300 campaign-only checks moved to the
companion, leaving a 1,452-check general baseline. The retained files then
changed by a net -7, yielding the honest v0.28 count of 1,445:

| retained test surface | v0.27 | v0.28 | delta | disposition |
|---|---:|---:|---:|---|
| authority registry | 6 | 8 | +2 | Lean/runtime scope drift controls added |
| campaign packet/ledger | 15 | 13 | -2 | JC cases replaced by neutral matroid cases and source-digest refusal |
| compact projection | 2 | 3 | +1 | missing-output-parent regression added |
| dossier | 16 | 15 | -1 | campaign portrait removed; neutral closeout retained |
| Laurent lowering | 17 | 15 | -2 | checked-in campaign copies removed; synthetic algebraic controls retained |
| projection | 8 | 7 | -1 | campaign graph migration example moved |
| release | 17 | 15 | -2 | campaign archive cases moved; synthetic archive retained |
| Stacks applicability | 12 | 10 | -2 | three campaign applications replaced by one neutral application |
| publication, factor/product, affine, triangular | 93 | 93 | 0 | fixtures and prose rewritten as neutral contracts |
| **retained-surface net** | **186** | **179** | **-7** | no padding tests |

The companion collects 368 checks: 312 inherited campaign checks (including
the 12-check historical Stacks surface) plus 56 new adapter conformance and
mutation checks. Its non-live result accounts for all 368 as 357 passed, 9
skipped optional integrations, and 2 deselected live checks.

The file move itself is exact: 175 tool paths relocated, while 12 generic
support files are intentionally duplicated in the companion. `PROVENANCE.json`
lists all 187 inherited files individually.

## Publication gate

The local companion repository has no remote and has not been pushed. Creating
or selecting the public remote remains an explicit external-authority step.
The core and companion should be published in that order so the companion's
pinned Grand Portage dependency remains resolvable.
