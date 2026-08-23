# Grand Portage v0.26 ARR15 hardening release

Grand Portage v0.26 repairs the open-locus verifier and custody seams exposed
by the post-ARR15 focus group. It keeps graph format 5, kernel epoch 10, the six
exact-affine transport types, and the four core claim kinds.

## Release boundary

- GP base: `fb72a341916ad14cfa7982b4f48912c439310115` (`0.25.0`).
- Implementation commit: `d7ad881e1716716d66a415e62e7eaf830f66a6f1`.
- Package: `0.26.0`.
- ARR15 reference: `2fe83ac60c789da0bd2677d0d927e5decbd42b8e`.
- Graph format / kernel epoch: 5 / 10, unchanged.

ARR15 mathematical authority was read and copied into hash-bound regression
fixtures only. This lane did not append to, rewrite, revalidate, or promote the
ARR15 graph.

## Reproduced failures and tests

| ARR15 observation | Before | v0.26 regression and result |
|---|---|---|
| `V(y) intersect D(x)` accepted `(0,0)` | equations checked; guards ignored | bad point is `NOT_A_POINT`, `(1,0)` is `VERIFIED` |
| equation-free `A1 intersect D(x)` could not verify | empty generator list returned `UNVERIFIED` | `x=1` verifies and `x=0` is rejected |
| class 12909 rational point remained ambient-only | 108 determinant guards were ignored | hash-bound equation-free fixture checks every guard exactly |
| full class 4102 exhausted sparse expansion | `CertificateError` escaped and aborted the batch | 42 equations / 291 guards return bounded `UNVERIFIED`; unrelated work continues |
| large localization had no scalable authority path | only in-process product search | supplied `localized_guard_reduction_chain_v2` checks exact factor/remainder cofactors and replays on fold |
| superseded family debt looked live forever | default check had no lifecycle distinction | current, historical, and stale-reference classifications; history remains available |
| MCP-only lanes lacked baseline and branch custody | manual diffs and JSONL surgery | baseline read/accept, prefix receipt, tail export, and read-only merge assay |
| evidence schema required rejected writes to discover | most semantic requirements appeared optional | native/MCP schema exposes requirements, enums, target types, conditionals, and both evidence examples |
| 45 historical backend-v2 records were called malformed | unavailable executable identity collapsed into parse failure | 291 references audit clean; 45 verdicts are legacy-readable/legacy-unverifiable |

The focused regressions live in `test_adversarial.py`, `test_localization.py`,
`test_arr15_post_focus_hardening.py`, `test_supersession_noise.py`,
`test_mcp.py`, and `test_artifacts.py`. The ARR15 copies and source hashes are
documented in `tests/fixtures/arr15/README.md`.

## Finding classification

| classification | result |
|---|---|
| FIXED | open-guard witness soundness; equation-free witnesses; bounded localization; per-claim batch isolation; supplied factor-chain replay; historical finding visibility; MCP baseline/tail/merge/schema; historical artifact classification |
| STILL CORRECTLY REFUSED | automatic localization search that exhausts its bounded frontier; certificates not exactly bound to ordered model inputs; rational maps without localization authority; stale/unavailable backend verdicts as current authority; conflicting branch presentations |
| DEFERRED | arithmetic models over `Spec Z`; mixed characteristic and nilpotents; algebraic residue-field witnesses; Betti/module profiles; arrangement freeness; any new transport edge or claim kind |

## Validation

The v0.26 workspace collects 1,718 tests. The deterministic tier passed 1,658
tests with nine expected skips and 51 live deselections in 303.70 seconds. The
separately authorized Windows/WSL Singular tier passed all 51 live tests in
388.12 seconds. Total: 1,709 passes and nine expected skips.

The first sandboxed live attempt correctly exposed
`WSL/Service/CreateInstance/E_ACCESSDENIED`; no result from that environmental
failure was counted. The authorized rerun was green. The ARR15 artifact audit
checks 291 execution references with zero integrity problems and classifies 45
historical verdicts as legacy-readable/legacy-unverifiable.

A no-dependency, no-build-isolation PEP 517 wheel build produced
`grandportage-0.26.0-py3-none-any.whl` with SHA-256
`280c4db8d6b60f79b7f8e908bc7850fb071cf2441be1749c3dc9bca4ad5e74d9`.

## Negative findings and rejected alternatives

- The sparse-expansion ceiling was not enlarged into a less predictable crash.
- A failed sufficient localization search is not interpreted as nonemptiness.
- `saturated_at` was not silently reinterpreted as `open_conditions`.
- Historical findings and immutable artifact records were not deleted or
  rewritten to make current views green.
- Merge assay performs no implicit append, normalization, or conflict
  resolution.
- Per-object computation ledgers, Betti tables, and arrangement-specific
  mathematics remain outside the GP ontology.
- No seventh transport type or fifth core claim kind was introduced.
