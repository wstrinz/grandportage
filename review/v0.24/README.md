# Grand Portage v0.24 public release packet

Grand Portage v0.24 publishes the campaign closeout toolchain, replay-closure
materializer, formalization transport assay, and a reproducible public-source
boundary. It does not enlarge the mathematical kernel: graph format remains 4
and kernel epoch remains 10.

## Release surface

The new public surfaces are:

1. `campaign-packet/v0` and its immutable attempt ledger;
2. `campaign-dossier/v0`, `campaign-release/v0`, and
   `campaign-publication/v0`;
3. content-addressed replay resources and publication-independent replay kits;
4. the experimental JC `formalization-transport-ledger/v0`; and
5. `grand-portage-public-snapshot/v1`, the checked public/private repository
   boundary.

Every campaign and formalization projection remains
`DERIVED_READ_MODEL_ONLY` with graph effect `NONE`. The formalization ledger
binds exact Lean source bytes and declaration names but does not replay or
replace Lean proofs.

## Reproducible public boundary

`public-snapshot-v1.json` classifies every tracked path as public, private, or
generated. A new unclassified path refuses the export. Exact private files can
be exceptions beneath otherwise-public directories, but no path can receive
two exact classifications.

The exporter reads blobs from one immutable Git commit, never from working-tree
bytes:

```text
python scripts/public_snapshot.py --revision v0.24.0 --output-dir SNAPSHOT
```

It emits `PUBLIC-SNAPSHOT-RECEIPT.json`, binding the source commit, boundary
manifest, every public path and SHA-256 digest, and the overall snapshot
fingerprint. Workspace handoffs, coordinator packets, private planning notes,
local configuration, campaign state, and `uv.lock` are not exported.

The v0.23 public Git objects were already LF, but its Windows checkout expanded
them to CRLF. Copying exact workspace blobs into that checkout therefore looked
like a whole-tree modification until Git applied its clean filter. v0.24 adds
`.gitattributes` with `eol=lf` so later public refreshes cannot recreate that
misleading working-tree state. The staged v0.23-to-v0.24 update modifies 14
existing files and adds 41 files for the new release surface.

## Validation

The v0.24 workspace collected 1,649 tests. The documented marker partition
covered all of them:

| lane | result | elapsed |
|---|---:|---:|
| ordinary deterministic | 1,522 passed, 8 skipped | 43.03 s |
| deterministic replay | 72 passed, 1 skipped | 313.82 s |
| exhaustive reconstruction | 6 passed | 48.97 s |
| live WSL/Singular | 40 passed | 542.11 s |

The one-process marker-unfiltered invocation exceeded its 1,200-second host
wrapper without emitting a failure. The four disjoint lanes above then passed
and account for all 1,649 collected tests: 1,640 passes and nine expected
skips.

Focused release, architecture, format, public-boundary, and formalization tests
also passed 70 checks with two intentional moving-JC skips. A no-isolation wheel
build produced `grandportage-0.24.0-py3-none-any.whl` with SHA-256
`12b0ba19eaf107ed0dc746a8dfc61141ed94e26ddb2581b3ed76faa0c2e25188`.

## Suggested review order

1. Confirm `grandportage/kernel.py`, graph format 4, and kernel epoch 10 did not
   change from v0.23.
2. Review `grandportage/campaign.py`, `dossier.py`, `release.py`, and
   `publication.py` as derived operational/read-model surfaces.
3. Attack `public-snapshot-v1.json`, `scripts/public_snapshot.py`, and their
   mutation tests for leakage, omission, path escape, and dirty-tree hazards.
4. Review the JC formalization fixture for exact endpoints, retained premises,
   and refusals across finite/formal, actual/relaxed, and field scopes.
5. Re-run the ordinary deterministic CI lane from a public clone; use WSL with
   Singular only for the separately documented live boundary.

## Non-claims

This release does not establish a JC summit theorem, source sufficiency, chart
coverage, H3, or `(75,125)`. It does not turn a campaign profile, publication
table, replay receipt, or Lean declaration binding into graph authority.
