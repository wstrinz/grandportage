# Campaign publication v0

`campaign-publication/v0` is the author/reviewer projection of one compiled
campaign release. It renders the publication tables that are most dangerous to
maintain independently in prose:

- exact-scope portrait claim cards;
- claim grade, assumptions, consumers, and evidence dependencies;
- residual and canonical price ledger;
- retired-representation table;
- replay and archival matrix;
- exact publication blocker ledger.

It is generated editorial material:

```text
authority: DERIVED_READ_MODEL_ONLY
graph_effect: NONE
```

It cannot upgrade a claim, close a leaf, satisfy an undeclared publication
artifact, or write the graph.

## Render the JC handback

The full report combines the dependency audit and manuscript tables:

```text
gp campaign-publication fixtures/release/jc_publication/release.json \
  --source-root ../math-stuff
```

Render either component separately:

```text
gp campaign-publication fixtures/release/jc_publication/release.json \
  --document portrait-audit --output PORTRAIT-AUDIT.md

gp campaign-publication fixtures/release/jc_publication/release.json \
  --document manuscript-tables --output MANUSCRIPT-TABLES.md
```

`--format json` emits the complete structured projection. Output files are
written atomically and never replace an existing file without `--force`. The
release input itself is protected from overwrite.

## Portrait dependency audit

Every claim row retains:

- stable claim and scope IDs;
- the proposition and non-collapsed grade;
- named assumptions and consumers;
- every evidence artifact's grade, role, availability, and public disposition;
- replay status, exact command, and release lane;
- selected archive path, license state, and aggregate release coverage.

The prose renderer then expands each row into a dependency card. A conditional
claim remains visibly conditional even when every dependency is packaged and
replays. `release covered` means only that the declared evidence payloads were
selected; it is not a theorem verdict.

## Manuscript-ready tables

The second document supplies factual tables suitable for review and adaptation
into a technical report:

1. current portrait and qualifications;
2. theorem-facing residuals, price status, exact object, next accepted object,
   and resume condition;
3. retired representations and their evidence-backed reasons;
4. artifact replay and archival selection;
5. release blockers by machine-readable class.

The output calls itself editorial material, not a manuscript. Consequently it
does not satisfy a dossier `MANUSCRIPT` placeholder.

## Generated-artifact contracts

A missing publication artifact may be projected present only when the dossier
declares its exact `generated_by` contract and the release selects the same
generator. For example:

```json
{
  "id": "JC.ARTIFACT.PORTRAIT_AUDIT",
  "availability": "MISSING",
  "role": "PUBLICATION",
  "generated_by": "PORTRAIT_AUDIT"
}
```

The release binds that contract to a safe output path, explicit provenance,
and license status. Supported bound generators are currently:

- `RELEASE_MANIFEST` — the archive's generated `manifest.json`;
- `PORTRAIT_AUDIT` — the exact claim dependency audit;
- `MANUSCRIPT_TABLES` — editorial source tables, only for a dossier artifact
  explicitly typed with that contract.

Generated documents receive deterministic digests and appear in
`SHA256SUMS`. The release manifest uses its plan fingerprint instead of a
circular self-digest. A present artifact cannot declare a generator, and a
generator contract is legal only on a missing `PUBLICATION` artifact.

This prevents two important category errors: arbitrary generation cannot
stand in for a proof/formal interface, and manuscript tables cannot stand in
for the manuscript.

## Current JC result

The current JC publication release requires 17 records. Sixteen are now
selected or generated. The portrait audit and release manifest are generated
under exact dossier contracts, leaving the manuscript as the sole absent
payload. Independent readiness debt remains visible: six non-S2 leaf price
cards are incomplete, six load-bearing notes lack replay receipts, and the
matching source checkout is dirty. The bound head includes the new
preimage-free LOCAL connecting row and exact 36-dimensional page binding; the
remaining lower S2 obligation is the generic rank-nine obstruction bound.

The generated tables are therefore useful immediate manuscript inputs without
misreporting the package as publication-ready.
