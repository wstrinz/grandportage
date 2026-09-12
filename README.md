# Grand Portage

**Transport typing and obstruction tracking for computational algebra.**

A computation produces an artifact. The artifact does not carry its own
license to conclude. Grand Portage records what each modelling step loses and
refuses conclusions that loss does not support.

```text
$ gp check
UNSOUND_CONCLUSION  TRANSPORT:INF-C08-HIST
  asserted: field-relative emptiness as geometric emptiness
  refused: BASE_EXTENSION licenses EMPTY along only when its certificate
           survives the extension
  discharge: provide a base-changing certificate or keep the narrower scope
```

That illustrative refusal came from a real published error: a nonsquare-class certificate
over one field was consumed over every characteristic-zero field. GP turns the
mistake into a type error at the transport boundary.

## What it is

Grand Portage is research middleware for seams between exact-affine
computations. It records models, typed model changes, claims, replayable
evidence, and the exact scope in which an inference is licensed. It is useful
when humans or agents hand a long-running campaign back and forth.

It is not a mathematical database or a home for bulk CAS output. Keep large
computations in content-addressed artifacts; use GP for compact conclusions,
provenance, and obligations that later work must not misread.

Scope is derived from certificate kind, never accepted from an author's label.
For example, a unit-ideal identity is stable under base change and receives
`SCHEME`; a nonsquare-class obstruction is field-relative. A contradiction
between declared scope and derived scope is refused at fold time.

## Transport at a glance

Edges point from a tighter model to a looser one. `ALONG` follows that arrow;
`AGAINST` runs backward.

| edge | ordinary point meaning | load-bearing transport |
|---|---|---|
| `NECESSARY_CONDITION` | source points are target points | `NONEMPTY` along; `EMPTY` against |
| `BASE_EXTENSION` | points change coefficient field | `NONEMPTY` along; `EMPTY` along only with stable evidence |
| `IMAGE_CLOSURE` | target is the closure of an image | witnesses require checked point-lift evidence |

The remaining edge types, every conditional cell, and the exact licensing
rules are in [SPEC.md](SPEC.md). Historical confessions remain there too: five
v0.1 identity cells were wrong, and later drift exposed additional checker and
read-surface defects. They are part of the review posture, not release notes.

## Start here

The v0.33 authority-boundary release preserves graph format 7 and kernel epoch
11. It routes every existing fold-time verdict projection through one checked,
sealed binder and ships the post-v0.32 review diagnostics without widening
mathematical authority. [Release notes](review/v0.33/README.md) describe the
boundary and validation. [Operational work](docs/WORK.md) covers unresolved
attempts and the explicit accounting-only check mode.

```console
python -m pip install -e .
python -m pytest -q
gp init --mcp
gp schema
gp check
gp table
gp evidence
```

Without Singular, bare `pytest` skips the live tier with a reason. Set
`GP_REQUIRE_LIVE=1` when the live CAS boundary is an authorized release gate
and must fail rather than skip. [QUICKSTART.md](QUICKSTART.md) carries a full
ten-minute campaign and the recovery commands.

## What a fresh reader can answer

- **Established:** current claims whose declarations, evidence, provenance,
  and transport paths replay successfully.
- **Carried:** only conclusions licensed by each typed edge and direction.
- **Stale:** evidence whose model, verifier, backend, or input fingerprint no
  longer matches; it remains history and carries no authority.
- **Licensed:** the graph effect and scope derived from the evidence contract,
  never from prose or process success.
- **First unresolved seam:** `gp check` reports current actionable debt first;
  `gp frontier` and the derived review surfaces show larger campaign context.

## Status and documents

Version <!--version-->0.33.0<!--/version-->, graph format
<!--graph-format-->7<!--/graph-format-->, kernel epoch
<!--kernel-epoch-->11<!--/kernel-epoch-->. The suite currently has
<!--checks-->1716<!--/checks--> checks. v0.33 centralizes fold-time verdict
authority without changing transport semantics; v0.31.2 makes exact cofactor-certified
identity authority independent of local CAS availability; v0.31.1 closes the
remaining untyped-model escape hatch for field-relative emptiness; v0.31 publishes the v0.30 native
verification, extension-witness, ordered-receipt, and Lean work together with
historical-format migration repairs and a closed, bounded grammar for
field-relative emptiness scope. The transport table remains at kernel epoch 11.

- [QUICKSTART.md](QUICKSTART.md) — install and first campaign
- [SPEC.md](SPEC.md) — complete transport and verifier behavior
- [OPERATION-CONTRACTS.md](OPERATION-CONTRACTS.md) — operation semantics versus checked guarantees
- [COMPATIBILITY.md](COMPATIBILITY.md) — formats, epochs, and migration
- [ARCHITECTURE.md](ARCHITECTURE.md) — trust zones and module boundaries
- [REVIEW.md](REVIEW.md) — current general attack surface
- [review/v0.29/README.md](review/v0.29/README.md) — public release record, selected-embedding implementation, and CFG23 replay evidence
- [review/v0.30/README.md](review/v0.30/README.md) — native verification, extension witnesses, ordered receipt independence, and Lean epoch-11 parity
- [review/v0.31/README.md](review/v0.31/README.md) — public release record, compatibility repairs, and field-scope hardening
- [review/v0.31.1/README.md](review/v0.31.1/README.md) — patch release record for field-scoped emptiness on untyped models
- [review/v0.31.2/README.md](review/v0.31.2/README.md) — patch release record for environment-independent exact identity receipts
- [review/v0.32/README.md](review/v0.32/README.md) — guard release, DK acceptance deltas, and operational accounting
- [review/v0.33/README.md](review/v0.33/README.md) — authority-binding boundary and review diagnostics
- [grandportage-jc-campaign](https://github.com/wstrinz/grandportage-jc-campaign) — optional extracted campaign fixtures, replay, and historical review brief
- [HISTORY/](HISTORY/) — superseded findings retained as evidence
- [lean/README.md](lean/README.md) — non-authoritative semantic shadow

After the companion is published, its optional external conformance lane is:

```console
git clone https://github.com/wstrinz/grandportage-jc-campaign
cd grandportage-jc-campaign
python -m pip install -e ".[test]"
python -m pytest -m "not live"
```

The core checker and JSON read models are Python standard-library code. A CAS
is used only for explicitly authorized live verification; the small checker
replays retained certificates independently of the search that found them.

## Limits

GP does not find missing equations, cannot type a modelling step that was never
declared, and detects absent structure more readily than weak structure. Most
of the real work remains deciding what the models are. The tool makes that
judgment explicit and keeps it from dissolving during handoff.

The name is the 8.5-mile haul around the Pigeon River falls: the deliberate
carry between two bodies of water, with constant attention to what can cross.
