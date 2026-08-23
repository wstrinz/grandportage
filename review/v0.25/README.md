# Grand Portage v0.25 ARR15 implementation release

Grand Portage v0.25 closes the ARR15 family-public-contract defect, repairs
backend freshness across process restart, makes the executing implementation
exactly identifiable, and completes the first distributed-campaign custody
surface. It advances graph format from 4 to 5 and keeps kernel epoch 10.

The final pre-release refresh also makes historical format-4 sources readable,
rejects writes until audited migration, verifies differently named polynomial
presentations, consumes structured predicate conditions, and closes two
vacuous/raw-error declaration paths found by the n15 and M13 lanes.

## Release boundary

The semantic nucleus is unchanged: six exact-affine transport types and four
model claim kinds. This release does not add a database-filter map, affine
subfamily transport, `FREE`, a module profile, a measurement claim, or
arrangement-specific behavior.

Graph format 5 is required because every new native header persists a closed
implementation identity containing:

- package version and exact source commit;
- clean/dirty checkout state;
- graph format and kernel epoch;
- MCP protocol version; and
- backend contract, implementation, implementation version, and protocol.

Format-4 sources migrate to new files with source-digest audit receipts. They
are never rewritten in place. The kernel stays at epoch 10 because no
transport meaning or mathematical authority changed.

## ARR15 defects closed

### Historical read boundary

Formats 1--4 load as read-only compatibility history with unknown
implementation identity. `check`, `show`, `doctor`, and artifact inspection can
resume the campaign; append names the exact non-destructive migration command.
The accepted ARR15 source remains byte-identical at
`sha256:59c4171013f9bc3df2d928aeec0d881b8672ca243719e71246293647c18704cf`.

### M13 presentation and condition checks

Cross-ring polynomial maps now use source-generator images and are verified by
two certified ideal memberships plus both quotient-ring inverse laws. The toy
`Q[x]/(x^2-2)` to `Q[y]/(y^2-2)` rename and the literal M13^2--M13^5 renames
pass real Singular; the `y^2-3` mutation returns `NOT_AN_ISOMORPHISM`. M13^1's
rational auxiliary-generator map reaches an honest localization-specific
`UNVERIFIED` boundary.

Structured PREDICATE conditions are no longer write-only. All five ARR15 M13
ZERO/NONZERO collinearity fixtures pass real Singular, their cofactor
certificates replay during graph fold, and verify/reload/check consumes the
persisted verdict.

Current-format ring-free `RESTRICTION`/`IDENTITY_MAP` edges are rejected unless
both endpoints declare exact characteristic, variables, and generators.
Malformed `evidence.decides` values receive a graph diagnostic rather than a
runtime `TypeError`. `verify` and `doctor` now honor an explicit global
`--graph`; verifier writes require exactly one target.

### Family enumeration contract

`family.enumeration` is now accepted by the same closed native and MCP schemas
that real authors use. A family count clears only when the referenced claim is
a same-family PREDICATE carrying the exact `asserts_count`, with current
ENUMERATION evidence declaring `decides: BOTH`.

The acceptance fixture passes an exact 173-member n14 manifest through MCP,
reload, and checking. Naked counts, wrong counts, missing exact evidence, and
schema drift remain refused.

### Backend identity and freshness

Singular version discovery closes stdin, extracts a stable identifying banner,
and fails closed for timeouts, nonzero exits, or unidentifiable output. Backend
implementation version 4 is checked lazily when a persisted graph reloads.

The lifecycle gate starts a writer process, verifies and persists a verdict,
exits, starts a reader process, identifies the backend again, and consumes the
verdict only when the identity is unchanged. Changed and unavailable identities
remain stale. The real Windows/WSL route reported:

```text
Singular for x86_64-Linux version 4.2.1 (4212, 64 bit) Dec 17 2021 20:20:53
```

### Agent-facing custody

The new surfaces are:

- `gp init --mcp`, producing an absolute, campaign-pinned MCP configuration;
- read-only `gp doctor`, naming root, graph, implementation, CAS route/version,
  and a no-write health probe;
- `gp schema`, generated from the native/MCP field contract, including closed
  enums, lifecycle fields, placement constraints, mutual exclusion, and an
  executable family-completeness example;
- complete `gp events --folded` state, including notes, citations, evidence,
  doubts, aliases, families, certificates, and verifier verdicts;
- fingerprinted `gp check --since RECEIPT`, classifying inherited unchanged,
  new, changed inherited, and resolved findings while retaining all current
  debt and the ordinary exit policy; and
- presentation-aware merge diagnostics that require distinct presentation IDs
  plus a verified mapped EQUIVALENCE for coordinate/ring conflicts.

## Immutable E10 replay

`tools/replay_arr15_e10.py` validates and replays copies of both preserved E10
graphs. The release run matched the recorded hashes:

| lane | source SHA-256 | events | findings after format-5 migration |
|---|---|---:|---:|
| Windows/local | `ca497fd5db7a75c2eb56b6393c9a90a324b05b57cc5cc5b4f634d1326f703d8d` | 18 | 3 |
| native Mac | `3eb5639d383cd2e6933812aa52809cfb4ee1bb5e33b8de2c6d02dd2f15a9d968` | 21 | 3 |

All eight historical E10 verifier records remain stale because their preserved
binary identity is literally `unavailable`. This is the required fail-closed
classification, not a replay failure. Re-verification under backend
implementation 4 can mint fresh authority; migration alone cannot.

The merged copies reproduce four hard conflicts: three model-presentation
collisions (`M-E10-A1`, `M-E10-A2`, `F-E10-X1-10`) and one dependent edge
collision (`E-X1-10-BASE-EXT`). No field-by-field blend is attempted.

## Finding classification

| class | ARR15 result |
|---|---|
| fixed | family remediation is publicly expressible and actually discharges; stable backend verdicts survive restart; build/root/schema/state/delta/merge surfaces are explicit |
| still correctly refused | historical unknown E10 backend identities; E10 family count without completeness; unverified witnesses/containments; independent coordinate presentations without a verified map |
| deferred semantic regime | finite parent/child census selection; `Q(sqrt(5))` and `F_4` residue-field witnesses; inert exact/heuristic measurement profiles; M11 property-to-locus lowering |

## Validation

The v0.25 workspace collects 1,702 tests. Four disjoint lanes account for the
entire collection:

| lane | result | elapsed |
|---|---:|---:|
| ordinary deterministic | 1,564 passed, 8 skipped | 61.87 s |
| deterministic replay | 72 passed, 1 skipped | 192.07 s |
| exhaustive reconstruction | 6 passed | 48.00 s |
| live Windows/WSL Singular | 51 passed | 495.76 s |

Total: 1,693 passes and nine expected skips. The live lane first demonstrated
the sandbox boundary (`WSL/.../E_ACCESSDENIED`) and then passed under the
required host permission. No native-Mac execution was available in this
workspace; the preserved native-Mac graph was hash-verified and replayed.

A PEP 517 isolated wheel build produced
`grandportage-0.25.0-py3-none-any.whl` with SHA-256
`31518770ff364c9ed91866d6e7b5c127a734098f0b581628f27162ee31f859db`.

## Negative findings and rejected alternatives

- An unknown or timed-out backend is not treated as fresh.
- Historical graph headers are not relabelled or edited.
- Native event objects remain closed; schema introspection does not open them.
- A 173-entry list does not self-certify that no 174th member exists.
- Database selection is not represented as an affine `RESTRICTION` or new
  `FILTER` map kind.
- Coordinate conflicts are not normalized into an unproved identity or
  papered over with `same_as`.
- M11 does not pre-authorize a seventh transport type, `FREE`, or graded-module
  authority.
