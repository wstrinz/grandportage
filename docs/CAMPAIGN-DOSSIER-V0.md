# Campaign dossier v0

`campaign-dossier/v0` is the provisional closeout and restart surface for
Portage Command. It compiles four records that research campaigns otherwise
keep in prose:

1. a graded current portrait;
2. a price card for every theorem-facing residual;
3. a content-addressed artifact/replay inventory;
4. named closeout profiles with exact readiness blockers.

It is a derived read model:

```text
authority: DERIVED_READ_MODEL_ONLY
graph_effect: NONE
```

A ready dossier is not a theorem. It means only that every criterion declared
by the named campaign profile is backed by an explicit, internally consistent
record.

## Run it

The self-contained shape fixture has a publication flag that permits one
priced open leaf and a gold flag that requires it to close:

```text
gp campaign-dossier fixtures/dossier/synthetic/dossier.json --format human
```

The current JC closeout fixture encodes both the short-of-summit publication
flag and the stronger gold flag:

```text
gp campaign-dossier fixtures/dossier/jc_publication/dossier.json \
  --source-root ../math-stuff --format human
```

Without `--source-root`, the dossier remains portable and the source audit is
`UNCHECKED`. Any profile requiring `CURRENT_CLEAN` stays blocked. With a source
checkout, the compiler checks:

- the expected Git commit;
- every canonical coordination-source digest;
- every present artifact digest;
- working-tree dirt.

The resulting source status is one of:

| status | meaning |
|---|---|
| `UNCHECKED` | no checkout was supplied |
| `UNAVAILABLE` | Git or the checkout could not be read |
| `STALE` | the commit or at least one bound digest changed |
| `CURRENT_DIRTY` | commit and digests match, but the checkout has changes |
| `CURRENT_CLEAN` | commit, digests, and clean-tree gate all match |

Drift is reported as a readiness blocker, not silently accepted and not
mistaken for a mathematical retraction.

Historical JC sidecar fixtures remain deterministic release tests. Their
moving-head comparisons are now intentionally opt-in because the sibling
research campaign can advance without invalidating the frozen retrodiction:

```text
GP_CHECK_JC_NATIVE_BINDINGS=1 python -m pytest -q tests/test_jc_*.py
```

Use that gate while coordinating a new native handback. Use the dossier source
audit for ordinary current-head drift reporting.

## Portrait claims

Claim grades are deliberately non-collapsed:

- `PROVED`
- `CHECKED`
- `CONDITIONAL`
- `CITED`
- `RECONNAISSANCE`

A non-reconnaissance claim cannot name a `RECONNAISSANCE` artifact as
load-bearing evidence. Conditional claims must name their assumptions. The
dossier does not decide whether a source campaign assigned the right grade;
it makes the assignment, scope, evidence, and consumers reviewable and rejects
internal grade laundering.

## Leaf price cards

Every open leaf names:

- its theorem-facing role;
- the smallest faithful exact object currently known;
- the next accepted object;
- price status `PRICED`, `PARTIAL`, or `UNPRICED`;
- cost class and measurement basis when known;
- retired representations and exact reasons;
- one explicit resume condition.

A short-of-summit profile may admit an open leaf by requiring
`LEAVES_PRICED`. A gold profile can require the same leaf through
`LEAVES_CLOSED`. This is the distinction between an honestly priced mountain
and a solved theorem.

## Artifacts

Artifacts have explicit availability, role, grade, public-release disposition,
digest, and replay state. A missing manuscript or release manifest is an
ordinary typed placeholder and therefore an exact readiness blocker. A missing
artifact cannot claim a passing replay.

Current roles are:

- authority source;
- claim support;
- formal interface;
- mechanism ceiling;
- reconnaissance;
- publication deliverable;
- external assumption.

Negative representation theorems therefore remain first-class release
artifacts without being misreported as leaf closure.

## Profile criteria

The v0 compiler supports a deliberately small generic vocabulary:

- `SOURCE_FRESH`
- `CLAIMS_PRESENT`
- `LEAVES_PRICED`
- `LEAVES_CLOSED`
- `ARTIFACTS_PRESENT`
- `ARTIFACT_REPLAY_PASS`

Profiles name exact record IDs. Unknown IDs, duplicate IDs, unknown grades,
authority widening, graph effects, path escape, digest-algorithm drift, empty
retirement reasons, and open leaves without a next object or resume condition
all fail before profile evaluation.

## Why this is separate from packets and evidence

`campaign-packet/v0` contracts one bounded attack. Its ledger records what was
tried. A dossier answers a later question: whether the campaign's cumulative
portrait, residual pricing, replay inventory, and terminal policy are ready for
publication, maintenance, or handoff.

Neither surface grants mathematical authority. If a result should alter the
proof graph, it still has to pass the ordinary Grand Portage evidence and
transport gates.

## Deferred until live use

- automatic parsing of campaign prose;
- automatic dossier synthesis;
- automatic dossier-to-release-manifest synthesis and RO-Crate export;
- UI and visualization overlays;
- planner or distributed-runner policy;
- freezing any schema as v1.

The current JC fixture is the first live pressure test. A non-JC dossier is
required before the schema freezes.
