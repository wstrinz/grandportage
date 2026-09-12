# v0.34 / epoch 12 executable contract

Status: accepted implementation contract, frozen before product semantics change.
Date: 2026-09-12.
Baseline: v0.33.0, graph format 7, kernel epoch 11.

This contract incorporates the accepted corrections in
`review/v0.32-preflight/README.md`, the epoch handoff in
`review/v0.32/SOL-HANDOFF.md`, and the later prior-art review.  Where the
original epoch packet differs, this document is authoritative for v0.34.

The release is intentionally narrow.  It adds explicit field context,
verifier-earned certificate reach, and one family-to-model composition seam.
It does not add a general number-field arithmetic backend, theorem search, SOS
search, an ATMS rewrite, or a Lean-first implementation.

## Non-negotiable judgments

The implementation keeps these as three separate pure decisions:

1. `concrete_extension(source, target)` checks a concrete compatible field
   inclusion.  Universal classes are not concrete fields.
2. `instantiate(reach, target)` checks whether a universally quantified
   certificate applies to a target field.
3. `witness_transport(witness, source, target)` checks whether the exhibited
   point itself has a compatible image.  It retains `point_universe`, exact
   coordinates, `witness_field`, selected embeddings, and coefficient maps.

No shared numeric field ladder implements these decisions.  In particular:

- an R-point of `x^2-2` does not generalize to every ordered field;
- a Q(i)-point of `x^2+1` does not become an R-point;
- an EMPTY result quantified over ordered fields instantiates at Q and R but
  not C;
- a rational point may move Q -> R because its coordinates replay through the
  canonical inclusion, not because R belongs to a larger class;
- missing context is never read as BASE, Q, R, or a universal class.

## Closed field vocabulary

`model.about` states the field or field class whose points the model discusses.
The v1 atoms are `Q`, `R`, `C`, `ANY_ORDERED`, `ANY_CHAR_0`, and `F_p` for a
prime p.  `ANY_*` is legal only where quantified semantics are meaningful; it
never participates in `concrete_extension`.

`model.compute_in` is an authoring alias for the existing
`model.coefficient_domain`.  The folded model keeps `coefficient_domain` as
the canonical computation field.  If both are present they must be identical.
Exact computation remains bounded to Q and prime fields.  A prose `field`
value is historical context, not a substitute for either new field.

`point_universe` remains independent and relative to `about`: `BASE`,
`ALGEBRAIC_CLOSURE`, or `REAL_CLOSURE`.  An omitted universe is untyped.  An
algebraic-closure point over Q may use i and therefore cannot be copied to an
R/BASE model merely because both presentations compute over Q.

Simple number-field witness v1 remains a checked Q-algebraic-closure witness.
Transport of such a witness to R requires a separately replayed real embedding
map.  The old spelling `Q(sqrt 17)` does not choose a root and supplies no map.
The first epoch-12 implementation may refuse this positive until that map is
present, but it may never guess one.

## Certificate reach

The serialized reach object is closed:

```json
{"kind":"ORDERED"}
{"kind":"CHAR_0"}
{"kind":"FIELD_SPECIFIC","field":"F_2"}
{"kind":"NONE"}
```

Reach is a checked, model-bound result, not authority attached globally to a
certificate name and not an author-selected scope.  A current verifier receipt
projects it onto the EMPTY claim.  Stale, missing, malformed, refused, or
inconclusive evidence projects no reach.

The initial conversion table is:

| Certificate/check | Checked computation context | Earned reach |
|---|---|---|
| exact unit/cofactor identity | Q | `CHAR_0` |
| exact localized unit identity with all recorded guards | Q | `CHAR_0` |
| exact unit/cofactor identity | `F_p` | `FIELD_SPECIFIC(F_p)` |
| exact rational SOS/cofactor identity | Q | `ORDERED` |
| selected-real-root sign receipt | one selected embedding | `FIELD_SPECIFIC` only; never `ORDERED` |
| nonsquare-class argument | named field | `FIELD_SPECIFIC(field)` when independently checked |
| cited proof without replay | any | `NONE` |
| failed/capped/timed-out search | any | `NONE` |
| `NO_RATIONAL_POINT_SEARCH` | any | `NONE` |

`NONE` is not weak EMPTY authority.  It is an explicit statement that the
record licenses no EMPTY transport.  Unfinished attempts belong in the
UNRESOLVED work sidecar.

Historical `base_changes` records remain readable only through historical
format handling.  Migration uses a certificate-specific table, records every
conversion in its audit, advances the epoch so old verdicts are stale, and
never maps booleans mechanically.  In particular, `true` in characteristic p
does not become CHAR_0 and `false` does not become FIELD_SPECIFIC.

## Replay-only ordered certificate

The new proof object is `rational_sos_cofactor_v1`:

```json
{
  "method": "rational_sos_cofactor_v1",
  "ring_vars": ["x"],
  "generators": ["x^2+1"],
  "squares": ["x"],
  "cofactors": ["-1"]
}
```

The checker verifies over Q, with the existing exact sparse-polynomial budgets,

`-1 = sum(squares[j]^2) + sum(cofactors[i] * generators[i])`.

It never searches for squares or cofactors and never invokes Singular.  A valid
identity proves no common zero in any ordered field and earns `ORDERED`.  It
does not apply at C.  Malformed, noncanonical, detached, over-budget, or false
proof objects refuse at replay and project no authority.

## Point-carrying edge gate

P0 remains first: point universes must agree unless the edge carries the exact
verified capability that changes them.  Field context is then checked for every
point-carrying path, not only BASE_EXTENSION:

- NONEMPTY with an exhibited point requires `witness_transport`;
- existential NONEMPTY requires the existing existential rule plus compatible
  concrete model context;
- EMPTY uses `instantiate` on checked reach, never witness transport;
- PREDICATE retains embedding identity and condition expressibility;
- IDENTITY retains coefficient descent, origin, and map checks.

The gate is shared by direct edges, equivalences, partitions, `same_as`,
inference paths, CLI/MCP probes, reloads, and verifier endpoint checks.  A
second edge type cannot route around it.

## Family-to-model bridge

The one new bridge record is closed and explicit:

```json
{
  "ev": "family_bridge",
  "id": "B-E5",
  "family": "F",
  "enumeration": "CL-F-ENUM",
  "coverage": "D-F",
  "group": "G-PROVED",
  "member": "E5",
  "model": "M-E5",
  "why": "the model is the exhibited E5 member"
}
```

An inference names bridges by premise claim id in `family_bridges`.  A bridge
licenses composition only when all of the following are live:

- the family names the exact enumeration claim;
- current ENUMERATION evidence for that claim decides `BOTH`;
- `coverage` is a COUNT claim at the same family;
- `group` occurs in that COUNT, is listed in `proves`, and exhibits `member`;
- the family explicitly lists `member`;
- the family premise rests on that same proved group;
- `model` is the inference path's model endpoint.

Premise order has no semantic effect.  EXCLUSIONS-only evidence, an unproved or
unexhibited group, stale enumeration/coverage, missing membership, or an open
E5 group refuses composition.  `established_by` and `ladder` remain provenance,
not theorem authority.  Enumeration debt and open slots remain visible.

## Epoch and compatibility

The semantic change targets graph format 8 and kernel epoch 12.  New current
graphs use `about`, canonical computation context, structured reach, and bridge
records.  Format-7/epoch-11 graphs remain inspectable and migrate
non-destructively.  Migration does not overwrite its source.

The following are licensing fields and enter supersession grading and all
relevant fingerprints: model `about`, `compute_in`/`coefficient_domain`,
`point_universe`, embedding; certificate reach policy; claim effective reach;
bridge endpoints and supporting claims.  Changing any of them stales prior
verifier authority.

CLI schema, MCP schema, manifest, compatibility docs, release docs, and the Lean
epoch shadow must agree before release.  Lean shadows decisions; it does not
mint runtime authority.

## Phased gate

1. Freeze this contract and pure field/SOS answer keys.
2. Add format-8 vocabulary and conservative migration.
3. Bind checked reach through the v0.33 authority nucleus.
4. Apply the point-carrying edge gate across every route.
5. Add the explicit family bridge and permutation/debt controls.
6. Replay frozen DK inputs; write `SEAM.md` only from checked results.
7. Run deterministic, live/pinned Singular, CLI replay, Lean, wheel, public
   snapshot, and release gates.

Any implementation result that contradicts the negative controls pauses the
release.  A new positive requiring an unimplemented exact map remains a named
refusal rather than being approximated by prose.
