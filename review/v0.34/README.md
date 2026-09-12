# Grand Portage v0.34.0 capability-bound composition release

Graph format **8**, kernel epoch **12**, collected checks **1,742**.

This release implements the accepted epoch-12 boundary: explicit field
context, verifier-earned structured certificate reach, replay-only ordered
emptiness, and one exact family-to-model composition seam. It builds on
v0.33's sealed authority binder; declarations still cannot mint verifier
authority.

## Field context and checked reach

`model.about` names the concrete field or quantified field class whose points
are discussed. `model.compute_in` is the authoring alias for the canonical
exact `coefficient_domain`; contradictory duplicates refuse. Point transport
retains `about`, computation domain, point universe, and selected embedding.
The gate applies to every point-carrying edge and to `same_as`, so a second
relation type cannot route around an incompatible field context.

Format-8 certificate records replace `base_changes` with one of the closed
reach objects `ORDERED`, `CHAR_0`, `FIELD_SPECIFIC(field)`, or `NONE`. A record
is a policy ceiling, not effective authority. Current exact unit/cofactor
replay earns reach from the checked model (`CHAR_0` over Q and field-specific
over `F_p`). Missing, stale, rejected, or inconclusive verification grants no
transport reach.

The new `rational_sos_cofactor_v1` proof object checks

`-1 = sum squares[j]^2 + sum cofactors[i] * generators[i]`

over Q using exact bounded polynomial arithmetic. It performs no proof search
and invokes no CAS. A valid current receipt earns `ORDERED` for that claim,
which instantiates at Q and R but not C.

## Family-to-model bridge

The closed `family_bridge` record binds a family's exact enumeration claim,
current `BOTH` enumeration evidence, a live COUNT coverage claim, one proved
group, an exhibited listed member, and its concrete model. Mixed family/model
inferences name bridges by premise claim id. Premise order is irrelevant;
one-sided enumeration, open groups, stale support, missing membership, and
implicit family transport refuse.

The frozen DK ledger remains a negative control: `D-E5-GAP` stays first because
its enumeration evidence decides only exclusions. The new bridge does not
manufacture the missing inclusion direction.

## Compatibility

Formats 1--7 remain directly readable as historical inputs. Migration is
non-destructive and advances old verdicts to stale history. Historical
certificate booleans are converted by a certificate-specific table with one
audit row per record; the Boolean is never interpreted mechanically and
unknown certificate names become `NONE`.

The format contract, CLI/MCP schema and show surfaces, projection,
supersession/fingerprint inputs, authority manifest, and non-authoritative Lean
shadow advance together. The exact contract and observed examples are in
`review/v0.34-preflight/README.md` and `review/v0.34-preflight/SEAM.md`.

Exact release validation and artifact digests are recorded in
`review/v0.34/validation.txt`.
