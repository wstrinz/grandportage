# Epoch-12 seam replay

Date: 2026-09-12.  Authority: checked implementation observations only.

This note records the examples that actually crossed the new field/reach and
family/model seams.  It does not promote the frozen DK campaign's open E5
premise and does not treat migration policy as verifier authority.

## Field and certificate reach

The replay-only `rational_sos_cofactor_v1` object for the model
`Q[x]/(x^2+1)` checked the exact identity

`-1 = x^2 + (-1)(x^2+1)`.

The current certificate verdict projected `{"kind":"ORDERED"}` onto that
one EMPTY claim.  The same claim transported to an `R` endpoint and refused a
`C` endpoint.  Before the current replay it transported to neither endpoint.
Changing only `model.about` changes endpoint fingerprints, and the otherwise
licensed point cells of EQUIVALENCE, NECESSARY_CONDITION, BASE_EXTENSION,
IMAGE_CLOSURE, and RESTRICTION all refuse the incompatible `C -> R` context.
`same_as` also refuses different or incomplete point contexts.

Format-8 custom certificate declarations carry a structured reach policy, but
the declaration itself projects no effective reach.  A current verifier
receipt remains necessary.  Its input fingerprint includes the certificate
policy, so superseding or changing that policy stales the receipt.

## Historical DK conversion

The immutable format-6 DK ledger at
`tests/fixtures/dk_retrodiction/fixtures/ledger/graph.jsonl` migrated in memory
through the current strict fold: 104 events, one metadata conversion and four
certificate conversions.  The certificate-specific table produced:

| historical certificate | format-8 policy |
|---|---|
| `ORDER_CERTIFICATE` | `ORDERED` |
| `TORUS_CERTIFICATE` | `CHAR_0` |
| `FORCED_INCIDENCE_COFACTOR` | `CHAR_0` |
| `BLAND_JENSEN_GF2_CONTRADICTION` | `NONE` |

Each audit row records the discarded historical boolean and the named mapping.
Unknown certificate names map conservatively to `NONE`; neither `true` nor
`false` is mechanically interpreted as a reach object.  All historical
verdicts remain stale after the epoch advance.

## Family-to-model composition

A bounded two-member family replay crossed the seam only with all of these
present: exact enumeration evidence deciding `BOTH`, a live COUNT coverage
claim, a proved group, an exhibited member listed by the family, a model bound
to that member, and an inference mapping its family premise to the bridge.
Both premise orders produced the same model endpoint.

The negative controls refuse EXCLUSIONS-only enumeration evidence, an unproved
group, a family claim without an explicit bridge, and an open member.  The
frozen DK ledger therefore keeps `D-E5-GAP` first: its one-sided enumeration
evidence is still debt, not a newly licensed family/model conclusion.

## Reproduction

The deterministic suite exercises these seams in
`tests/test_epoch12_contract.py`, `tests/test_format_epoch.py`, and
`tests/test_guard_release.py`.  The release record will pin the final command
outputs and package/public-snapshot checks after version metadata is advanced.
