# Grand Portage v0.32.0 guard release

Graph format **7**, kernel epoch **11**. This is Phase A of the approved DK
packet revision; epoch-12 field vocabulary and certificate reach are gated
behind this release and are not implemented here.

The source campaign is `campaigns/dk-retrodiction` at
`b876fe4ed5c8963a0e8c19e18c829821c0686654`. Imported controls and their LF
digests live in `tests/fixtures/dk_retrodiction`. Historical expected outputs
are preserved, and new acceptance tests assert the intentional changes.

## Changes

- Family premises refuse with a discharge instead of crashing. This covers
  PREDICATE and the other family claim kinds; it grants no new composition rule.
- Live non-COUNT claims cannot carry `splits`, `groups`, `method`, or `proves`.
  Shared `rests_on`, `asserts_count`, and lifecycle `why` keep their existing
  uses. Explicitly superseded malformed claims remain readable as history;
  the frozen 57-claim DK ledger contains such repaired generations.
- Witness evaluation uses simultaneous constant substitution with bounded
  expression depth. The frozen 96/97-variable pair and 138/174/1024-variable
  positive and negative controls exercise the real Singular boundary.
  Program construction is linear in coordinate payload plus generator text;
  arithmetic cost and the configured CAS timeout still bound evaluation.
- Model field, universe, characteristic, embedding, guard/localization,
  pending-ideal, elimination and component changes require semantic
  supersession instead of AMEND. No transport-table cell changed.
- History includes model and other supported entity supersessions, all
  successors of a split chain, and the model-inclusive event tally.
- `gp work` records/resolves UNRESOLVED attempts outside the graph. CLI and
  MCP checks show them without giving them mathematical authority.
- `gp check --seam unchecked` and the MCP equivalent explicitly select
  accounting checks and never report transport inferences clean. Full checks,
  hooks, and baseline authority remain independent of this mode.

See `docs/WORK.md` for the operational schema, examples and compatibility.

## Acceptance and compatibility notes

The original DK D1/D2-fail/D3-before observations intentionally differ after
the repairs. The history delta adds the sixth chain. D-E5-GAP remains the
first finding, F-TRADE remains unflagged, and X8/X10 open slots remain refused.
The original misuse observations remain in the preflight record: arithmetic
cannot detect a false total supplied by an author; (i) and dishonest COUNT
(ii) remain accepted, while the honest partial COUNT retains its finding.
The PREDICATE variants BAD-2 and BAD-2b now refuse the inert COUNT fields,
the same intentional D3 repair. `observations.json` records these deltas.
No fixture has been regenerated to invent a better baseline.

One existing witness test double was updated to evaluate the simultaneous-map
coordinates instead of searching nested-substitution output text. Its
true/false witness assertions are unchanged. Marked documentation counts are
resynchronized with the new tests.

The live CI lane uses Ubuntu 22.04 and pins Singular and its companion packages
to `1:4.2.1-p3+ds-1`, matching the reproduced D2 build. It requires live CAS
availability and runs each frozen boundary input three times. The package pin
is documented by the [Ubuntu package archive](https://packages.ubuntu.com/fr/jammy/singular).

## Deferred by design

The present DK action/template adjacency is not STALE_OVERLAP: per-action
exclusion and lack of portable template certificates can both be true. The
existing family records have neither common counting units nor a shared
evidence obligation that would establish a contradiction. Preserve the
adjacency for human review; do not infer containment from counts or prose.

Phase B must first freeze the revised extension/instantiation/witness rules,
the certificate-specific migration table, and the family/model composition
contract described in `review/v0.32-preflight/README.md`. T2 is a separate
bounded customer run; this release does not launch or modify cfg23 work.

Validation results are recorded in `validation.txt` when the release checks
complete. This source preparation is not a remote publication or deployment.
