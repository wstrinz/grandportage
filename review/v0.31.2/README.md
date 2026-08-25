# Grand Portage v0.31.2 patch release record

Version: `0.31.2`

Graph format: `7`

Kernel epoch: `11`

Collected checks: `1643`

v0.31.2 fixes an environment-dependent verdict fold exposed by CFG23. Three
current identities had complete exact cofactor derivations, but appeared as
`VERIFIED_DERIVED` only when the reader could probe the same Singular binary.
With WSL unavailable, the same bytes fell back to older `UNVERIFIED` attempts
and produced three misleading TRIAGE findings.

## Exact receipt boundary

For a derived identity, GP now checks the retained equation
`lhs - rhs = sum b_i f_i` against the exact claim, model generators, ordered
ring variables, coefficient characteristic, and input fingerprint. A valid
receipt remains current regardless of whether the reader's local Singular is
unavailable or a different version. Mutated targets, generators, rings,
cofactors, or incomplete envelopes fail closed.

This does not weaken backend custody generally. Refutations, uncertified
results, searches, and other backend-dependent verdicts retain their existing
binary-identity rules.

`gport verify --dry-run` also now says when no current retryable obligation is
both eligible and checkable. It no longer claims all empty selections mean the
graph lacks reduction data; already-current terminal verdicts are named as a
separate case.

## CFG23 replay

The canonical CFG23 graph now has the same answer with WSL available or denied:

- zero TRIAGE findings and zero findings at or above `UNSOUND_PREMISE`;
- no retryable verification work, because all three identities are current;
- 38 referenced execution artifacts pass the independent artifact audit.

No campaign graph event was added or changed.

## Validation

- Complete collection: `1593 passed, 50 skipped` (`1643` total).
- Focused provenance, artifact, adversarial, and backend gate:
  `284 passed, 13 skipped` before the final release commit.
- Full Mathlib-free Lean shadow: 28 jobs passed under the pinned toolchain.

## Compatibility

Graph format 7, kernel epoch 11, persisted schemas, and the transport table are
unchanged. This is a patch-level correction to exact receipt replay and the
verification read surface.
