# v0.28 cold packet trial

Authority: `DERIVED_READ_MODEL_ONLY`

Graph effect: `NONE`

## Cold read

A fresh agent read only `README.md` and `QUICKSTART.md`. It correctly identified
what is established, carried, stale, licensed, and where to ask for the first
actionable seam in 45.459 seconds. The main reading friction was the distinction
between an illustrative seam and the current campaign seam, plus the expected
PowerShell `gp` alias caveat.

## Single bounded attempt

The selected handoff was `n15-publication-positioning.md`. One attempt ran from
`2026-08-23T16:02:39.0737098Z` through
`2026-08-23T16:24:32.4468340Z` (1313.373 seconds), with no mathematical or
procedural coaching. The worker made useful object-level progress and every
artifact/mutation check passed, but the mandated replay exited nonzero because
one packet source digest was wrong.

The standard ledger outcome is therefore `PACKET_DEFECT`, not worker failure,
success, or pending verification. The declared digest for `RESULTS_SO_FAR.md`
was `f15ac92092a24014a1413909966632559dc998d36377de8af9ae2a26c9d53290`;
the exact LF-normalized Git-blob digest was
`384681f801f5197b4cb9a82b7f09d68e07808446cc27da48eba7ebddc0db1ead`.
The remaining five source bindings matched.

The exact failure matrix is retained in
`cold-trial-failure-matrix.md` (raw SHA-256
`ffb05ef7e2f1c4d8561aa75c27a8b270028db879600df7d7875e7467835e8432`).

## Tool findings

The compiler previously normalized the syntax of task source bindings but did
not read and verify the bound files. v0.28 now resolves every task source under
the declared campaign root and refuses an absent, escaping, or digest-drifted
input before emitting a packet. Missing-source and digest-mismatch regression
controls cover the exact failure class observed here.

The trial was not repeated after fixing the compiler: repeating it would turn a
cold trial into a coached retry and erase the evidence this lane was meant to
collect.
