# GP delta for the JC adjoint-recurrence lane

Date: 2026-08-01

## Result

Grand Portage independently replayed the corrected unilateral annihilator
boundary from the frozen certificate. The current native checker passes 44/44
checks and retains certificate digest
`9a3f3854b19d5efe988c660f51babbb7b71eca00cf99b2fd88c8b6168ccb7ba4`.

GP independently established the certificate premises:

- padded operator jumps occur exactly at depths `7, 9, 11, 13`;
- `B_d = 0` for every `d >= 14`;
- `B_13 != 0`;
- on the unilateral domain `d >= 6`, `S^8` annihilates and `S^7` fails.

A new Mathlib-free Lean theorem proves the reusable inference: for rational
constant shift coefficients acting faithfully on a sequence module, a zero
tail from `N` with nonzero value at `N-1` characterizes annihilators by
vanishing of all coefficients below shift `N-start`. Thus the live ideal is
exactly `(S^8)`, no annihilator has nonzero constant term, and no reversible
backward recurrence exists.

The GP report retains graph effect `NONE`. P1--P5, S2, the pin, and H8 remain
explicit assumptions. Nothing about additive values, source membership,
geometric nonextension, H3, or `(75,125)` is promoted.

## One wording clarification found

The result note describes `S-1` as the minimal annihilator “within each
regime.” On the declared padded sequence, regimes R5 (`d=14`) and R6
(`d>=15`) are identically zero, so the unit operator already annihilates those
regimes. Therefore blanket minimality of `S-1` across all six regimes is false
as written unless “regime” is intended to exclude the zero-tail regimes or to
refer to a different unpadded object.

This does **not** affect the corrected global unilateral ideal `(S^8)`. The
certificate field itself says only `within_regimes: S - 1`, which is true as an
annihilation statement; the overstatement is the word “minimal” in the prose.
Recommended repair: qualify it as applying to the nonzero regimes R1--R4, or
drop “minimal” where R5--R6 are included.

## Review artifacts

- `review/jc-h3-adjoint-recurrence-v1.json`
- `fixtures/jc_adjoint_recurrence/v1.json`
- `experiments/jc_h3_adjoint_recurrence/adapter.py`
- `lean/GrandPortage/ParametricRecurrence.lean`
