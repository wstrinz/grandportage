# Phase 3a reach slice

Authority: post-G2 §3.6 and Addendum A §3. Receipt: [PHASE-3A-SLICE.json](PHASE-3A-SLICE.json). 19 of 19 rows agree.

## What runs

`profile/` is Mathlib-free Lean, 666 lines. It contains:
- a canonical AST on `HexMvPoly` (`MvPoly n Rat lex`);
- characteristic-set scopes;
- the C1, C2 and C3 checkers, which compute reach;
- one shared frontend and an infix parser;
- an untrusted proposer behind a commit guard;
- the `gp_reach_slice` runner.

The Kernel fold alone grants authority, and the pin is unchanged.

A case's characteristic selects both the requested scope and the replay field (0 → ℚ, p → F_p). The proposer then re-replays each held receipt over ℚ. When the reach is strictly wider, it files that claim, which then appears in the earned surface.

## Results

| Case | Verdict | Reach |
|---|---|---|
| A08b | ACCEPT | {3}; widened to every field, **earned** |
| A08c | ACCEPT | {3}; widened, exclusion set **{2}** |
| A05 | REFUSE | ill-formed, S_stmt = {2} |
| A04 at p = 3, 5 | REFUSE | on reach: cofactor 1/p excludes p |
| X125 / X126 | ACCEPT / REFUSE | excludes {2, 23} |
| X15 / X16 | ACCEPT / REFUSE | F_2 replay reaches exactly {2}; fails over ℚ |
| Fano C1, char 0 / char 2 | ACCEPT / REFUSE | char 0 and every prime except **2** |
| Fano F_2 witness | ACCEPT | {2} |

**Fano encoding.**
- **System:** a frame on points 1, 2, 3 and 6; charts on 4, 5 and 7; 6 variables, 7 incidences, 21 nonconstant guards.
- **Certificate:** sympy found it in 0.1 s. Six incidences are linear, and the cubic reduces to 2, so the cofactors carry ½.

**Controls (§3.3).** All seven behave as expected:
- a wrong cofactor;
- a swapped generator;
- a hidden denominator at F_3, with a ℚ contrast;
- a guard vanishing mod 3, with a ℚ contrast;
- an F_2 witness used in characteristic 0.

**DK-B027 disposition.** "Finite-field controls are not a char-0 proof" is now computed rather than policy. An F_p replay reaches exactly {p}. The F_2 Fano witness is refused in characteristic 0 because incidence 457 evaluates to 2.

**Cost.** Under 5 ms per case.

## Decisions for review

- **A04 is schematic in p.** It runs through generic parameter substitution, at p = 3 and p = 5. That is an instantiation, not a pass for every p.
- **Fano cases are provisional slice fixtures.** Corpus intake at §3.7 needs a schema change, signed off in `corpus/CHANGES.md`.
- **F_p uses core `Fin p`,** not HexModArith: its FFI needs `cc` and `gmp.h`.
- **Statement identity is canonical text,** not a host SHA-256.

## Open (G3a)

- The Mathlib soundness theorems that admit C1–C3.
- The rules R1–R4.
- The A4 theorem costs, measured in the §3.6a shadow slice, which is next.
- A bound on k ≥ 1, which currently expands the full guard product.
