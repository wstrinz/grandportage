# Hex adoption map (0.50 Trials, R1)

2026-10-13. Desk research only: nothing was built, changed or filed. Sources, read as data:

- GP 0.50 at `dbad771` (the workspace).
- Hex v0.9.0, aggregator tag `b608972`, with every library at its `v0.9.0` tag (shallow clones in `src/v09/`).
- hex-dev `main` at `98eccd8`, read through `git show` because Windows checkout fails on that tree. Open PRs and issues were read on the same day.

"Lines" are real Lean lines: non-blank, outside comments. They were counted with a script, not estimated. Glue estimates are marked "≈".

## Summary

- **GP uses Hex thinly.** The profile imports `HexMvPoly` (three files) and `HexPoly` (`Real/RAlg.lean` only). The binding imports `HexMvPolyMathlib` and `HexPolyMathlib`; the census imports `HexGraphIso` v0.4.0. Everything else GP replays was written by GP: prime factors, Descartes/Möbius sign certificates, number-field reduction, LDLᵀ, the hash zero test.
- **A version-only bump deletes nothing.** Every API GP calls still exists at v0.9.0 under the same name, for example `MvPoly.subst`, `toMvPolynomial_subst`, `coeff_toMvPolynomial`, `aeval_apply`, `Colored`, `canon` and `iso_iff_canon_eq`. `PolyFast.lean` is still needed, because v0.9 `Mono.lex` still compares `toList`s.
- **Real adoption candidates exist in released v0.9.0**, in six places:
  - HexPrimality for prime factors;
  - HexRealRoots (Tarski/Sturm) for real-root signs;
  - HexBerlekampZassenhaus for irreducibility;
  - HexPoly `xgcd` for the untrusted Bezout searches;
  - HexDeterminant for the matroid determinant;
  - HexGraphIso v0.9.

  Their total net deletion is about **500 lines out of 15,375** in profile, census and binding (about 3%). About 240 of those 500 come from one swap, RAlg to HexRealRoots, which also changes the certificate format and adds Tau Ceti to the binding.
- **The packet's suggested first drop-in is mis-aimed.** Lane H says to start with "HexModular for denominator and reach arithmetic". HexModular does CRT and rational reconstruction, which is producer-side work, and its Mathlib companion is only planned. GP's reach arithmetic needs complete prime factorizations of denominators, guard values and coefficients. The released fit for that is HexPrimality with HexPrimalityMathlib.
- **The toolchain cost comes before any deletion.** At v0.9.0, `HexMvPoly` itself requires `HexModArith`. Its umbrella imports `KernelResidue.Denote`, which imports `HexModArith.Ring`, which imports `HexModArith.Residue`, which holds `@[extern "lean_hex_zmod64_*"]` C code built with `cc`.

  That is exactly the FFI the A3 deviation avoided: "needs `cc` and gmp.h". This machine still has no `cc` on PATH, though the Lean toolchain ships `clang.exe`. Most adoption candidates also pull in `HexArith`, whose `extended_gcd.c` links `-lgmp`: HexPrimality, HexPolyZ, HexRealRoots, HexBerlekampZassenhaus and HexNumberField all do. See [PIN-PROMOTION-REQUEST-HEX09.md](PIN-PROMOTION-REQUEST-HEX09.md).

## What GP uses from Hex today

| Package | GP pin | Used by | v0.9.0 commit |
|---|---|---|---|
| HexMvPoly / HexPoly / HexBasic | v0.6.0 | profile: `Poly`, `PolyFast`, `Layout`, `Real/RAlg` | `f75a205` / `140cd37` / `c5b9f3b` |
| HexMvPolyMathlib / HexPolyMathlib | v0.6.0 | binding: `Admission/Bridge`, `Real/AlgPointSound`, `Real/RAlgSound` (and transitively) | `c9bc472` / `1e1a604` |
| HexGraphIso (+ HexMatrix, HexBasic) | v0.4.0 | census: `Formula`, `Encode`, `Listing`, `V4`, `Extension` | `9f1c75a` (now also requires HexPermGroup; no FFI) |

## Adoption map: GP component → Hex

| GP component (real lines) | Hex v0.9.0 equivalent | Unreleased hex-dev | TCB change | Toolchain change | Net deletion |
|---|---|---|---|---|---|
| Prime test and factor list: `Poly.isPrime/trialFactors/multiplicity/primeFactors` (25); binding `Arith.isPrime_iff`, `mem_primeFactors` (33) | `HexPrimality.isPrime`, `isPrime_iff`, `rhoFactor?_spec`; `HexPrimalityMathlib.isPrime_iff_natPrime` | none needed | + HexPrimality, HexArith compiled; trial division → certified primality and validated factors; completeness of the factor list stays GP glue (≈12) | HexArith FFI (`cc`, gmp) | ≈ −46 |
| p-integrality and F_p residuals (`zeroMod`, `unitMod`; A3 deviation) | `HexMvPoly.Kernel` residue arithmetic (`KernelResidue.mulMod`) and `HexModArith` | Kronecker `Mod` (#10281, spec #10269) | swaps Rat replay for residue replay; certificates would carry residues | HexModArith FFI if linked | 0 (keep) |
| C1/C3 residual over ℚ (`Algebra.residual`, `reachBase`) | already HexMvPoly | Kronecker `checkTermsEq` (Int only) | revision bump only | v4.35.0-rc3 | 0 |
| `PolyFast` `@[csimp]` twins (34) | none: v0.9 `Mono.lex` still lists | n/a | none | twin target `MvPoly.instMulOfAddOfLawfulBEq` may be renamed: port risk | 0 |
| `Real/IdealZero` hash zero test (156, with proofs) | none | `HexKronecker` packed identity checks (#10281; perf issue #10287 open) | n/a | n/a | 0 now |
| SOS/ordered LDLᵀ (`SOS.Mat`, `ldl`, `LDL.squares`, 42) | none (HexMatrix has Gram/Gram–Schmidt, no LDLᵀ); soundness never rests on the LDL | n/a | n/a | n/a | 0 |
| Real-root signs: `RAlg` trusted replay (33), `RootCover.atMostOneRoot` (7); binding `RAlgSound` signs, Descartes, anchor (149), `RootCoverSound` sign variations, Möbius (144) | `HexRealRoots.tarskiQuery`, `IntTarskiCertificate.check`, `sturmCount`; `HexRealRootsMathlib.IntTarskiCertificate.check_sound`, `TarskiCount` | HexSturm (Phase 5; open PRs #10886, #10885), HexRealAlgebraic | + HexRealRoots, HexPolyZ, HexArith, HexModArith compiled; binding + **Tau Ceti** `1c497c3` (Mathlib-based) | FFI; integer polynomials and **dyadic** endpoints: GP brackets are arbitrary rationals, so the certificate format changes and the corpus must be re-executed | ≈ −240 (−333, glue ≈ 90) |
| `RAlg` isolation and refinement search (80, untrusted) | `HexRealRoots.isolateRealRoots?` | n/a | none (untrusted) | as above | ≈ −70 |
| Irreducibility: `NumberField.rrtOk` (6); binding `rrtOk_irreducible` block (62) | `HexBerlekampZassenhaus.ZPoly.isIrreducible` or `checkIrreducibleCert`; Mathlib `isIrreducible_iff`, `checkIrreducibleCert_sound` | n/a | + BZ stack compiled (HexLLL, HexHensel, HexBerlekamp, HexPrimality); a Gauss-lemma glue ≈25 | FFI | ≈ −43; **lifts the degree ≤ 3 limit** (LIMITS.md), a capability change for Will |
| Untrusted Bezout and inverse searches: `Univariate.lean` (34), `AlgPoint.bezoutFor` (5), `NumberField.invK…invR` (27) | `HexPoly` `xgcd`, `divMod` (already a dependency) | n/a | none (untrusted) | none | ≈ −56 |
| ℚ[θ]/(s) and K[Z]/(r) evaluation (`RealPoint.fieldEval`, `NumberField` RE arithmetic) and their binding proofs | `HexNumberField.QAdjoin`, `HexNumberFieldTower` | n/a | would replace `evR_*` proofs only after a representation change; QAdjoin needs an irreducible presentation, GP uses square-free `s` | FFI | 0 (not drop-in) |
| Matroid `det3P` (5); binding `Matroid/Det` (49) | `HexDeterminant` over `MvPoly` (v0.9 adds `Lean.Grind.CommRing` in `HexMvPoly.Ring`); `HexDeterminantMathlib` | n/a | + HexDeterminant | none | ≈ −39; ENCODING-FRAME equality must be re-checked |
| Census canonical forms (`canon`, `iso_iff_canon_eq`) | HexGraphIso v0.9.0, same names | n/a | revision bump | v4.35.0-rc3; no FFI | 0 |
| Binding `Admission/Bridge` (132) | HexMvPolyMathlib v0.9.0, same API | n/a | revision bump | Mathlib `85e3a25e` → `6b7abb3c` | 0 |
| Generated theorem warrants (`linear_combination`) | none | `kronecker` tactic (opt-in, #10281) | n/a | n/a | 0 now |

**Gross deletion** is about 659 lines. Glue is about 160. **Net is about −500.** By package: profile ≈ −200, binding ≈ −300.

## No Hex counterpart (checked, not assumed)

The packet's expected list is confirmed. Three more items have no counterpart: the Positivstellensatz checkers, the census encoders with their LRAT checker, and the binder.

| GP component | Real lines | Closest Hex | Why not |
|---|---|---|---|
| Kernel fold, closure, cover, conflict (22 pinned modules) | 1,853 | none | domain-independent ledger semantics |
| Reach aggregation: `Algebra` scopes and `reachBase`/`reach`/`treeObligations`; `Rules` `Scope.meet`, C4 obligations, `ruleReach` | 118 + 120 | none | Hex outputs identities and certificates, not characteristic scopes; generic rank's generic/conditional/locus (#10259) is the nearest idea |
| Ledger runners and guard (`Plan`, `Ledger`, `Guard`, `Memo`, `Real/Ledger3`, `Real/Memo3`) | (in profile 6,749) | none | GP custody |
| COVER/spine/decide: `Real/Goal.coverAllCheck`, the `Real/Admission` rule checks; binding `GoalSound`, `UDG/Spine` | 31 + 151; 217 + 94 | none | GP goal semantics |
| UDG encoder and frame (`UDG.lean`; `UDG/Frame`) | 39; 206 | none | GP encoding |
| Matroid encoder and frame (`Matroid.lean` without `det3P`; `Matroid/Frame`) | 62; 244 | none | GP encoding |
| SOS, ordered and case-tree refutations (`SOS`, `Ordered`, `CaseTree`; `SOSSound`, `OrderedSound`, `CaseTreeSound`) | 116 + 72 + 163; 156 + 170 + 205 | hex-coverings, planned (spec #10325, #10363; no code) | covering refutation, not Positivstellensatz; not released |
| Census encoders (`Formula`, `Encode`, `Circuit`, `Listing`, `V4`, `Extension*`) | 1,211 | none (HexGraphIso is used, not replaced) | GP encodings |
| LRAT replay (vendored LRAT-Catcher) | 591 (core) | none; the alternative is Lean core's `Std.Tactic.BVDecide.LRAT` | not Hex's scope |
| Binder and warrant generation | (binding) | none | GP custody |

## Watch list (unreleased; guardrail: watch, don't build)

| hex-dev item | State on 2026-10-13 | What it could replace on release |
|---|---|---|
| Kronecker `Mod` (`HexKronecker`, done_through 4) | merged: #10281 (certificates, opt-in tactic), spec #10266/#10269/#10276; open perf issue #10287 | `IdealZero`; F_p replay; `linear_combination` warrants |
| HexReflect | residue coefficients #10240/#10256; open #10690 (guarded expansion), #9437 (shared reflection plan) | nothing in the runner; maybe warrant emission |
| HexRealAlgebraic / HexSturm | Phase 4 / Phase 5; open #10885, #10886 | `RAlg`, `RealPoint`, `RootCover` with rational endpoints |
| HexRealFormula | #10414, #10422, #10702, #10799 | statement surface: R4's question, not R1's |
| hex-coverings, CAD | spec only (#10325, #10363); CAD is future work (Tau Ceti roadmap #10300, closed) | `CaseTree`/`Ordered` refutations, eventually |
| generic rank | #10259 (generic and conditional) | nothing directly; its locus output is the nearest analogue of reach |
| Gröbner | deferred (future-work §Gröbner bases) | nothing |

## What reach would look like downstream of Hex

There are two layers.

**Identity reach: a few lines downstream.** Suppose the identity `Σ qᵢ·eᵢ = hᵐ·Gᵏ` has denominators dividing `N`. Clearing them gives an integer identity. Its image in any field `K` gives `N·(L − R) = 0`, and `N ≠ 0` in `K` when `char K ∤ N`, which is one Mathlib lemma. Printing the excluded set needs a complete factorization of `N`, which HexPrimality supplies with proofs. A single prime `p` uses Kronecker `Mod`: `L̃ − R̃ = p·Q`, mapped into any `CharP R p`. HexModular adds nothing here.

GP already has this layer: `Algebra.reachBase` together with the binding's `check_sound` and `natCast_ne_zero_of_factors`. Hex would make it shorter, not possible. R3 can call this "a few lines downstream", and say so in the issue.

**Certificate and ledger reach: GP's own, about 240 lines.** This layer covers three things:
- points, where the primes of guard-value numerators are excluded;
- `proper`/`properCoeff`, where the nonvanishing of a value difference or coefficient is checked;
- the meets over cover trees and rules R1–R4.

None of these is an identity check. They are a scope algebra over certificates, and nothing in hex-dev's SPEC/PLAN computes one. This layer is a real project upstream; for GP it already exists.

## Recommendation (for Will)

- Treat a v0.9.0 bump as a version-only move first: no checker swaps, with zero byte-change in fold outputs as the bar.
- Adopt only HexPrimality and HexPoly `xgcd` in the same pass. Both are small, and the second one is untrusted.
- Defer the RAlg-to-HexRealRoots swap until it is worth a certificate-format change plus Tau Ceti.
- Defer BZ irreducibility until a campaign needs number fields of degree above 3.
- Raise the FFI question (`cc`, gmp) first. It decides whether any of this runs on this machine.
