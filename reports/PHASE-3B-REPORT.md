# Phase 3b report (gate G3b)

Builder, 2026-10-09. Authority:
- [post-G2 handoff §5](../docs/GP-0.50-POST-G2-HANDOFF.md);
- [post-G3a §6](../docs/GP-0.50-POST-G3A-HANDOFF.md);
- [post-G4 §7](../docs/GP-0.50-POST-G4-HANDOFF.md);
- DECISIONS 2026-10-09: contexts, ℝ first, early freeze, and the stop-and-ask calls.

Design: [3B-CONTEXT-TRUTH-NOTE.md](../docs/3B-CONTEXT-TRUTH-NOTE.md) and [3B-PROFILE-DESIGN.md](../docs/3B-PROFILE-DESIGN.md). G3b is Will's to ratify.

## Result

| G3b condition | Status |
| --- | --- |
| 100% of 3b-owned cases pass | **51 of 51** decided, all agreeing; 0 pending (`gp_corpus_3b`, `tests/test_gp50_corpus_3b.py`) |
| Zero false ACCEPTs, re-run over all profile cases | 0 in 3b. 3a's 242-case global-safety receipt is byte-identical. The full gp50 suite passes (83 tests, 735 subtests). |
| Kernel pin unchanged, or every change logged | Unchanged in 3b. The two logged Track K promotions predate it. |
| Cloquet and u(22) realization moves have an admitted checker path | Yes; see below |

## What 3b adds

One summed profile, `Stmt3`/`Scope3`, over 3a's field contexts. 3a's statements keep their own meaning and proofs unchanged. The Kernel is unchanged.

| Family and scope | Evidence | Soundness (standard axioms only) |
| --- | --- | --- |
| `alg` (3a), lifted | 3a receipts and rules | 3a's theorems, reused |
| `orderFree` EMPTY at `semireal` / `ratField` / `real` | exact SOS/Positivstellensatz; rational-root test | `sosCheck_sound`, `ratRootCheck_holds` |
| `real` NONEMPTY at `real` (ℝ), with sign atoms | real algebraic point (field form, selected root, shared sign anchor) | `pointCheck_sound` (IVT) |
| `real` EMPTY at `real`, with sign atoms | Krivine–Stengle certificate (C7) | `orderedCheck_sound` |
| `realCover` at `real` | selected-root cover | `rootCoverCheck_holds` (at most one root, from Mathlib's Descartes bound) |
| `nf`: a number-field point or finite-quotient unit, inside characteristic 0 | irreducibility, reduction, Bezout inverses; fixture custody by SHA-256 | `nfCheck_holds` |
| `alg` NOT_IN_IDEAL(1) inside characteristic 0 | `algPoint`: a root of m plus Bezout per guard | `algPointCheck_means` |

Kind-1 rules: K1a (3a EMPTY at char 0 gives `orderFree` EMPTY at `semireal`) and K1b (3a NONEMPTY gives `orderFree` NONEMPTY at `real`).

Refusing controls: no scope relates `alg` to the real family. A ℂ or characteristic-0 claim never narrows into ℝ (GP-A10-C, X343, X345).

The main theorem is `fold_held_meaning3`: every claim the Kernel fold holds under `admission3` means its statement.

## Realization moves

**u(22)** ("22 points in ℝ² with ≥ 61 unit-distance pairs", rev 3 App. E):
- *realize*: real algebraic coordinates (`pointCheck`);
- *exclude_by_relaxation*: complex emptiness, which is 3a NOT_IN_IDEAL(1)/EMPTY with `algPoint` for the relaxation, and real emptiness (SOS, or C7 with sign atoms);
- *Kummer square-class independence*: a named OPEN premise, as ENCODING-FRAME was in 3P.

**Cloquet:**
- point receipts with orientation signs (`pointCheck`);
- M2 at `semireal` (SOS);
- the balance filter and "no admissible real solution" (C7). These are covered by worked tests, not yet by campaign data.

## Decisions taken in 3b

- **Contexts:** semireal and ℝ. The class of all real closed fields is deferred, because IVT in an arbitrary real closed field would cost about 800–1,500 lines.
- **The early freeze.**
- **The stop-and-ask calls:**
  - the ℚ-field scope plus the X56 fixture;
  - the A11a fixture;
  - the real cover.
- **3b fixtures live in a 3b-only sidecar** (`corpus/INSTANTIATIONS-3B.json`). This keeps 3a's ratified receipts byte-identical.

## Known limits

- **Selected-root signs mean "some root of m in [lo, hi]".** Root uniqueness is proved only inside the cover check, not for single sign claims.
- **ℝ, not every RCF.** Claims hold in fields isomorphic to ℝ.
- **No fast paths.** 3b admission has no indexed tables like Track K's. That's fine at corpus size; u(22) scale needs a GK-style pass.
- **The C5 fixture cases cost 11–17 s each,** because the certificate search runs even when custody refuses; the 3b corpus takes about 70 s. A cached certificate would fix it.
- **Number-field irreducibility** uses the rational-root test (degree ≤ 3). Higher degrees need another certificate.

## Before Phase 5 (u(22))

1. **3b claims in the `gp` CLI surface:** filing, views and MEANING text, with Kummer as a named OPEN premise.
2. **The GK budget re-measured on a u(22)-shaped ledger,** plus 3b fast paths if it is needed (post-G4 §8).
3. **Emitter paths for the 3b families** (post-G4 §7: every checker ships with one): ℝ challenges in Mathlib vocabulary.
4. **The Phase 5 entry items** (post-G2 §6):
   - collision controls on the commit/merge guard;
   - the M5 meaning audit;
   - the cost-log schema.

## Custody share

0 of 18 builder commits are custody-only (0%): 7 governance, 11 work (`tools/custody-share.py b9188f7^..472a385`).
