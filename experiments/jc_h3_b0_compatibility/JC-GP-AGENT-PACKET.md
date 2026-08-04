# JC `b=0` compatibility / `Phi_b0_compat` GP rendezvous packet

**Audience:** Grand Portage implementation agent.  
**Date:** 2026-08-02.  
**JC native head:** `b40fe71` or later on `main`.  
**Scope:** one isolated adapter/campaign copy; no canonical campaign migration.

## Why this seam is ready

The native JC lane has frozen the first uniform source-compatibility class on
the exact localized `b=0` residual base locus

```text
X_b : b=0, R=0, A=0, OB=0
      pin/S2 inherited; a,p,det5 declared units.
```

After the already-certified five-row Cramer solve, the final two affine rows
in `s=c7_5` have compatibility eliminant `Lambda`.  Clearing the chart
denominator gives the exact base polynomial

```text
Phi_b0_compat := det5^2 * Lambda|_{det5-solve}.
```

The native checker proves that this class is **nonzero but not a unit** in the
localized coordinate ring: the tested length-two family gives a nonvanishing
unit fiber, while an explicit legal degree-14 quotient-ring witness lies on
`Z(Phi_b0_compat)`.  This is only the materialized depth-6/7 compatibility
problem.  Actual-source membership beyond it remains open.

## Frozen native inputs

Read from `C:\Users\wstri\dev\math-stuff`:

- `d2_plane_72_108/F2_H3_B0_UNIFORM_LAMBDA.md`
- `d2_plane_72_108/f2_h3_b0_uniform_lambda.py`
- `d2_plane_72_108/f2_h3_b0_uniform_lambda.json`
- `d2_plane_72_108/F2_H3_B0_COMMON_ROOT.md`
- `d2_plane_72_108/f2_h3_b0_common_root.py`
- `d2_plane_72_108/f2_h3_b0_common_root.json`
- `d2_plane_72_108/lean/JC/SourceIncidenceBezout.lean`
- `d2_plane_72_108/f2_h3_source_incidence_bezout_adapter.py`
- `d2_plane_72_108/H3_LOCALIZED_CAS_PILOT.md` (tooling provenance only)

Run the native uniform checker and bind all digests it reports.  Do not
reconstruct the million-term Res61 object or treat CAS output as authority.

## Phase A: available now

Build the narrowest disposable GP adapter that can represent and replay:

1. the exact model and coefficient domain `K=QQ[t]/(15t^3+1)`;
2. restriction to `b=R=A=OB=0` and declared localization at `a,p,det5`;
3. the five-row chart solve and denominator-cleared identity defining
   `Phi_b0_compat`;
4. the tested-family unit/nonvanishing control;
5. the degree-14 quotient-ring zero witness, including explicit guard-unit
   cofactors/coprimality receipts;
6. the exact authority ceiling and first open obligation.

Prefer graph effect `NONE` until every context change is bound.  If existing GP
semantics cannot license “nonzero and nonunit in this localized ring,” return
the smallest missing checker/authority type rather than weakening the claim.

Useful supported output would be phrased like:

> GP independently replayed the identity transport from the frozen affine
> compatibility block to `Phi_b0_compat`, verified one legal nonvanishing
> control and one legal zero witness, and therefore records the class as
> neither zero nor a unit on the stated localized materialized-depth model.

## Phase B: rendezvous, do not block Phase A

A local JC lane `h3-source-compatibility-module` is currently freezing the
block-triangular `M(z)u+r(z)` packet, ranks, left syzygy, and augmented minor.
When that native commit lands, bind it only if it supplies a smaller or more
semantic transport contract for the same digest-bound `Phi_b0_compat`.

Do not infer its contents in advance, edit its files, or teach the research
lane GP schema.  If Phase A is complete first, stop with an explicit rendezvous
field naming the native packet/digest still awaited.

## Standing semantic traps

1. The native packet enum is `GENERIC_NONZERO_DIVISOR`, but it explicitly does
   **not** prove componentwise nonzerodivisor status.  GP must encode only
   **nonzero and nonunit** unless a later primary/component certificate lands.
2. Name this object `Phi_b0_compat` (or another digest-bound unambiguous name).
   Do not collide it with older JC polynomials also named `Phi`.
3. `det5` is a genuine multivariable localization guard uniformly, although it
   specializes to a unit of `K` on the tested length-two family.
4. The degree-14 witness is over a nonzero quotient algebra/field extension;
   it is not asserted `K`-rational.
5. A zero of `Phi_b0_compat` satisfies only the materialized depth-6/7 bodies.
   It grants no all-orders lift, source sufficiency, H8, H3, or `(75,125)`.
6. The full WSL msolve/M2/Julia pilot remains exploration tooling outside any
   routine or canonical GP gate.  Its compact conjugate/norm witness may be
   rebound only through the exact native replay.

## Mutations / stop rule

Require refusals for changed model digest, chart guard, clearing exponent
`2 -> 1`, eliminant scalar `(3/2)at -> (2/3)at`, altered witness polynomial,
zero/nonzero direction reversal, `K`-rationality promotion, and any
nonzerodivisor/source/H3/global promotion.

Stop after one disposable replay ledger plus either:

- a narrowly licensed GP result with explicit ceiling; or
- the smallest exact missing GP semantic/evidence obligation.

No canonical campaign repin or migration, no broad primary decomposition, no
new source body/depth, and no shared JC front-door edits.

