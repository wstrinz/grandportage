# Native receipt request: source depth 2--6 composition

## Status: fulfilled downstream, with one narrower seam remaining

JC commit `cb3136c` landed Option A as a 23-step certificate plus two
residuals. GP's independent consumer verifies it completely and welds its
inputs and outputs to existing GP fixtures. The landed artifact is sufficient
for the exact ordered chain *inside its 25 bound face tables*.

It does not separately prove that those face tables are coefficient
extractions of the raw E-system rows. Consequently the sentence below saying
Option A could bind an "actual-source necessary condition" was optimistic by
one operation boundary. GP correctly emits no actual-source graph edge. Any
follow-up request should now be only a bounded raw-row-to-face-table extraction
certificate; the solve chain itself needs no further materialization.

The earlier boundary-only depth-6 receipt was sufficient for GP to validate
the final `R2B` and `beta` sparse maps and certify both boundary-stratum rewrites. It was
not sufficient to license the transition from the actual-source E-system to
those polynomials: each intermediate solve value is represented only by a term
count and SHA-256.

The original useful follow-up was not another summary receipt. It was one of
the following proof-carrying forms, in preference order.

## Option A: exact ordered step records

Start after the already-consumed second face (depth 1). For each of the 20
rungs at depths 2--5 and the three solved depth-6 rungs, retain:

- depth, row, source slot, and pivot coordinate;
- the exact post-prior-substitution equation as a native sparse polynomial;
- the exact pivot coefficient and its `t`-unit witness;
- the exact solved value as a native sparse polynomial;
- any cofactor modulo `15*t^3+1` needed to normalize the equation;
- input and output generator-state fingerprints;
- the ordered list of prior substitutions included in the state.

For the pivot-free rows `E[2,21]` and `E[3,22]`, retain the exact final
post-substitution equations and their equality to `R2B` and
`alpha*c7_5+beta`, again with normalization cofactors if the equality is only
modulo the pin.

This is enough for `localized_triangular_solve_chain_v2` plus the v0.20
proof-composing adapter to replay the march and bind an actual-source necessary
condition.

## Option B: compact straight-line certificate

If serializing every expanded state is too large, expose a closed exact
straight-line program whose inputs are the second-face generators and whose
outputs are the 23 solved values plus the two residuals. Every instruction must
use a bounded operation GP can replay—addition, multiplication, rational scale,
substitution, and reduction by an explicit multiple of `15*t^3+1`. Bind the
program, input state, output maps, and variable order by full digests.

A recurrence theorem plus a finite list of exceptional boundary steps is also
acceptable if its semantics is stated and checked in Lean and the concrete
initial conditions are exact.

## Not sufficient

The following remain useful provenance but cannot earn the source edge:

- hashes and term counts without polynomial bodies;
- random-point agreement;
- a rerun of the native verifier that checks the same frozen commitments;
- prose saying the producer performed the substitutions;
- only the final residual maps, even when those maps are exact.

No GP-native JSON is required from the JC research lane. A native certificate
with stable field names is preferable; the isolated adapter will translate it.
