# Expression transport after the v0.35 release candidate

`lean/GrandPortage/ExpressionTransport.lean` extends the bounded interpreter
with an explicit map preserving zero, one, addition, multiplication and negation.
`eval_map` proves by structural induction that evaluation commutes with this map.
It needs neither ring laws nor injectivity: those are stronger assumptions than
this syntax-level fact requires. Operation maps also compose.

Two semantic consequences have different directions:

- `holds_transport` sends a source solution to a target solution.
- `emptiness_pullback` derives source emptiness from target emptiness.

The map alone does not transport source emptiness forward. The concrete map
from integers to Gaussian integers preserves every operation and transports the
sample certificate equality. Nevertheless x*x+1 has no integer root and has
the Gaussian root (0,1). `forward_emptiness_counterexample` proves both facts;
`gaussian_has_no_ordering` in the preceding interpreter identifies the missing
contradiction interpretation. No assertion about a general complex-field
formalization is needed for this counterexample.

This sharpens the four-judgment program: equality preservation is an algebraic
fact; interpreting equality as impossibility is an additional semantic step.
Receipt freshness remains a third, independent operational obligation.

The generic pullback theorem does not authorize a new GP edge. Connecting it to
GP requires a checked operation-map representation, compatible point universes,
and binding the certificate generators to the current endpoints. The expression
language still lacks rational constants and their denominator obligations.
The [unit-cofactor follow-up](ATLAS-FOLLOWUP-V1.md) now supplies a second
certificate interpretation and characteristic-sensitive graph composition.

Validation: `lake build` passed all 31 jobs, with only the two existing linter
warnings. The module is imported by the aggregate build, so hosted Lean CI checks
its proofs. Python behavior, graph format and kernel epoch are unchanged.
