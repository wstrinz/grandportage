# Phase 0a: residual-witness contract extraction

Five new cases, GP-X332 through GP-X336, cover the distinct residual mechanisms in the six-parameter scope/pin/order/middle/slice test and its changed-modulus test. The intact finite-quotient positive control is GP-X319. GP-X123 already refuses promotion from one excluded witness or fiber to stronger parent emptiness (M1), and GP-X71 already refuses a receipt whose nested source fingerprint changed (N4). Those conclusions need no duplicate cases.

All new cases use the hash-bound retained historical fixture at 7991c9052f13e8dcaa78b5eae36f31663e080c1e. Each attempted conclusion and expectation was fixed before its route was wired. The probes call the pinned validate_fixture_value directly on in-memory mutations, so observed refusals are the named gates rather than the outer fixture digest.

| Mutation | Case | Gate | Exact observed boundary |
|---|---|---|---|
| LOCAL_EMPTY projection from one excluded witness | GP-X123 | Existing refusal | One excluded witness/fiber does not exclude its parent |
| Change Psi8 coefficient field from 15*t^3+1 to 15*t^3-1 | GP-X332 | N6 | Psi8, pullback and module no longer share the pinned coefficient algebra |
| Reverse pullback ring-variable order | GP-X333 | N7 | Ordered coordinates disagree across pullback and Psi8 certificates |
| Change nested source digest | GP-X71 | Existing refusal | The bound source fingerprint is no longer current |
| Replace r8_2's middle-zero explanation with an unexplained placeholder | GP-X334 | A4 | The deliberate absence of the middle residual loses its required algebraic rationale |
| Change c2_1 in the witness slice from zero to one | GP-X335 | N8 | The same witness result cannot be used on a different slice |
| Change the first coefficient of r_final to one | GP-X336 | W3 | The joint finite-witness modulus/equation check refuses |
| Intact finite quotient unit witness | GP-X319 | ACCEPT | Exact replay verifies the unit claim on the stated quotient |

The changed field is a change to the coefficient algebra, not to the point universe. Ring-variable order is an ordered cross-certificate binding, not generic byte canonicalization. GP-X334 does not turn a missing object into a named certificate; it records the loss of the stated middle-zero reason. GP-X335 changes the actual finite-witness slice, without claiming parent authority. GP-X336 reaches W3 before W5; the W3 predicate jointly checks modulus degree, squarefreeness, chain degree and sliced equations, so this extraction does not isolate which conjunct failed or claim Omega8 became a nonunit. GP-X320 remains a different W5 refusal for a false reported gcd degree.

## Replay and preservation

tools/check-corpus.py validated 377 cases, source anchors, and the pinned oracle. Full offline replay at reports/oracle-runs/20260928T203130963441Z.json: 362 AGREES, 12 KNOWN_DIFFERENCE, 1 DIAGNOSTIC_OBSERVED, 1 PENDING, 1 UNSUPPORTED. All five new cases AGREE. Compared with reports/oracle-runs/20260928T201826560097Z.json, all 372 old case files have the same SHA-256, and expectations, observed verdicts, statuses, routes, and layers are unchanged. GP-X236/X237 regenerated only per-run completion markers in diagnostic reason text; normalized reasons match. Earlier immutable runs were not edited.

Structured observations and hashes: reports/PHASE-0A-RESIDUAL-CONTRACT-EVIDENCE.json. This extraction does not change global coverage or gate status.
