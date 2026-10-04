# Phase 0a 84.8 — geometric noncoverage and BASE coverage

The proposed GP-X56 reuse is rejected. X56 tests transporting a base-field EMPTY claim to an extension. Finding 84.8 tests the different attempted conclusion that a failed *geometric cover* refutes a cover over BASE points. The parent decision is `reports/PHASE-0A-CLOSURE-DECISIONS.json#/decisions/46`.

## Countermodel and pair

For parent `x²+1=0` over Q, the literal empty branch family covers every Q-point vacuously: there are no Q-points because `q²+1>0` for every rational `q`. Over the algebraic closure, `i²+1=0`, and the empty branch family misses `i`. Thus geometric noncoverage is true while BASE coverage is true. **Refusing a BASE refutation does not prove that a checker has established BASE exhaustiveness.**

| Case | Attempted conclusion | Expected and observed | Frozen classifier result |
| --- | --- | --- | --- |
| GP-X368 | Promote the failed geometric test to refuted BASE exhaustiveness | REFUSE / REFUSE | `NOT_GEOMETRICALLY_EXHAUSTIVE` |
| GP-X369 | Refute coverage in the declared algebraic-closure universe | ACCEPT / ACCEPT | `NOT_EXHAUSTIVE` |

`Exhaustive.lean:45,63,94,99,102` pins the vacuous-cover theorem, countermodel, and scoped classification. The frozen runtime regression at `tests/test_adversarial.py:5006,5020` tests the same verdict distinction; `grandportage/verify.py:1516` is the invoked classifier.

## Native representation and observation layer

The frozen graph requires at least two branch IDs (`grandportage/store.py:1729`), so it cannot represent a literal zero-branch partition. The two native cases use branches `B0` and `B1`, each with equation `1=0`. Both loci are empty; their union is the same empty set as the formal zero-branch family. The cases retain the literal family `[]` and the native encoding separately.

The native classifier was called on each declared point universe. Its backend responses were **injected**: `1` is reported outside `(x²+1)`, and the geometric cover test reports a hole with uncovered polynomial `1`. Those answers agree with the elementary exact point argument above, but the test output was not independently checked by a CAS or certificate replay. No persisted verdict or held mathematical claim is asserted.

## Replay and limits

The immutable baseline had 408 cases. The new run has 410: **393 AGREES, 14 KNOWN_DIFFERENCE, 1 DIAGNOSTIC_OBSERVED, 1 PENDING, 1 UNSUPPORTED**. Both new cases agree. Every prior case SHA-256, expected and observed verdict, status, layer and route is unchanged. Exact source pins, cases, injected calls, run hashes and preservation comparison are in the companion JSON.

- Baseline: `reports/oracle-runs/20260929T013956101499Z.json`.
- New run: `reports/oracle-runs/20260929T120626698944Z.json`.
- Evidence: `reports/PHASE-0A-BASE-COVER-REFUTATION.json`.

No live CAS, Lean compilation, kernel implementation, predecessor repair, or policy decision was performed. This is a bounded proposal for parent review.

Parent acceptance2026-09-29: read both neutral payloads, full probe and route/runner diff. Independently reran the two probes, validated410 cases/source anchors/pin, matched current runner/route/probe hashes to the immutable full replay, and verified all408 prior case hashes, expectations, observations, statuses, routes and layers unchanged. Accepted at the explicit injected-classifier layer; no full-replay repetition needed after read-only review. Finding84.8 extraction gap is closed.
