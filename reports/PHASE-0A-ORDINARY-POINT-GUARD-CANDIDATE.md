# Ordinary-point guard candidate design

Three neutral candidates for ARR-G09's ordinary equation-bearing and equation-free witness paths. Design only: all observed native/diagnostic verdicts and receipts are null. No corpus IDs or runnable oracle routes are assigned. The 456 cases, routes, replays and pending A24 remain untouched.

## Main finding

At pin `ac4155787207e2847d248cffed7be871d5dcd577`, `point_witness` sends ordinary witnesses to Singular even when `generators=[]`. It builds `expressions = gens + guards`, evaluates every expression, then separately requires equations to vanish and guards to be nonzero. There is no equation-free success early return in this pinned implementation. An empty equation list with guard `x` still evaluates `x`.

The default production route cannot supply a faithful fresh observation without external CAS. Backend availability was not tested. Existing tests contain `_ExactPointBackend`, a limited evaluator for `0`, `x`, `y`; it can exercise the actual guard-decision code for these literal0/1 candidates if separately commissioned. Such an observation remains a diagnostic seam: it is not Singular execution, a general rational checker, a native receipt, epoch-1 admission or current held authority. Nothing was executed in this pass.

## ordinary-equations-vanishing-guard

```json
{
  "model": {
    "id": "M",
    "desc": "Minimal ordinary rational open locus",
    "characteristic": 0,
    "coefficient_domain": "Q",
    "point_universe": "BASE",
    "ring_vars": [
      "x",
      "y"
    ],
    "generators": [
      "y"
    ],
    "open_conditions": [
      "x"
    ]
  },
  "claim": {
    "id": "W",
    "model": "M",
    "kind": "NONEMPTY",
    "statement": "The recorded open model contains the displayed rational point.",
    "scope": "Q",
    "witness_kind": "EXHIBITED",
    "witness_point": {
      "x": "0",
      "y": "0"
    }
  },
  "witness_field_present": false
}
```

Expected contract: **REFUSE**; the source verifier spelling is `NOT_A_POINT`. This expectation is a design/source assertion, never a fresh runtime result. Reject this offered witness. Do not infer the model is EMPTY or that no other point exists.

Exact literal values: y=0; guard x=0. This is transparent arithmetic reasoning, not an invented reference checker.

Primary retained test: `oracle/checkout/tests/test_adversarial.py`, lines 4493-4500. The test uses the same equation, point and guard values; its model omits explicit coefficient domain/universe. The candidate records Q/BASE explicitly; graph admission is unexecuted. Omit `witness_field` entirely to reach the ordinary path. No inherited `established_by: RAN`, receipt or success label is copied into these neutral inputs.

## ordinary-equation-free-vanishing-guard

```json
{
  "model": {
    "id": "M",
    "desc": "Minimal ordinary rational open locus",
    "characteristic": 0,
    "coefficient_domain": "Q",
    "point_universe": "BASE",
    "ring_vars": [
      "x"
    ],
    "generators": [],
    "open_conditions": [
      "x"
    ]
  },
  "claim": {
    "id": "W",
    "model": "M",
    "kind": "NONEMPTY",
    "statement": "The recorded open model contains the displayed rational point.",
    "scope": "Q",
    "witness_kind": "EXHIBITED",
    "witness_point": {
      "x": "0"
    }
  },
  "witness_field_present": false
}
```

Expected contract: **REFUSE**; the source verifier spelling is `NOT_A_POINT`. This expectation is a design/source assertion, never a fresh runtime result. Reject this offered witness. Do not infer the model is EMPTY or that no other point exists.

Exact literal values: guard x=0. This is transparent arithmetic reasoning, not an invented reference checker.

Primary retained test: `oracle/checkout/tests/test_adversarial.py`, lines 4509-4520. The test uses the same equation, point and guard values; its model omits explicit coefficient domain/universe. The candidate records Q/BASE explicitly; graph admission is unexecuted. Omit `witness_field` entirely to reach the ordinary path. No inherited `established_by: RAN`, receipt or success label is copied into these neutral inputs.

## ordinary-equation-free-nonvanishing-guard

```json
{
  "model": {
    "id": "M",
    "desc": "Minimal ordinary rational open locus",
    "characteristic": 0,
    "coefficient_domain": "Q",
    "point_universe": "BASE",
    "ring_vars": [
      "x"
    ],
    "generators": [],
    "open_conditions": [
      "x"
    ]
  },
  "claim": {
    "id": "W",
    "model": "M",
    "kind": "NONEMPTY",
    "statement": "The recorded open model contains the displayed rational point.",
    "scope": "Q",
    "witness_kind": "EXHIBITED",
    "witness_point": {
      "x": "1"
    }
  },
  "witness_field_present": false
}
```

Expected contract: **ACCEPT**; the source verifier spelling is `VERIFIED`. This expectation is a design/source assertion, never a fresh runtime result. Validate the offered point at its own open model. Do not infer transport or current held authority.

Exact literal values: guard x=1. This is transparent arithmetic reasoning, not an invented reference checker.

Primary retained test: `oracle/checkout/tests/test_adversarial.py`, lines 4509-4514. The test uses the same equation, point and guard values; its model omits explicit coefficient domain/universe. The candidate records Q/BASE explicitly; graph admission is unexecuted. Omit `witness_field` entirely to reach the ordinary path. No inherited `established_by: RAN`, receipt or success label is copied into these neutral inputs.

## Minimum positive coverage

The third candidate directly contrasts the equation-free negative: `x=1` on `D(x)` should be accepted. This also prevents treating the backend's aggregate all-zero boolean as the point verdict. The equation-bearing positive `generators=["y"]`, guard `x`, point `(1,0)` is already asserted in pinned test lines4502-4506 through the same seam. It is retained as primary source support, not an admitted existing case or fresh pass; a fourth payload is unnecessary for this minimum reviewable design. Actual production evidence for both branches remains absent.

## Native call path and observation limits

`verify_all` dispatches NONEMPTY structured witnesses needing verification at verify.py2798-2801. `point_witness` checks claim/model/expression prerequisites, then uses `witness_field` at1929 to choose extension arithmetic. These candidates omit it and enter the ordinary path at1946. Lines1949-1970 evaluate equations plus guards through `SingularBackend.evaluate_point`; cas.py1185-1190 delegates to `check_witness`, which builds the Singular map and calls `_execute` at1542. verify.py1972-2000 ignores the aggregate boolean, divides expression rows at `len(gens)` and returns VERIFIED or NOT_A_POINT. A failed offered witness does not prove the model empty.

The existing test evaluator at test_adversarial.py4461-4481 reports exact literal x/y rows and leaves the verdict decision to production `point_witness`. Its string comparison is suitable only for the displayed0/1 literals. It bypasses the production CAS parser, coordinate validation, execution identity and receipt lifecycle. The test `_graph` helper at32-36 applies events to `S.Graph` and validates them; it does not assert current epoch-1 native admission. Do not invent an oracle route/verdict or present a future seam result as fresh native refusal. Unsupported production observations remain null.

## X349 comparison

X349 uses `Q[a]/(a^3-2)`, point `x=a`, equation and vanishing guard `x^3-2`, with ALGEBRAIC_CLOSURE universe. ROUTES gives `q2_exact/native_exact_cubic`, a CAS-free simple-number-field check. `number_field.check_extension_witness` at248 and its equation/guard loops267-281 provide that distinct path. It has an explicit field and nonempty generators. It cannot substitute for either ordinary Singular-backed branch or the equation-free omission mechanism. Only the guard rule is related; no literal reuse is claimed.

## Pinned primary anchors

HEAD was read as `ac4155787207e2847d248cffed7be871d5dcd577`; selected tracked source diff against HEAD returned0. These are raw checkout file SHA256 hashes, with focused read extents rather than a full-file reading claim.

| File | Lines | SHA256 |
|---|---:|---|
| `oracle/checkout/grandportage/verify.py` | 1827-1828 | `51ee50fd4be7e8f0f6b2cdd10f680ac7060ef8f91f1f424290a342e3c7ce9c03` |
| `oracle/checkout/grandportage/verify.py` | 1873-2000 | `51ee50fd4be7e8f0f6b2cdd10f680ac7060ef8f91f1f424290a342e3c7ce9c03` |
| `oracle/checkout/grandportage/verify.py` | 2798-2801 | `51ee50fd4be7e8f0f6b2cdd10f680ac7060ef8f91f1f424290a342e3c7ce9c03` |
| `oracle/checkout/grandportage/cas.py` | 1185-1190 | `b33ed86b25361eb9c6e8993b96f12ae5359fe12c20bf4d729cbc29374cdab453` |
| `oracle/checkout/grandportage/cas.py` | 1483-1557 | `b33ed86b25361eb9c6e8993b96f12ae5359fe12c20bf4d729cbc29374cdab453` |
| `oracle/checkout/tests/test_adversarial.py` | 32-36 | `1150aa49c0596af1a9816a71f44694838e6fef17370a2fc8337b453b3d43c9f8` |
| `oracle/checkout/tests/test_adversarial.py` | 4461-4520 | `1150aa49c0596af1a9816a71f44694838e6fef17370a2fc8337b453b3d43c9f8` |
| `oracle/checkout/grandportage/number_field.py` | 248-281 | `bb815c2cfe03feb2eaae94756e5d41fcf8d5b836ba50d97c750fd52a7cad877e` |
| `oracle/checkout/tests/test_guard_release.py` | 121-131 | `62c81e677be9145b9694e9f4e1cfdb951af93e22a7991e191d06af93788d67a0` |

The JSON companion also pins ARR source report, parent D2 note, X349 payload and ROUTES hashes. ARR-G09 remains historical implementation evidence with later0.26 source-reported recovery, not current execution.

## D2 qualification carried forward

`PHASE-0A-GUARD-SNAPSHOT-PARENT-NOTES.json` records that retained live source tests assert success for both96 and97 variables. The pinned `test_guard_release.py` lines121-131 parametrize `[96,97]`, choose the historical `fail-97vars.json` filename for97, then `assert ok, detail` for both. DK REPORT515-528/570-573 describes the historical failure; the filename is never frozen refusal authority. No live test was run, and the completed reconciliation report was left unchanged as directed.

## Stop boundary

Only this one family's minimum candidate design is complete. No backend/test/campaign/Lean execution, extraction, corpus/adapter/route/tracker/replay edit or commit occurred. Scaling, migration, retry and display work stays uncommissioned. Parent owns final admission and any separately commissioned observation.
