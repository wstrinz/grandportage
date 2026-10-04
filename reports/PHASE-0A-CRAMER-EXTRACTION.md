# Phase 0a Cramer clearing-exponent extraction

Two unintegrated, exact historical candidates are prepared: `GP-X406` refuses exponent one and `GP-X407` accepts exponent two. They bind the retained `class_v1.json` fixture, source adapter, test file, and history pin; they are not corpus cases and no oracle route or expectation was changed.

The replayed expression is `Phi_b0_compat = det5^2 * Lambda|det5-solve`, with `Lambda = VD - (3/2)*c2_3*t*E321`. The five Cramer columns are `c8_9`, `c7_7`, `c8_8`, `c7_6`, and `c8_7`, each over `det5`. The stored Lambda profile has one `c8_9^2` term. After `c8_9 = N_0/det5`, one power leaves an uncancelled denominator; two powers clear the committed expression.

The focused offline replay used only the pinned adapter's `validate_fixture_value` entry on the 1,487,286-byte fixture. It completed in 102.191019 seconds. It reconstructed the 3,137-term `Phi_b0_compat` at exponent two and verified a nonzero polynomial-division remainder at exponent one. It did not invoke native replay, native binding checks, fixture construction, CAS, campaign input, graph operations, or source binding checks.

After the focused replay, the two candidate files were repackaged to `corpus/case.schema.json`: `seed: null`, `REGION`, historical bindings and limits under `inputs`, and literal `gp-history` adapter/test anchors at pin `7991c9052f13e8dcaa78b5eae36f31663e080c1e`. JSON Schema and those anchors validate. The recorded focused output predates only this container/schema correction; fixture, adapter, test hashes, inputs, guards, and arithmetic observations are unchanged, so the 102-second replay was not rerun.`n`nThe result is limited to this frozen historical Cramer replay. It supplies no general denominator theorem, source equivalence, nonzerodivisor result, rational witness, geometry, graph effect, or live/native authority. `GP-X119` and `GP-X120` remain separate nonzero/nonunit controls and do not cover this threshold.

