# Phase 0a - Groebner producer and materialization

Fully read groebner_producer.py and test_groebner_producer.py plus verify.materialize_elimination_groebner. Twenty-eight offline tests pass; three live Singular tests were deselected.

Indexed basis rows and every matrix cell must be explicit, contiguous and unique. Polynomial canonicalization precedes reuse in generated programs; basis size is bounded before parsing.

The certificate proves contraction completeness only: source generators belong to the candidate basis ideal, critical pairs reduce to zero, and retained basis belongs to the target ideal. It omits basis-in-source witnesses. This is the intentional one-way boundary previously tested in Batch 47.

Materialization independently checks target generators in the source ideal through operation_output before recording both verdicts. Its invented-generator regression refuses without graph append. Legacy native operation-output replay still has the producer-trust weakness documented in Batches 24-25; this producer review does not repair it.

Artifact certificate is attached only after the exact checker accepts. Phase-two failure leaves no certificate. Graph-bound and producer checker summaries must agree.

Producer deadline spans both subprocess stages and host checkpoints with a shared arithmetic budget. Individual host operations may overrun before the next deadline check; timeout positivity does not explicitly reject NaN or infinity. These are resource-boundary follow-ups, not reproduced proof admissions.

Recording persists content-addressed objects before appending the prevalidated graph batch, reloads source and checks target IDs. Source-race checks are narrow; the append is explicitly not a crash-atomic transaction.

Offline tests include actual bounded Python subprocess output/blocked-input controls, but Singular responses and materializer recording identity are mocked. Three live Singular tests remain unexecuted.

Proposed follow-ups: require finite deadlines, document total resource limits, retain independent replay of both ideal inclusions, and specify atomic append/concurrency guarantees. These are recorded design considerations; frozen code is unchanged. All 352 corpus cases validate unchanged. No external campaign harvest, live Singular execution, Lean spike or publication. Phase 0 remains active.
