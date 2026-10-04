# Historical GP oracle inputs

These 112 files are verbatim Git blobs from 7991c9052f13e8dcaa78b5eae36f31663e080c1e, the parent of the campaign-extraction release. Its ancestry to the main v0.37 oracle pin was checked before recovery. PIN.json records original paths, Git blob IDs, SHA-256 hashes and byte sizes. This is a historical oracle snapshot, not rework implementation.

The corpus validator checks every snapshot byte and source anchor before importing the adapter. Each replay report binds PIN.json by SHA-256; historical cases identify the older adapter revision separately from the current runtime commit. Do not edit recovered files or normalize their line endings.

The seam adapter uses the pinned v0.37 evidence module; the formalization ledger uses its kernel. It checks stored bindings and the conditional report boundary; it does not rerun the native reduced-row derivation or prove the missing upstream map. check_native_bindings/check_bindings remain false. No companion-campaign files were read or copied.

Semantic negative probes use the inner manifest validator so the separate outer file hash cannot mask premise checks. The altered-revision probe follows the historical regression by repinning only the scratch fixture digest. A separate probe rejects changed bytes under the original digest. Scratch files stay under tmp.

The formalization snapshot adds direct source pointers for transport, premise and endpoint cases. Stored expected-verdict mismatches (ASY8) are regression diagnostics, not authority refusals. Reports bind the manifest version used for that run; prior versions remain in Git history.

The p-axis snapshot replays an exact localized unit-ideal proof. Its graph receipt tests use the original fabricated Singular execution descriptor solely to exercise binding. No real backend execution or native parent regeneration is claimed. Changed contexts are tested for stale receipt currency before graph structural validation.

Batch 7 completes the first reading pass over all 29 deleted test files. The snapshot totals 15,874,307 bytes and includes the GP-owned fixtures, adapters, historical review outputs and Lean source snippets needed for offline regression. Snapshot inclusion is not a claim of full implementation review. Companion files were not read or copied. The tests referencing Lean names do not compile those theorems.

Run `python -B tools/run-historical-review.py` for the selected offline regressions. The runner explicitly excludes 27 functions requiring companion data and two requiring live Singular; it permits Git for provenance and a synthetic local fixture repository. SymPy 1.14.0 is required for the exhaustive formula reconstruction. See reports/HISTORICAL-REVIEW-RESULTS.json for per-instance results and corpus/history/DELETED-TEST-REVIEW.json for every function disposition.
