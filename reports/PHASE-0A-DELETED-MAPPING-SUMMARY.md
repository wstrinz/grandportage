# Phase 0a deleted-test mapping review

Reviewed exactly 42 closure-matrix rows with `prior_disposition=covered_by_existing_cases`, against the pinned historical checkout at `7991c9052f13e8dcaa78b5eae36f31663e080c1e` and their cited neutral cases.

| Classification | Count |
|---|---:|
| mapped | 1 |
| mapped_outer_hash_only | 10 |
| partial | 22 |
| unresolved | 9 |

`mapped` means the candidate has the same policy conclusion and failure mechanism. `partial` preserves a policy mechanism but leaves fixture-specific premises/assertions unmatched. `mapped_outer_hash_only` is deliberately limited to byte/content binding; it is not arithmetic or semantic validation. `unresolved` has no candidate with the needed independent mechanism.

The JSON report contains every exact pinned test body, candidate-case source pointer, equivalence argument, distinction, and confidence. No corpus expectation or oracle status was changed.
