# Existing-case reuse review: 24 obligations

All 24 `existing_case` obligations were reviewed against their case payloads and stored oracle routes. Sixteen are exact premise/conclusion/mechanism reuse. Seven are only partial: `73.4`, `73.5`, and `75.2` depend on the known-difference refusal for `GP-X260`; `75.7` and `84.9` depend on known-difference partition negatives `GP-X270` and `GP-X274`; and `83.7` plus `85.3` use diagnostic-only `GP-A03a`.

`83.2c` is missing. Its proposed case, `GP-A13-ambient`, accepts an already ambient identity and has the opposite premise from the needed refusal of a derived identity after dropping `x=0`. The JSON proposes the exact paired control and retains `GP-A13-ambient` as its positive case.

The review preserves all original IDs, reconciles to 24 obligations, and does not change corpus expectations or oracle observations.
