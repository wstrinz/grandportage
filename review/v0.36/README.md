# v0.36.0 repairs

Independent branch from released v0.35; format 8 and epoch 12 unchanged.
Native executions retain in-band version identity and refuse probe disagreement
or mixed traces. No executable hashing or retry policy is introduced.
Read surfaces describe contextual gates and interpreter requirements, distinguish
unlicensed claims from semantic loss, and warn about prose predicates with gp lint.
New campaign charters require formulas; existing graphs remain legal.
Research references are pinned to PR #3; this release is independent of new
read-model implementation work. Validation is recorded in validation.txt.

The sweep also corrected the MCP transport-table handler, which still printed
Boolean base-change policy after the CLI table had been repaired in v0.35.
