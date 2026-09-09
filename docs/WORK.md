# Unfinished work and accounting-only checks

An exhausted budget records an unfinished attempt, not a mathematical result.
Create a JSON file such as `attempt.json`:

```json
{
  "id": "TRY-BS21-7",
  "family": "F-BS21-TEMPLATES",
  "locus": "template-7",
  "disposition": "UNRESOLVED",
  "reason": "TIMEOUT",
  "budget": {"value": 75, "unit": "seconds"}
}
```

```console
gp work --file attempt.json
gp check
gp work --resolve TRY-BS21-7 --why "Retried; the resulting evidence is recorded separately."
```

The family must already exist and be live. IDs identify individual attempts;
retries use new IDs. Reasons are TIMEOUT, CAP, or BUDGET. Budgets require a
finite nonnegative number and a nonblank unit. The writer supplies UTC time.
An explicit resolution names one preceding unresolved attempt and retains the
reason. It does not declare EMPTY, NONEMPTY, completeness, or any other claim.
Multiple attempts at a locus remain independently visible until resolved.

`gp check` and `portage_check` list unresolved attempts under their families.
These records do not contribute to coverage, satisfy premises, affect verifier
fingerprints, or suppress findings. An unresolved attempt at a subsequently
retired family remains visible until explicitly resolved.

The append-only operational log is `.portage/work.jsonl`, schema
`grand-portage-work/v1`. It is separate from graph format 7 and kernel epoch 11.
Each persisted record has `schema`, `id`, `created_at`, and `disposition`, plus
the fields in the example, or `resolves` and `why` for RESOLVED. Unknown fields,
duplicate IDs, invalid timestamps, and invalid resolutions refuse. For an
explicit graph named `other.jsonl`, its companion is `other.jsonl.work.jsonl`.
Merged reads combine the companions of the selected graphs; writes select
exactly one graph. Copy the companion with the graph when transferring the
operational history. Older GP versions can still read the mathematical graph
but do not display this new companion.

Writers validate under an exclusive `.lock` file and flush before releasing it.
If a writer crashes, inspect the complete JSONL log and confirm no writer is
active before removing its abandoned lock. GP does not guess that a lock is
abandoned. Malformed work logs are reported, not silently skipped. The
mathematical hook deliberately retains its independent full-graph contract.

## Accounting without field-scope checking

```console
gp check --seam unchecked
gp check --seam unchecked --json
```

This selects counts, evidence direction, cross-counts, supersession, stale
references, doubts, evidence/citation obligations, and explicit open-premise
slots. It prints `ACCOUNTING ONLY: field-scope transports were not checked.`
even in quiet mode. JSON includes `seam: "unchecked"` and an empty `clean`
list. A zero exit means no accounting finding at the selected severity floor;
it is not a transport license. MCP `portage_check` supports the same `seam`
option and never labels inferences clean in unchecked mode.

Graph parsing and structural validation still run. In particular, the current
point-universe omission/mismatch guard still refuses an ill-formed graph.
This mode is not a way to bypass the P0 guard. It does not rewrite graphs,
mint evidence, clear hook baselines, or permit full-check `--since` comparison.
Unchecked receipts cannot be used as full-check receipts. Ordinary `gp check`,
the hook, and baseline commands continue to run the complete checker.

## Classification without completeness

Keep the missing statement explicit in an inference:

```json
{"required_kind": "PREDICATE", "at": "M-23-4-REAL",
 "missing_why": "The retained census has not been shown exhaustive."}
```

Use this alongside actual model premises. The slot licenses nothing and names
the proof still needed. UNRESOLVED work cannot close it. A family claim cannot
be transported as a model claim in v0.32: the declaration refuses with a
discharge, preserving the family and its enumeration obligation. An explicit
family-to-model composition contract is reserved for the later epoch.
