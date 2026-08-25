# v0.30 compatibility repair and CFG23 assay receipt

Lane: `gp-v030-compatibility-assay-v1`. Base: `9f49e4f` (Release v0.30 native
witness semantics). Scope: repair a P0 historical-format read regression,
prove it against the real CFG23 campaign graph, and exercise the release's
new native witness/diagnostic machinery on that real data. No matroid or
`GF(2)` support was added; see `README.md`'s "Remaining boundary".

## P0 defect: historical meta validation was not format-conditional

**Symptom, exactly as reproduced by DKC** on the untouched, valid CFG23
format-6 graph:

```
gport --root <CFG23-copy> check --full
line 1: historical meta event has wrong fields; extra: implementation
```

**Root cause.** `graph_format` 5 (commit `59e119c`, "Expose exact
implementation identity and diagnostics") added a closed `implementation`
identity to every meta event; formats 1-4 never had one.
`validate_meta_for_read` (`grandportage/format.py`) was introduced later
(`fb72a34`) when the *current* format was still 5, so its historical-header
field set `{"ev", "graph_format", "kernel_epoch", "created_with"}` was correct
for every format it needed to validate at the time (1-4). When `GRAPH_FORMAT`
later advanced past 5 and then 6 (`d798f6f`, `9f49e4f`), format 5 and then
format 6 themselves became *historical* inputs -- but the historical-header
field set was never updated to admit the `implementation` field those formats
actually carry. Direct reads of any format-5 or format-6 graph therefore
failed, while migration succeeded only because `migration.py` reads raw
events and replaces the header outright, never calling
`validate_meta_for_read` on the source.

**Fix.** `grandportage/format.py`: `IMPLEMENTATION_IDENTITY_MIN_FORMAT = 5`
marks the boundary. `validate_meta_for_read` now accepts the four-field
header for formats 1-4 and the five-field (`+implementation`) header for
formats 5 and 6, structurally validating the recorded identity via a new
shared `_validate_implementation_identity` helper (factored out of
`validate_meta`) -- but, per the packet, **never** asserting that the
recorded identity matches the implementation doing the reading. An archival
header describes the build that wrote it, not this one.

**Migration follow-up.** Independent intake found that direct reads were fixed
while migration could still launder a malformed historical header by replacing
it before validation. `migrate_kernel_epoch` now applies the same historical
read boundary before rewriting a format-5/6 header. Missing, malformed, or
internally inconsistent implementation identities are rejected even in
`--dry-run` mode. The format-5 fixture is pinned to the historically possible
v0.25.0 format-5/kernel-10 writer (`fb72a34`), rather than borrowing a later
format-6 identity.

**Reproduction evidence.** Checked out `grandportage/format.py` at base commit
`9f49e4f` into an isolated copy and ran the unmodified
`validate_meta_for_read` against the real first line of
`campaigns/cfg23/.portage/graph.jsonl` (`graph_format: 6`, real
`implementation` identity, `source_commit: d798f6f7...`): it raised exactly
`historical meta event has the wrong fields; missing: (none); extra:
implementation`. The fixed worktree code accepts the same line unchanged and
reads the whole graph directly (`gp check --full` succeeds, see below).

## Fixtures and adversary tests (`tests/test_format_epoch.py`)

25 new tests, including:

- `REAL_CFG23_FORMAT6_META`: a byte-identical copy of the real graph's first
  line, used as a regression pin (`test_real_cfg23_format6_meta_reads_directly`,
  `test_real_cfg23_format6_meta_migrates_to_current_format`).
- Format-5 and format-6 direct-read and migration round trips.
- Adversaries: missing `implementation` on formats 5/6 (rejected); `implementation`
  present on formats 1-4 (rejected as `extra`); malformed `implementation` shape,
  disagreeing `graph_format`/`kernel_epoch`, unsupported identity schema,
  non-boolean `source_dirty` (all rejected with format-specific diagnostics);
  and an explicit check that the recorded identity is never compared against
  the current build's own version/commit.

## CFG23 assay: copy, direct read, migration, authority ledger

The campaign `.portage` directory is read-only; the complete directory
(`graph.jsonl` + `artifacts/` + `migrations/`) was copied to an isolated
scratch root and assayed there. Graph: 6 models, 9 claims, 0 inferences,
8 verdicts, `graph_format` 6, `kernel_epoch` 11.

**Direct archival read** (unmodified copy): `gp check --full` runs cleanly --
4 `TRIAGE` findings (untested witness/identity claims awaiting `gp verify`,
exactly as authored), 0 findings at or above `UNSOUND_PREMISE`.

**Migration to format 7**: `gp migrate --to-current-kernel` succeeds
(audited, non-destructive; source untouched, sha256-fingerprinted).

**Before/after verdict-authority ledger** (`P.current_verdict` for every
persisted verdict):

| verdict | subject | verifier/version | kernel_epoch | BEFORE (format 6) | AFTER (format 7) |
|---|---|---|---|---|---|
| `v.C-CT1-QI-WITNESS.70d4d98e...` | witness | `verify.point_witness`/3 | 11 | not current: *epoch-0 verdicts are compatibility history only* | **current**: `current` |
| `v.C-CT1-QI-WITNESS.88fe5309...` | witness | `verify.point_witness`/3 | 10 | not current: *epoch-0 ... history only* | not current: *kernel epoch does not match* |
| `v.CL_FIELD22_SAMPLE_INCIDENCE.f49fd2af...` | claim | `verify.identity`/2 | 11 | not current: *epoch-0 ... history only* | **current**: `current` |
| `v.CL_FIELD22_SAMPLE_INCIDENCE.75728c3e...` | claim | `verify.identity`/2 | 10 | not current: *epoch-0 ... history only* | not current: *kernel epoch does not match* |
| `v.CL_FIELD26_SAMPLE_INCIDENCE.fbda9990...` | claim | `verify.identity`/2 | 11 | not current: *epoch-0 ... history only* | **current**: `current` |
| `v.CL_FIELD26_SAMPLE_INCIDENCE.78ad4a95...` | claim | `verify.identity`/2 | 10 | not current: *epoch-0 ... history only* | not current: *kernel epoch does not match* |
| `v.CL_ORBIT_A0_AUT_LIFT_RECON_INCIDENCE.f4b18365...` | claim | `verify.identity`/2 | 11 | not current: *epoch-0 ... history only* | **current**: `current` |
| `v.CL_ORBIT_A0_AUT_LIFT_RECON_INCIDENCE.ab09a02b...` | claim | `verify.identity`/2 | 10 | not current: *epoch-0 ... history only* | not current: *kernel epoch does not match* |

**Reading the ledger.** BEFORE, direct format-6 reads treat every verdict as
inactive compatibility history -- that is a property of *reading an archival
format directly*, not a mathematical judgement, per `CURRENT.md`: "Graph
syntax compatibility and mathematical authority are separate." AFTER
migration to format 7, the four verdicts whose `kernel_epoch` (11) already
equals the current kernel epoch, and whose verifier identity
(`verify.identity`/2, `verify.point_witness`/3) is unchanged, **regain current
status deterministically** -- confirming the acceptance gate: no
unchanged verifier identity in the same kernel epoch was silently revoked.
The three current `VERIFIED` identity verdicts license authority; the current
`UNVERIFIED` witness attempt is merely visible and retryable and licenses no
positive conclusion.
The four `kernel_epoch: 10` verdicts correctly remain stale before and after,
for the honest reason that their kernel epoch really did advance (10 -> 11);
that is real drift, not a migration artifact.

## Native `Q(i)` witness on `M-CT1-SAT-5GUARDS`

The task-packet coordinates (`a^2+1=0`;
`t1=(-1-a)/2, t2=(1-a)/2, t3=(1+a)/2, t4=(1+a)/4, t5=(3+a)/4, t6=1/2`) are
exactly the already-accepted `C-CT1-SAT-WITNESS-1` prose witness on the real
`M-CT1-SAT-5GUARDS` model (`t1=-1/2-1/2*I, ...` with `a = I`). A new claim
(`C-CT1-SAT-WITNESS-1-NATIVE-QI`) records the same point structurally via
`witness_field`/`witness_point` and was verified on the migrated copy:

- `V.point_witness` (direct call, `simple_number_field_v1`): **`VERIFIED`**
  -- all 6 saturated generators (`2*t6-1`, `2*t4-2*t5+1`, `t3-2*t5+1`,
  `t2+2*t5-2`, `t1+2*t5-1`, `8*t5^2-12*t5+5`) reduce to `0` in `Q[a]/(a^2+1)`.
- `V.verify_all` with the Singular backend **forced unavailable**
  (`binary_version="unavailable:assay"`): still `VERIFIED`. The persisted
  verdict's backend manifest is `gp-native-v1:{"contract":"grandportage-native",
  "executions":[],...}` -- zero backend executions, `verifier =
  verify.extension_point_witness`, `current: true`. Confirms exact native
  provenance without Singular.
- A second pass with an ordinary (available) backend leaves the already-`VERIFIED`
  claim untouched, as `needs_verification` promises.

## `M-CT1-CLOSED`, exercised honestly

`M-CT1-CLOSED`'s committed `generators` are authored descriptor objects
(`{expr, id, why}` per generator, for provenance/readability) and its
`open_conditions` is a prose inventory pointer (`full_inventory`,
`not_inlined_reason`, a `summary` stating "474 total" guards, pointing at
`artifacts/ct1-realization-v1/output/presentation.json`) -- neither is the
flat polynomial-string schema any verifier here substitutes into. Before this
lane, the real graph's recorded attempt (`C-CT1-QI-WITNESS`, kernel_epoch 10
and 11) shows exactly what that mismatch produces: the descriptor objects and
prose keys got `%s`-formatted straight into a Singular `subst(...)` session
(9 generator dicts + 3 bogus "guard" identifiers from the prose dict's own
keys = 12 declarations, `GP_V0..GP_V11`, matching the recorded trace exactly),
which failed with an opaque parser dump ending in `` `I` is not defined ``.

**Fix** (`grandportage/verify.py`, `_inexecutable_model_reason` +
`point_witness`): before any backend call, `point_witness` now recognizes a
model whose `generators`/`open_conditions` are not flat string lists and
returns a precise `UNVERIFIED` immediately:

> model M-CT1-CLOSED cannot be substituted: its `generators` are structured
> descriptor objects, not the flat polynomial-string list this verifier
> substitutes. `gp verify` refuses to guess a flat polynomial reading of a
> schema it was not given -- it names nothing VERIFIED or NOT_A_POINT here,
> and it checked none of whatever guard count the model's own prose claims.

No backend is touched, no authority is minted, and the message never repeats
the model's own "474 guards" claim as something that was checked.
An automated minimized `M-CT1-CLOSED` adversary now asserts that diagnostic,
zero backend executions, a persisted current-but-`UNVERIFIED` attempt,
retryability, and absence of `WITNESS_VERIFIED` authority.

## New tests

- `tests/test_format_epoch.py` (+31): historically faithful format-5 and real
  format-6 fixtures, direct reads, migrations, malformed-migration refusals,
  the real-CFG23
  regression pin, and adversaries (see above).
- `tests/test_ordered_real_semantics.py` (+7): Sturm receipt mutations
  spanning **value** (`sturm_chain`, `root_interval` endpoint), **ordering**
  (`variations`, and a dedicated `root_interval` lo/hi swap on a
  non-endpoint-root model), and **embedding** (isolating interval, variable
  name); plus an **implementation-drift** pair -- an unchanged native
  implementation survives reload, a drifted `NATIVE_IMPLEMENTATION_VERSION`
  correctly loses currency (`native_provenance` returns `None`,
  `current_verdict` reports `execution provenance is absent or invalid`, and
  the claim's `condition_verdict` is not licensed).
- `tests/test_number_field_witness.py` (+2): adversarial native-vs-Singular
  provenance -- a manifest with non-empty `executions` can never decode as
  native (dodging binary-version staleness is not available to it), and a
  fabricated Singular-contract label with a genuine zero-execution trace still
  pays the binary-version currency toll a real native manifest is exempt from.
- `tests/test_adversarial.py` (+2): the structural `M-CT1-CLOSED` refusal and
  an unavailable-then-available retry for a
  genuinely transient backend outage (not the M-CT1-CLOSED structural
  UNVERIFIED, which never recovers) -- a test-double backend's answer is
  correctly discarded to `UNVERIFIED` ("install the exact production backend
  and retry"), `needs_verification` says try again, and a
  production-identified backend on the second attempt records `VERIFIED`
  authority that survives reload.

## Validation and custody

- `python -m grandportage.cli docs`: resynced the marked check-count spans
  (1536 -> 1576) across `CURRENT.md`, `HANDOFF.md`, `README.md`, `REVIEW.md`,
  `SPEC.md`, `TESTPLAN.md`.
- DKC successor-focused lane
  (`python -m pytest -q -m "not live and not replay and not exhaustive"`):
  **1526 passed, 50 deselected** in 66.51s.
- The predecessor commit's complete collection, before the seven successor
  adversaries were added, was **1569 passed, 0 failed** (679s, Singular
  available). Collection after the successor is **1576 checks**; the
  non-live successor gate above is the retained local rerun.
- Lean: `lake build` in `lean/` -- **28/28 jobs, build completed
  successfully** (two pre-existing lint-only warnings in
  `LaurentLowering.lean`/`Exhaustive.lean`, unrelated to this lane).
- Worktree clean at completion; only the files listed in this lane's commit
  are touched.

Tool identity: Python `3.10.6`, pytest `9.0.2`, Lean toolchain
`leanprover/lean4:v4.32.1`.

Successor hashes (SHA-256):

- `grandportage/format.py`: `0299998e09600605b50901b9ff352e5f03007b5b61830bac54ddfc18f32cb763`
- `grandportage/migration.py`: `ea015e83bbd8bc0a3410c9fd3156227c0fc8ff05c17045f000127d3ad9ba75d8`
- `grandportage/verify.py`: `c2e98101a49cf60a89619c259615ce681cf9860bfbb30d0c7d591a27e7305475`
- `tests/test_format_epoch.py`: `453c20bbbf232bc07a95eda15f529ce7922bd103e5e20b821e5b4c0f95a9163e`
- `tests/test_adversarial.py`: `16ae4f0d9890ccccef270c57512714b95872a45ca1b00461a263599273f088b5`
- `tests/test_number_field_witness.py`: `effd06747f14a4ae1e2f9cd5c29bd000590fc59020ba846b074dee0c9c108bdf`
- `tests/test_ordered_real_semantics.py`: `94a74580265e851d9ced55b866eada76c427f5570dc87140664da09b1c2ac348`
