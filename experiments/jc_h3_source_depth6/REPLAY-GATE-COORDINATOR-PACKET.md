# JC H3 depth-6 GP replay gate — coordinator packet

**Date:** 2026-08-01
**Audience:** lead Sol coordinator for the Jacobian program
**GP release line:** v0.22.0, graph format 4, kernel epoch 10

## Executive use

Grand Portage now has one bounded command for the landed H3 depth-6 receipt
chain:

```powershell
cd C:\Users\wstri\dev\grand-portage
py experiments\jc_h3_source_depth6\replay_all.py `
  --seam `
  --check-native-bindings `
  --journal review\jc-h3-depth6-stage-journal.jsonl `
  --output review\jc-h3-depth6-fast-replay.json `
  --force
```

Use it after a relevant JC receipt lands and before promoting or summarizing
the depth-6 result. It is a post-receipt semantic integration gate. It must not
be put on the critical path of native discovery, and JC agents do not need to
emit GP-native schemas.

A healthy run ends with:

```text
overall_verdict: VERIFIED_TO_EXPLICIT_OPEN_OBLIGATION
first_missing_authority.id: target_pair_to_normalized_laurent_root
first_missing_authority.status: UNMATERIALIZED_OPEN
authority_ceiling: CONDITIONAL_NORMALIZED_ROOT_TO_DEPTH6_BOUNDARY_ONLY
open_frontier: R5, R6, R7, R6.Q_side_relocation,
               target_pair_to_normalized_laurent_root
```

That is a success, not a partial failure. It means the checked chain reaches
the exact depth-6 boundary under the conditional normalized-root premise and
refuses to pretend that premise came from an original source pair.

## What the command checks

The ledger is ordered by mathematical dependency:

1. **Conditional source seam** — normalized Laurent-root data replay to five
   exact reduced polynomiality rows; strict original-source promotion refused.
2. **Corrected R1--R7 frontier** — R1--R4 close only inside the conditional
   seam; R5 stays premise-bound, R6 lacks the exact non-monomial frame
   conversion, R7 stays inferred, and Q-side relocation remains open.
3. **Graded face extraction** — those five rows yield the exact 25 selected
   depth-2..6 faces under the declared finite supports.
4. **Complete finite template** — in full mode, the 25 faces are checked as an
   exact generator subset of all 147 nonzero finite-template rows in 78
   coordinates.
5. **Ordered depth-6 chain** — 23 state-bound solve steps carry the ten landed
   ladder values to the two exact boundary residuals.
6. **Boundary projection and strata** — the 3,262-term `R2B` and 6,124-term
   `beta` maps decode exactly; full mode also recomputes the generic affine
   solve and discriminant-collapse equivalences.
7. **Optional native seam replay** — the sibling JC verifier runs five upstream
   checkers and refuses all nine source-seam mutations.

The aggregate report itself has graph effect `NONE`. Full mode reports two
authorities that their underlying checked graph edges already possess:

- `POINT_INCLUSION` for the complete-template to selected-face relation;
- `IDENTITY_TRANSPORT` for the two exact boundary rewrites.

The gate does not mint a new source edge or a new H3 conclusion.

## Operating grades

### Tier 0: preflight — identity and drift check only

```powershell
py experiments\jc_h3_source_depth6\replay_all.py `
  --preflight `
  --journal PATH
```

Measured runtime on the Windows development machine: **1.23 seconds**. It
gunzips the frozen chain, checks canonical and per-record digests, ordering
fingerprints, fixture bindings, and rung welds. It performs no sparse decoding
or polynomial arithmetic. Its only license is that the inputs are the named
inputs; it emits `PREFLIGHT_BINDINGS_ONLY`, never a chain verdict.

### Tier 1: seam receipt gate — routine use

```powershell
py experiments\jc_h3_source_depth6\replay_all.py `
  --seam `
  --check-native-bindings `
  --journal PATH.jsonl `
  --output PATH `
  --force
```

Measured runtime on the Windows development machine: **3.9 seconds** without
live sibling checks and **4.8 seconds** with `--check-native-bindings` in the
bounded 2026-08-01 passes (historically about 4–6 seconds). `--seam` is the
default when no tier flag is supplied and is verdict- and license-identical to
the former fast mode.

Use after:

- a depth-6 chain, face, boundary, or source-seam receipt changes;
- rebasing the JC checkout;
- preparing a status update that cites this lane;
- handing the lane between agents.

Seam mode checks every frozen weld and the boundary polynomial projection. It
deliberately marks the 147-row graph inclusion and the two boundary graph
equivalences as deferred optional work. Do not describe seam mode as having
recomputed those graph authorities.

### Tier 2: full GP milestone gate — synchronization points

```powershell
py experiments\jc_h3_source_depth6\replay_all.py `
  --full `
  --check-native-bindings `
  --output PATH `
  --force
```

Latest measured runtime on the same machine: **310.6 seconds**. Stage split:

- defining-row rederivation and selected faces: 17.7s;
- complete 147-row graph inclusion: 37.5s;
- all 25 ambient chain substitutions: 242.7s;
- boundary projection and two graph equivalences: 12.7s.

The older checked-in v1 full ledger measured about 160 seconds, including 104
seconds in the chain. Full-mode wall time is therefore sensitive to machine
load; use its ledger and journal rather than a fixed timeout as the diagnostic.

Use at named milestones, before release/review, or after changes to the
mathematics or verifier logic. Full mode needs SymPy. On this machine, `py`
selects the established runtime with that dependency; the minimal GP `.venv`
correctly refuses full source replay because SymPy is absent.

### Native cross-check — source-seam changes only

```powershell
py experiments\jc_h3_source_depth6\replay_all.py `
  --check-native-bindings `
  --native-replay `
  --output PATH `
  --force
```

Measured runtime: 59 seconds total, 55 seconds in the native verifier. Run this
when the native manifest, native verifier, or any of its five bound upstream
checkers changes. It is usually redundant for unrelated GP edits.

`--native-replay` is independent of `--full`; combine them only when both the
native source seam and the downstream GP mathematics changed.

### Interrupted-run diagnostics

`--journal PATH` appends and fsyncs one JSON record after each completed stage:
`id`, `status`, `verdict`, `seconds`, `graph_effect`, and `rss_mb`. The journal
is diagnostic-only and grants no authority; the single atomic `--output`
ledger remains authoritative. A killed run therefore names its last completed
stage even when no final ledger exists.

The reported 255-second chain-stage signature did reproduce in the real tier-2
run: full mode spent 242.7 seconds in `ordered_depth6_chain`, while tier 1 spent
2.7 seconds there. That strongly identifies full replay (or an equivalent
full-replay invocation), compounded by machine load, rather than a current
fast-tier regression. The exact argv of the earlier run was not preserved.
Separately, seam mode decoded all 25 face bodies even though only full mode
consumes them; those decodes now occur only in tier 2. This small cleanup is not
presented as the cause of the 255-second observation.

## What a coordinator should do with the result

Treat the JSON ledger as a review and synchronization artifact, not as the JC
truth ledger itself.

When it passes:

- cite the exact fixture/certificate digests from `bindings`;
- report which authority tier ran and which stages were deferred;
- preserve the named first missing authority in status prose;
- continue native JC discovery normally;
- ask the GP lane to adapt only newly landed, load-bearing receipts.

When it refuses:

- stop promotion of this composition seam;
- inspect the first error and the last progress label on stderr;
- distinguish environment refusal (for example missing SymPy) from evidence
  drift or mathematical mutation;
- do not repair a digest by weakening or deleting a refusal;
- send the changed native receipt plus its independent verifier to the isolated
  GP adapter lane.

Do not infer from any passing mode:

- actual original-pair membership;
- a reverse lift or source-image sufficiency;
- chart, branch, generic/discriminant, or global coverage;
- survival/nonemptiness in the reverse direction of the 147-to-25 row
  relaxation;
- H3 or a `(75,125)` verdict change.

## Recommended coordination pattern

```text
native JC discovery
  -> native receipt + independent native replay
  -> GP seam gate
  -> continue discovery / agent handoff

named synchronization point or semantic change
  -> GP full gate
  -> review JSON ledger and explicit first missing authority
  -> optional canonical campaign promotion by the lead coordinator
```

Keep GP isolated from the discovery loop unless a transition has become
load-bearing. The useful trigger for more GP work is not “new math exists”; it
is “a conclusion now depends on moving a claim across this precise context
change.” Build the narrowest contract or adapter needed for that seam.

## Checked-in review artifacts

- `review/jc-h3-depth6-full-replay-v1.json` — real full gate, all GP stages.
- `review/jc-h3-depth6-native-replay-v1.json` — real fast gate plus all nine
  native mutation refusals.
- `fixtures/jc_source_depth6/r1_r7_seam_v1.json` — corrected, LF-normalized
  R1--R7 source-frontier binding.
- `review/jc-h3-depth6-seam-replay-v2.json` — schema-v2 seam ledger with the
  typed open frontier.
- `review/jc-h3-depth6-full-replay-v2.json` — real schema-v2 tier-2 replay with
  complete template, all substitutions, and both boundary equivalences.
- `review/jc-h3-depth6-status-block-v1.md` — generated, machine-owned status
  projection suitable for coordinator review (not installed in JC files).
- `tests/test_jc_h3_depth6_replay_all.py` — real fast-path integration plus
  mutation, stage-order, graph-authority, native-boundary, and atomic-output
  tests.

The current full and native ledgers both stop at the same
`target_pair_to_normalized_laurent_root` obligation. That agreement is the
present handoff invariant.
