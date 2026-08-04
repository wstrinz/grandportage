# JC actual-source depth-6 boundary assay

This isolated adapter consumes the frozen JC receipt
`f2_h3_source_depth6_receipt.json` at SHA-256
`3c9954943d94faf8122ef556aa7248454d3d3d03e460747c6d55c0d3bc4a1464`.
It does not modify the sibling `math-stuff` checkout.

The native receipt contains two different grades of evidence:

- full sparse maps for the 3,262-term `R2B` residual and the 6,124-term
  `beta` residual;
- term counts and SHA-256 commitments, but not polynomial bodies, for the 33
  preceding top/depth-1--6 solve values.

`adapter.py` preserves that distinction. It independently decodes both sparse
maps, recomputes their native canonical digests, checks the exact
`-5*c2_3*c8_7*t` witness, checks that `beta` remains nonzero after
`c4_5 = c2_3^2/4`, and freezes a portable GP projection under
`fixtures/jc_source_depth6/boundary_v1.json`.

It then constructs two exact graph components using the existing
`mapped_ring_iso_v1` proof format:

1. On `alpha != 0`, adjoining `alpha*GP_INV_alpha-1` makes
   `alpha*c7_5+beta=0` equivalent to the translated coordinate
   `c7_5+GP_INV_alpha*beta=0`.
2. On `c2_3^2-4*c4_5=0`, the same equation is exactly `beta=0`, and `c7_5`
   remains free.

Both equivalences verify by direct cofactor expansion without Singular. The
large `beta` polynomial is represented through a fresh `GP_BETA` alias plus
one exact sparse alias equation; this keeps the coordinate maps small while
binding them to the complete polynomial.

## Landed chain replay

JC commit `cb3136c` supplies the missing bodies and ordered transitions in
`f2_h3_source_depth6_chain_certificate.json.gz`. GP retains a byte-identical
copy as `fixtures/jc_source_depth6/chain_v1.json.gz`; its canonical
uncompressed SHA-256 is
`d5ed44977e1f39312fbd2d30a286f686a0cd26d55dba237420a7a3d2bf513f15`.

`chain_adapter.py` is an independent consumer rather than an import of the JC
verifier. Its routine gate checks all 25 face/value digests, 23 ordered state
transitions, unit witnesses and solve identities. It additionally proves that
the ten starting bodies are exactly the solutions in GP's verified top- and
second-face fixtures and that the two outputs are exactly the existing `R2B`
and `alpha*c7_5+beta` boundary projection. `--full-replay` recomputes every
ambient face substitution and explicit `15*t^3+1` cofactor; it currently takes
about 80 seconds on the development machine.

The chain certificate alone retains graph effect NONE: it authenticates and
replays the landed face tables, but it does not derive them from the E-system.

face_extraction_adapter.py closes that translation-validation seam in two
layers. Its roughly one-second routine gate independently expands the five
frozen reduced E-system rows through the declared finite root supports and
matches all 25 landed depth-2..6 face digests and term counts. The stronger
--full-source-replay audit reconstructs those five rows from

- Zu = 1 + sum(z_e u^e);
- the fourteen unit-triangular P-side eliminations; and
- the defining Zu^5 + a4 Zu^4 + a2 Zu^2 + a1 Zu + am1 Zu^-1 + lam Zu^-2
  formula with the declared invariant substitution.

That audit takes about 15 seconds and agrees exactly. The checker remains
bounded to 50 million sparse term products and 20,000 terms per intermediate;
the selected live fixture uses 67,868 products.

## Complete finite-template graph assay

The graph itself has no 64-variable model limit. Sixty-four is a shared
resource bound on several specialized certificate checkers and producers.
Raising it globally would relax unrelated trust boundaries and is unnecessary
for this seam.

full_template_campaign.py instead expands the complete declared finite root
supports while leaving every global bound unchanged. The resulting exact model
has:

- 78 active variables;
- 147 nonzero coefficient equations through complete row depths
  25, 27, 28, 30, and 32;
- 424,934 sparse terms and 914,741 checked sparse products;
- the 25 landed depth-2..6 equations as literal members of that generator set.

The generic containment verifier now recognizes exact generator inclusion as a
unit-cofactor proof before spawning a backend. It reparses every included
target generator, so identical malformed payloads are refused. Containment
verifier version 3 makes the backend-free result replayable as a current
verifier-native structural decision.

A disposable persisted campaign earns VERIFIED containment on a
NECESSARY_CONDITION edge from the complete reduced E-system template to the
25-face selection, produces zero findings, and spawns no CAS process. Its JSONL
is about 39.5 MB, making generator interning or content-addressed model payloads
the next review-tooling issue rather than a reason to weaken semantic scope.

## Deliberate refusals

The graph-bound edge establishes exactly:

- a reduced-E-system witness gives a selected-face witness;
- emptiness of the selected face system refutes the complete reduced E-system
  template.

It does not establish the reverse witness direction. More importantly, its
source endpoint is the reduced E-system presentation, not an original
polynomial pair. Therefore the assay still grants no:

- selected-face survival -> reduced-E-system survival;
- original polynomial-pair membership;
- checked cover joining the generic and discriminant components;
- q- or p-chart membership;
- depth-7, H3, or (75,125) conclusion.

The next upstream seam is the mathematical/presentation bridge from an
original polynomial pair to this reduced E-system. No graph field, edge type,
claim kind, transport cell, or kernel-epoch change was needed.

## Review-surface measurement

The complete two-model/one-edge campaign is about 39.5 MB as JSONL because
its 25 target generators repeat values already carried by the 147-generator
source model. It folds cleanly. gp show now collapses large structured ideals
to generator count, total term count, and the per-generator range instead of
printing 147 individual summaries.

An earlier five-model/two-edge boundary projection measured about 56 MB and
its static explorer about 9 MB because the derived read model also repeats
large generator payloads. Those temporary artifacts were not checked in.
Content-addressed generator bundles or projection interning are now supported
by two live measurements; they should precede publishing a full-template
visualization packet.

## General proof-frontier projection

`frontier_adapter.py` compiles the checked seam ledger into the shared
`frontier/v1` read model. It is independent of the H8/c7_9 consumer and keeps
all five depth-six statuses in their native vocabulary by marking their
`frontier_state` explicitly `OPEN`. Stable semantic IDs replace local R5/R6/R7
labels, the three R6 premises become stable source IDs, and the parent target-
pair seam receives a scope distinct from the conditional depth-six argument.

The older generated status block remains available for compatibility. The new
projection is the current machine-facing research boundary; it changes no
status, infers no discharge, and retains graph effect `NONE`.

## Run

The aggregate post-receipt gate is the normal entry point. Its default seam
tier checks the conditional source seam, corrected R1--R7 frontier, exact
selected-face extraction,
ordered chain envelope, and frozen boundary projection. It deliberately
defers the two expensive graph-authority recomputations and still ends at the
explicit open `target_pair_to_normalized_laurent_root` obligation:

```powershell
python experiments/jc_h3_source_depth6/replay_all.py `
  --seam --check-native-bindings --journal JOURNAL --output PATH
```

Use `--preflight` for a roughly 1.2-second binding/digest-only check that grants
no mathematical verdict. Use `--full` at milestone synchronization points. It
additionally rederives
the five rows, materializes and checks the complete 147-row/78-variable graph
inclusion, replays all 25 ambient substitutions, and recomputes both boundary
equivalences. It measured 310.6 seconds in the latest load-sensitive run
(historically 160 seconds) and requires the optional SymPy dependency. Use
`--native-replay` separately when a landed JC source-seam manifest/verifier
changes; it runs the five native upstream
checkers and all nine mutation refusals, taking about 55 seconds here.

The mathematical tiers emit machine-readable aggregate schema
`gp-jc-h3-depth6-milestone-replay/v2`; old v1 ledgers migrate explicitly and
lossily. Passing means `VERIFIED_TO_EXPLICIT_OPEN_OBLIGATION`, not
original-source membership or H3.
The aggregate itself has graph effect `NONE`; its full-mode stage records make
the already-existing point-inclusion and identity-transport authority visible
without minting any new campaign conclusion.

```powershell
python experiments/jc_h3_source_depth6/frontier_adapter.py
python experiments/jc_h3_source_depth6/adapter.py
python experiments/jc_h3_source_depth6/chain_adapter.py
python experiments/jc_h3_source_depth6/chain_adapter.py --full-replay
python experiments/jc_h3_source_depth6/face_extraction_adapter.py --check-native-bindings
python experiments/jc_h3_source_depth6/face_extraction_adapter.py --full-source-replay --check-native-bindings
python experiments/jc_h3_source_depth6/full_template_campaign.py
python experiments/jc_h3_source_depth6/full_template_campaign.py --campaign-root PATH --record
python -m pytest -q tests/test_jc_source_depth6_authority.py
python -m pytest -q tests/test_jc_source_depth6_chain.py
python -m pytest -q tests/test_jc_source_depth6_face_extraction.py
python -m pytest -q tests/test_jc_source_depth6_full_template.py
```

To build a disposable persisted campaign and record both equivalence verdicts:

```powershell
python experiments/jc_h3_source_depth6/adapter.py `
  --campaign-root PATH --record
python -m grandportage.cli --root PATH check
python -m grandportage.cli --root PATH show
```
