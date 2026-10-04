# Cloquet bounded Phase 0b review

Completed the five required full reads and exactly five pointer followups. This is a finite source review, not a complete mathematical audit or an executed GP replay. Only this report and its JSON companion were written. Source root: `$DEV/math-research/campaigns/match4`; source HEAD: `a343801c9af4bb06f1cb514dfecdc745a8f5ac64`. Frozen oracle remains `ac4155787207e2847d248cffed7be871d5dcd577`; all 454 cases, routes, trackers and immutable replay files are unchanged.

There are twelve proposal rows: four attributed source corrections, five deliberate mathematical misuse controls, and three GP mechanics observations. These are not twelve independent mathematical incidents. Every shipping and incident-cost value stays unknown; every `core_expressible` and `core_would_refuse` stays null. Shipping means a wrong claim published or handed off for reliance, not a commit or merge. The private-origin and “published” checkpoint wording do not establish which wrong claim, if any, was relied upon.

## Source identity and read bounds

The first five documents below were required; the remaining five consumed the entire pointer allowance. All were read fully. Raw hashes identify actual bytes; Git blob and latest path-history commit are separately retained in JSON. Primary literature PDFs, GP JSONL ledgers, artifact bodies and campaign scripts were not opened or executed. No harvest took place.

| Relative path | Full lines | Raw SHA-256 | Latest path commit |
|---|---:|---|---|
| README.md | 1–46 | `c443eb8ad50746cfc207272d7ca2d98826e8eccc96d30f0266d498ac33edc7eb` | `794587a59486dfbce2989be675c2b105086bd483` |
| CHECKPOINT.md | 1–67 | `4d95f847321459056c9930104128e4688d4e7f9681838ffe8e8eb48630266b51` | `a343801c9af4bb06f1cb514dfecdc745a8f5ac64` |
| packets/founding/CQ-PLAN.md | 1–313 | `b7bd2ef6f7f934855af47e8ccc0d37c314addc522f4003e56ad196cfb5acf080` | `794587a59486dfbce2989be675c2b105086bd483` |
| packets/founding/cq-scouting.md | 1–440 | `22ef379cb247595c62740a539b2997d7276aa0733a7b228af32b5aea7a44fcaa` | `794587a59486dfbce2989be675c2b105086bd483` |
| packets/founding/gp-cq-read.md | 1–361 | `385150a7cbb557efea315780acca1f7d5fc82ecd7fa2f35615ed7144fcd9623a` | `794587a59486dfbce2989be675c2b105086bd483` |
| literature/READS.md | 1–457 | `e8687934f4e7176d42ccdcb5feb88402b526ecdadf1f71485ba734f8a78eaec5` | `ef412026dc55e8ed61385a1b03e09a3e24d86c0c` |
| lanes/G/RESULTS.md | 1–218 | `2e0f9e5028cacf0a93150a566b6b86d85c8378e4d7cdabcafa00da5f5fd80736` | `51b6ba447089ac13e8480a9bf58f8ce727a69cac` |
| fixtures/gp-miniatures/M5.json | 1–49 | `08cc7b1b2b114f6be9557c1c2ff38e6b917f85bc7fc2bbedd1b4b30ee4ba974d` | `51b6ba447089ac13e8480a9bf58f8ce727a69cac` |
| receipts/SCHEMA.md | 1–28 | `83aeb3a99e7badfce98b950b3915b80d6c9d89589a7879955d6fa3686ad6774c` | `794587a59486dfbce2989be675c2b105086bd483` |
| verdicts/SCHEMA.md | 1–48 | `60d6ee65e0d2cde670985d2bccb8e9e430f77827801c2418febdd930ae76a8dc` | `54c67deb6ab0f191922d0013df44a1a9b9d5a93a` |

## Source corrections and controls

### CQ-C01 — Kurz angle-LP discrepancy

attributed literature discrepancy / campaign adoption near-miss; BOTH. Dedup: `kurz-angle-row`.

Claim at risk: Use the printed stronger angle row as a necessary condition, and treat reported survivor counts as a certification gate.

Source reports Lemma 6 gives adjacent-angle sum > pi/2, while LP uses x_u+x_v-y >= pi. Scouting supplies a unit pentagon with angle sum about134.76 degrees. No complete falsely rejected4-regular graph or disproof of34 is supplied.

Discovery: Scouting records exact pentagon checks; LSA reports a subsequent PDF read finding no nearby justifying hypothesis; checkpoint records correction.

Disposition: One discrepancy across scouting, LSA and checkpoint, not three incidents. Retain as attributed source statement: this worker did not open the primary PDF or execute pentagon code. No GP case asserted to certify LP-to-geometry validity.

Evidence: `$DEV/math-research/campaigns/match4/packets/founding/cq-scouting.md`, lines 259–327 (raw SHA in table); `$DEV/math-research/campaigns/match4/literature/READS.md`, lines 25–77 (raw SHA in table); `$DEV/math-research/campaigns/match4/CHECKPOINT.md`, lines 41–45 (raw SHA in table).

### CQ-C02 — General34 bound citation conflated with3-connected source

campaign source correction; SCOPE. Dedup: `general34-provenance`.

Claim at risk: Read arXiv:1401.4375 as proof of the general m(4)>=34 bound.

LSA traces the general bound citation to a2011 Geombinatorics article absent from its files; the arXiv paper is scoped to3-connected graphs. Similar titles do not establish identical sources.

Discovery: LSA citation-chain read; founding scouting had already left provenance open.

Disposition: Proposal for a source/scope correction, not evidence general34 is false. No direct primary read here; no native GP reuse for bibliography fact.

Evidence: `$DEV/math-research/campaigns/match4/literature/READS.md`, lines 81–108 (raw SHA in table); `$DEV/math-research/campaigns/match4/literature/READS.md`, lines 354–363 (raw SHA in table); `$DEV/math-research/campaigns/match4/CHECKPOINT.md`, lines 41–45 (raw SHA in table).

### CQ-C03 — Order8 uniqueness unsupported by cited source

campaign source correction; SCOPE. Dedup: `m3-uniqueness`.

Claim at risk: Attribute uniqueness of the8-vertex3-regular graph to Kurz-Pinchasi.

LSA reports that the paper states m(3)=8 as an exercise and never asserts uniqueness. Lack of that attribution does not prove nonuniqueness.

Discovery: Scouting flags unverified uniqueness; LSA recommends dropping or sourcing the clause.

Disposition: One corrected attribution episode; unknown original author/cost/reliance. No distinct GP mathematical defect.

Evidence: `$DEV/math-research/campaigns/match4/packets/founding/CQ-PLAN.md`, lines 108–112 (raw SHA in table); `$DEV/math-research/campaigns/match4/literature/READS.md`, lines 110–129 (raw SHA in table); `$DEV/math-research/campaigns/match4/literature/READS.md`, lines 364–368 (raw SHA in table); `$DEV/math-research/campaigns/match4/CHECKPOINT.md`, lines 41–45 (raw SHA in table).

### CQ-C04 — 53 target paper/calculator identity conflation

campaign source correction; BOTH. Dedup: `calculator100-versus-paper53`.

Claim at risk: Attribute the mirror-symmetric one-angle53 target to arXiv:1906.11908 rather than calculator record100.

LSA says PDF text did not establish symmetry/angle; calculator record100 supplies the explicit source. The lane could not render the figure. Its phrase 'not in this PDF' is not adopted as proof geometric objects differ.

Discovery: LSA caption-text comparison against already-replayed calculator identity; no direct raw-page read by this worker.

Disposition: Source-binding correction proposal, with paper symmetry still inconclusive. Do not infer an exact graph exclusion from separated numerical closure roots.

Evidence: `$DEV/math-research/campaigns/match4/packets/founding/cq-scouting.md`, lines 36–60 (raw SHA in table); `$DEV/math-research/campaigns/match4/literature/READS.md`, lines 279–350 (raw SHA in table); `$DEV/math-research/campaigns/match4/literature/READS.md`, lines 369–375 (raw SHA in table); `$DEV/math-research/campaigns/match4/CHECKPOINT.md`, lines 41–45 (raw SHA in table).

### CQ-P05 — Collapsed K222 witness promoted to injective realization

deliberate mathematical misuse control; no actual campaign error demonstrated; BOTH. Dedup: `M5-collapsed`.

Claim at risk: Promote the unguarded NONEMPTY point to an injective matchstick realization.

M5 records plain witness VERIFIED in Q(s)/(s^2-3), guarded identical witness NOT_A_POINT because same-class separation product is0. This is a positive-witness guard boundary. If G subset U, actual emptiness of U implies emptiness of G.

Discovery: Prewritten miniature, historical guarded replay. Parent separately checked all12 unit edges and vanishing guard with Fraction arithmetic.

Disposition: Reuse parent A24 source grounding; do not duplicate extraction or edit seed. Current A24 attempted conclusion is no-realization, and parent clarification remains pending Will. No wrong GP verdict shown.

Evidence: `$DEV/math-research/campaigns/match4/packets/founding/cq-scouting.md`, lines 221–257 (raw SHA in table); `$DEV/math-research/campaigns/match4/fixtures/gp-miniatures/M5.json`, lines 8–48 (raw SHA in table); `$DEV/math-research/campaigns/match4/lanes/G/RESULTS.md`, lines 103–110 (raw SHA in table).

### CQ-P06 — Ordered vector obstruction offered as complex emptiness

deliberate misuse control; SCOPE. Dedup: `M2-ordered-versus-complex`.

Claim at risk: Issue3u=v+w with unit vectors as SCHEME/algebraic-closure emptiness.

Real contradiction norm(v-w)^2=-5; complex point over Q(sqrt(-5)) remains. Historical GP NOT_UNIT and VERIFIED complex witness. Ordered identity is only an ungraded note in0.32.

Discovery: Prewritten M2 answer key then Lane G exercise.

Disposition: Not a newly observed wrong campaign conclusion. A10-R/C reuse the ordered-versus-complex reach decision, not M2's particular model or literal cofactor.

Evidence: `$DEV/math-research/campaigns/match4/packets/founding/gp-cq-read.md`, lines 191–219 (raw SHA in table); `$DEV/math-research/campaigns/match4/lanes/G/RESULTS.md`, lines 89–101 (raw SHA in table).

### CQ-P07 — One correct chart offered as complete coverage

deliberate misuse control; REGION. Dedup: `M6-half-angle-cover`.

Claim at risk: Treat the half-angle chart alone as covering the circle or all relevant graph branches.

Chart omits(-1,0); two opens D(1+x),D(1-x) cover via unit identity. Historical omitted-chart ideal NOT_UNIT with gap witness.

Discovery: Prewritten M6; Lane G records positive two-open cover and hostile omitted chart.

Disposition: Existing A16 covered/missing captures required exhaustion but has Boolean cover inputs. It does not encode these circle opens, graph family reconstruction or all sign/degenerate branches.

Evidence: `$DEV/math-research/campaigns/match4/packets/founding/gp-cq-read.md`, lines 235–289 (raw SHA in table); `$DEV/math-research/campaigns/match4/lanes/G/RESULTS.md`, lines 80–87 (raw SHA in table).

### CQ-P08 — Infinitesimal tangent direction offered as finite flex

deliberate misuse control; BOTH. Dedup: `M7-finite-flex`.

Claim at risk: Infer finite-flex family existence from rank deficiency at one realization.

Ideal(x,y^2) has one point and1-dimensional tangent space. Lane G's undeclared t witness is UNVERIFIED, not a native finite-flex classification.

Discovery: Prewritten M7 then deliberate free-parameter witness attempt.

Disposition: No distinct actual mathematical incident demonstrated. No exact existing case selected: affine rank/existence or Jacobian sampling examples are not the same higher-order flex assertion. Parser diagnostic is separately CQ-G03 with same dedup episode.

Evidence: `$DEV/math-research/campaigns/match4/packets/founding/cq-scouting.md`, lines 361–367 (raw SHA in table); `$DEV/math-research/campaigns/match4/packets/founding/gp-cq-read.md`, lines 306–314 (raw SHA in table); `$DEV/math-research/campaigns/match4/lanes/G/RESULTS.md`, lines 112–118 (raw SHA in table).

### CQ-P09 — Budget exhaustion offered as empty-family evidence

deliberate misuse control; BOTH. Dedup: `M8-budget`.

Claim at risk: Use a BUDGET work attempt to settle EMPTY or unbacked family count.

WORK-M8-001 recorded UNRESOLVED / graph_effect NONE,2.0 core-hours in the operational payload. Hostile EMPTY remains UNVERIFIED; unbacked family count flagged UNSOUND_PREMISE. Recorded2.0 is not measured cost of this incident.

Discovery: Prewritten M8 hostile; extra count finding arose in exercise.

Disposition: X96/X106 reuse the unfinished-search authority boundary but concern JC extraction/search, not the literal work sidecar or family-declaration path. Count refusal is a successful defense within same exercise.

Evidence: `$DEV/math-research/campaigns/match4/packets/founding/CQ-PLAN.md`, lines 229–235 (raw SHA in table); `$DEV/math-research/campaigns/match4/lanes/G/RESULTS.md`, lines 120–129 (raw SHA in table); `$DEV/math-research/campaigns/match4/lanes/G/RESULTS.md`, lines 175–179 (raw SHA in table).

### CQ-G01 — False ambient cofactor reads as VERIFIED_DERIVED at unit ideal

GP mechanics interpretation observation; REGION. Dedup: `M1-unit-quotient`.

Claim at risk: Read VERIFIED_DERIVED at M1 as independent arithmetic validation of the hostile cofactor.

Every polynomial vanishes in the zero quotient of an already-unit ideal; source says verdict correctly derived, then ambient-ring anchor REFUTED. The distinction can be misread; no false algebraic acceptance asserted.

Discovery: Deliberate mutation and anchoring comparison, source explicitly files observation without fix.

Disposition: A13 ambient/derived distinction is relevant semantic reuse but does not test zero quotient or message wording. Retain specific presentation probe only if parent needs it; do not count legitimate derived identity as mathematical incident.

Evidence: `$DEV/math-research/campaigns/match4/lanes/G/RESULTS.md`, lines 61–71 (raw SHA in table); `$DEV/math-research/campaigns/match4/lanes/G/RESULTS.md`, lines 137–150 (raw SHA in table); `$DEV/math-research/campaigns/match4/CHECKPOINT.md`, lines 49–53 (raw SHA in table).

### CQ-G02 — Live stale-model finding hidden by later unrelated supersession

GP mechanics candidate visibility defect; N/A. Dedup: `M1-stale-view`.

Claim at risk: Rely on plain gp check view to expose live stale-anchor debt after unrelated history changes.

Source records STALE-MODEL disappearing from default view after unrelated claim supersession, still visible under --history with historical label. Footer points to history: not literal silent deletion. No receipt ledger inspected or replayed here.

Discovery: Lane G staged supersession sequence then separate CLI reload, as recorded in result table.

Disposition: A18/X160 supply stale evidence/retired context decision reuse, but neither includes unrelated later supersession plus default-vs-history display. Candidate defect remains historical0.32 observation, not confirmed at frozen0.37.

Evidence: `$DEV/math-research/campaigns/match4/lanes/G/RESULTS.md`, lines 73–78 (raw SHA in table); `$DEV/math-research/campaigns/match4/lanes/G/RESULTS.md`, lines 152–165 (raw SHA in table); `$DEV/math-research/campaigns/match4/CHECKPOINT.md`, lines 49–53 (raw SHA in table).

### CQ-G03 — Free-parameter witness refusal exposes raw CAS parse error

GP mechanics diagnostic observation; N/A. Dedup: `M7-finite-flex`.

Claim at risk: Obtain a useful semantic refusal explaining undeclared t in purported flex-family witness.

UNVERIFIED with Singular parse error; no false VERIFIED. Source suggests naming undeclared variable rather than surfacing raw error.

Discovery: Same M7 attempt as CQ-P08; no second mathematical episode.

Disposition: Diagnostic-quality proposal only. No exact corpus reuse selected for wording. No backend invoked in this pass.

Evidence: `$DEV/math-research/campaigns/match4/lanes/G/RESULTS.md`, lines 112–118 (raw SHA in table); `$DEV/math-research/campaigns/match4/lanes/G/RESULTS.md`, lines 167–173 (raw SHA in table).

## Existing 0a reuse and its limits

Read the parent resumption Markdown/JSON and eleven existing case payloads fully; their exact raw hashes and paths are in the companion JSON. No case was extracted twice or changed.

- **A24:** M5 supplies concrete witness/guard evidence. Parent independently checked all twelve cross-class lengths and the zero separation guard. The current A24 seed attempts “no realization exists”; the parent’s proposed witness-promotion clarification still awaits Will. If the guarded set is contained in the unguarded set, true unguarded emptiness implies guarded emptiness. This report does not approve changing A24.
- **A10-R/C:** precise ordered-versus-complex reach contrast for M2. Their model is `x²+1`, not the three-vector model; they do not replay M2’s particular identity.
- **A16-covered/missing:** the exhaustive-cover decision for M6; Boolean cover inputs do not encode the circle chart, all assembly branches, or graph-level reconstruction.
- **A13-ambient/derived:** the identity-origin distinction for M1. These do not exercise the zero quotient or the wording of `VERIFIED_DERIVED`.
- **A18/X160:** stale-input and superseded-context refusal. They lack the unrelated later supersession and default-versus-history display sequence; the observed visibility issue is therefore not already reproduced by those payloads.
- **X96/X106:** unfinished extraction/search cannot acquire mathematical authority; different JC data and operations, not M8’s literal work-sidecar or family-count declaration.
- **M7:** no exact case selected. Rank-based affine existence or Jacobian-sampling cases do not establish the higher-order finite-flex boundary. Its free-parameter parser observation is the same episode as CQ-P08.

## No-distinct-incident dispositions

- **Lane D signatures and53 angle scan:** Recorded reconnaissance/calibration and seed-branch numerical roots, no newly proved family/graph/order exclusion. No solver run in this pass. Evidence: `$DEV/math-research/campaigns/match4/CHECKPOINT.md`, lines 8–20.
- **Gerbracht polynomial and Winkler4x4 checks:** Recorded transcription/compatibility controls. One coordinate polynomial is not full Harborth reconstruction; rank checks are not nonlinear closure. No error episode identified. Evidence: `$DEV/math-research/campaigns/match4/literature/READS.md`, lines 187–246.
- **M3 selected root; M4 nonedge; degeneration controls:** Prewritten proposed positive/negative contract controls; Tier(c) deposit, not implemented by Lane G. No adverse actual verdict demonstrated. Evidence: `$DEV/math-research/campaigns/match4/packets/founding/CQ-PLAN.md`, lines 142–160.
- **Laman/degree/rational-coordinate/uniqueness advice:** Conceptual corrections with no traced run or published wrong conclusion in this bounded record. Retain risk guidance; no fabricated independent incidents. Evidence: `$DEV/math-research/campaigns/match4/packets/founding/cq-scouting.md`, lines 361–367.
- **Custody and intake fixes:** Mailbox dirt, parser bullet-list requirements, stale blocked tempo and CRLF handling are process fixes. No mathematical contamination or wrong shipping established. Evidence: `$DEV/math-research/campaigns/match4/CHECKPOINT.md`, lines 44–54.
- **verdict schema promotion clauses:** Scope policy read and recorded, including a stated Whitney promotion with3-connectivity premise. This worker did not audit its sufficiency for geometric realizations; no blanket theorem endorsement or new incident finding. Evidence: `$DEV/math-research/campaigns/match4/verdicts/SCHEMA.md`, lines 17–23.

The literature allegations remain attributed to scouting/LSA. This worker read their reports, not the original PDFs. In particular, unsupported uniqueness attribution is not proof of nonuniqueness; the LP discrepancy is not proof the 34 bound is false; missing caption text is not proof two geometric graphs differ. Broad source warnings are not converted into invented runs or wrong published claims.

## Cost, custody and parent harvest pointers

Three Sonnet lanes approximately120k,120k,240k tokens; two intake stewards approximately100k,130k; Fable a few short turns. Approximately710k tokens across the wave, as a source-reported aggregate. Not attributable per proposal; actual wall-clock, incident cost and recovery cost unknown. CQ-PLAN8 core-hours per witness/candidate proposed, not runtime. M8's2.0 payload is a fixture work record.

Markdown scoped reports and schemas; JSON miniatures and construction records; hash-pinned immutable raw HTML/PDF fetch manifests; JSONL GP graph/work ledgers and verdict index; SHA256-addressed JSON artifacts. The receipt contract binds adjacency and rotation-system hashes, raw source/version/record/branch, equations and guards, selected-root selector, quantifiers, evidence kind and verifier version. Arithmetic correctness and the bridge to the CQ object stay separate. Positive witnesses require distinct vertices, exact edges, legal intersections including zero determinants, and the declared rotation system; unit-length nonedges remain allowed.

The six negative scope labels are parameter box, assembly branch, construction family, plane embedding, abstract graph and complete vertex order. A numerical failure has none. Scopes are not a linear strength ladder. The schema’s Whitney-based promotion statement is recorded as source policy, not independently audited here.

Historical Lane G identity: GP 0.32.0, source `cca5b05d1d74df68d2fb8eb0e13429d3d6fe85ee`, format 7, epoch 11; SingularBackend implementation 4/protocol 2 with Singular 4.2.1 under WSL. RESULTS lines 31–34 report 43 events and prefix digest `ed83e8f4164492f77ac0b87c93d5c0630f5caea25b7fe6b5704541b136db2927`. This was not independently folded; prefix digest is not a raw-file SHA. Lane G separate graph; root empty by design per checkpoint. New campaign receipts effect NONE until binding/reach review. No campaign root proof inferred from miniatures.

Selected existing paths below were located by filename inventory. Except M5, their bodies were not read. They are pointers for parent private harvest only:

- `$DEV/math-research/campaigns/match4/lanes/G/.portage/graph.jsonl`
- `$DEV/math-research/campaigns/match4/lanes/G/.portage/work.jsonl`
- `$DEV/math-research/campaigns/match4/lanes/G/.portage/artifacts/sha256/`
- `$DEV/math-research/campaigns/match4/fixtures/gp-miniatures/M1.json`
- `$DEV/math-research/campaigns/match4/fixtures/gp-miniatures/M2.json`
- `$DEV/math-research/campaigns/match4/fixtures/gp-miniatures/M5.json`
- `$DEV/math-research/campaigns/match4/fixtures/gp-miniatures/M6.json`
- `$DEV/math-research/campaigns/match4/fixtures/gp-miniatures/M7.json`
- `$DEV/math-research/campaigns/match4/fixtures/gp-miniatures/M8.json`
- `$DEV/math-research/campaigns/match4/data/raw/MANIFEST.json`
- `$DEV/math-research/campaigns/match4/data/raw/mikematics_matchstick-graphs-calculator_2019-06-25.htm`
- `$DEV/math-research/campaigns/match4/data/graphs/calculator_records_2019-06-25.json`
- `$DEV/math-research/campaigns/match4/verdicts/INDEX.jsonl`
- `$DEV/math-research/campaigns/match4/results/inbox/p05-source-reads-v1.md`
- `$DEV/math-research/campaigns/match4/results/inbox/lane-g-tier-ab-v1.md`
- `$DEV/math-research/campaigns/match4/results/intake/2026-09-11-wave1-intake.md`
- `$DEV/math-research/campaigns/match4/results/intake/2026-09-11-wave1-intake-laneG.md`

receipts inventory showed only SCHEMA.md. Verdict INDEX path exists; no claim about its entries. rg inventory does not list ignored PDFs; this pass does not assert current PDF presence/absence. Historical LSA PDF hashes in READS are not newly verified PDF bytes. Literature/scouting bundle sandbox links not fetched.

## Finite stop boundary

- Parent decides A24 semantic clarification with Will; source guard control does not settle the current no-realization seed direction.
- Parent integration determines which attributed corrections/probes merit admission. No new cases or routes were produced.
- If parent needs current GP defect confirmation, inspect/fold exact Lane G custody and test the unrelated-supersession view under separately authorized frozen replay; this pass alone cannot establish it.
- Primary evidence is required before turning Kurz/bibliography allegations into verified literature conclusions;2011 general-bound source and PDF figure symmetry remain source-recorded gaps. No automatic further audit.

No additional general audit, source search, execution, communication, install, kernel/Lean change, commit or publication is implied by this remaining list. The JSON companion carries full source history/blob identities, proposal nulls and case hashes.
