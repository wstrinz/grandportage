# v0.32 / epoch 12 preflight — 2026-09-09

Recommendation: keep the two-release structure, revise the packet before implementation, and ship a narrowly bounded guard release first. Phase B is not implementation-ready as written. Its motivating failure is real, but its proposed single ordering conflates field extension with universal quantification, and its migration can preserve the timeout loophole it is supposed to close.

This review changes no product code, release version, kernel epoch, or campaign input. It is a planning record, not a release sign-off or a complete formal soundness audit.

## Evidence and reproduction

- GP baseline: `fa5644dd6f50cf904ad2c1be5f37e7371fe9bf0d`, v0.31.2, graph format 7, kernel epoch 11; initially clean checkout.
- DK source: separate repository `math-research/campaigns/dk-retrodiction`, commit `b876fe4ed5c8963a0e8c19e18c829821c0686654`, matching the packet.
- Read the packet rev 2, project architecture/current/review/spec surfaces, T1 follow-up and verbatim transports, frozen fixture instructions, adjacency note, misuse report, and custody measurement. Inspected the store, kernel, checker, CAS boundary, provenance, format, CLI/history, migration/release boundaries, and relevant regression tests.
- [observations.json](observations.json) records fresh in-memory folds of D1/D3, all five field probes, every transport JSON, and misuse inputs. Source JSON hashes cover LF-normalized bytes; [source-manifest.json](source-manifest.json) binds the principal source documents. The observations also contain explicitly labeled local mutations; these are not replacements for T1 fixtures.
- [observations-live.json](observations-live.json) additionally records six direct `cas.check_witness` runs using the frozen D2 inputs. On Singular 4.2.1 (4212; installed Debian package reports 4.2.1-p3+ds-1), 96 variables succeeds three times; 97 fails three times with the same nested-`subst` memory/parser error. This directly reproduces the underlying boundary; it is not a verbatim replay of the `gp verify` shell fixture.
- Ledger replay: 57 claim records, 52 live; `DOUBT:D-E5-GAP` first, then the two incomplete-family findings. `F-TRADE` remains unflagged. LF SHA-256 is `647006161a9af5b6ac2fd6d1e9938c1e5519e6b576359bfa9d6735b88a6a0fd8`, matching T1.
- [history-baseline.txt](history-baseline.txt) reproduces five displayed claim chains; the model chain is omitted.
- Deterministic baseline: **1,593 passed, 50 deselected**, 111.04 seconds. Remaining release lanes, with `GP_REQUIRE_LIVE=1`: **50 passed, 1,593 deselected**, 554.53 seconds. Together these account for **all 1,643 existing Python tests, with no skips**. The Lean build was not rerun in this preflight.

Reproduce the read-only observation harness from the GP root:

```powershell
python review/v0.32-preflight/probe.py C:/Users/wstri/dev/math-research/campaigns/dk-retrodiction
python review/v0.32-preflight/probe.py C:/Users/wstri/dev/math-research/campaigns/dk-retrodiction --live
```

The original shell runner was not run in the sibling campaign: it creates/deletes `.scratch` there. No `--record`, fixture regeneration, cfg23 edit, or configuration-23-4 edit was performed. The 189 custody-derivable commits are a pinned path-based proxy from T1, not a newly measured time saving.

## Packet amendments required before implementation

| Item | Finding | Required amendment |
|---|---|---|
| A1/D1 | The minimal frozen premise is family **PREDICATE**, not COUNT. `store.py:2967` assumes every cited claim has `model`. | Guard every family-claim kind. Distinguish crash containment from adding family-to-model inference semantics. |
| A1/D1 | Current inferences co-locate premises at a model, have no materialized derived claim, and do not implement the proposed family authority inheritance. | For Phase A, choose REFUSED plus discharge, as the frozen fixture README recommends. Move successful mixed family/model composition and authority propagation to B. Do not substitute `.get('model')` and call this fixed. |
| A2 | A structured UNRESOLVED record is new operational vocabulary; the format has closed event keys and no task/locus disposition schema. | Replace “no vocabulary change” with “no mathematical vocabulary or transport change.” Specify format compatibility, operational storage, and lifecycle before adding fields. A new graph format need not imply a kernel epoch. |
| A4 | T1 `followup/04-adjacency.md` explicitly says both counts can be true: actions excluded versus portable certificates missing for quotient templates. | Defer this DK `STALE_OVERLAP` finding. Different counting units and evidence obligations are not contradictory verdicts. Family count/description alone proves no containment. |
| A6 | `ledger-history` cannot remain byte-identical while A4 adds the sixth chain and repairs its tally. | Preserve the historical golden, but explicitly expect the reviewed history delta. |
| A6 | T1 REPORT section 4 says misuse (i) is accepted; (ii) is caught only for honest partial counts; (iii) is refused. Fresh folds confirm the distinction. | Replace “(i)–(iii) still refused” with per-input expectations. Any new prevention of dishonest totals is additional evidence binding, not an existing regression control. |
| B1/X3 | Frozen X3 refuses structurally because RESTRICTION is declared POLYNOMIAL; X3b is the meaningful boundary refusal. Neither is a positive covered-real-chart test. | Keep both originals; add distinct covered-chart positive and uncovered-boundary negative controls. |
| B1/P-A2, X4 | An omitted point universe still does not say R. | Distinguish the immutable legacy observation from a new explicitly typed `about: R` positive case. Define any normalization explicitly; never infer R from prose. |
| B2/B3 | `exact_coefficient_domain(0)` returns Q only. Number-field witness support does not make general number-field coefficient computation available. | Keep `compute_in` tied to supported exact representations. Reuse `coefficient_domain` where possible; define aliases and refuse contradictory duplicate declarations. Do not promise a general K-arithmetic backend. |
| B3 | `base_changes: false` includes `NO_RATIONAL_POINT_SEARCH`, and `true` is also used in positive characteristic. | Replace blanket boolean migration with a certificate-specific, model-bound conversion. See below. |

The DK overlap deferral is stronger than “containment is not implemented”: even an action-to-template map would not make lack of a portable template certificate contradict per-action exclusions. A future rule needs the same population, proposition, and evidence obligation. Keep the adjacency visible to readers without labelling either current claim false or stale.

## Phase B mathematical design gate

### Field inclusion and instantiation are different judgments

For concrete fields, an extension requires an embedding compatible with the coefficient data, not merely labels in a hierarchy. The standard definition makes the field map explicit; see [Stacks, field extensions](https://stacks.math.columbia.edu/tag/09FT).

The packet puts instances below `ANY_ORDERED` and also says a NONEMPTY witness travels to everything above its field. Counterexample: `x^2-2=0` has a real point but no rational point. R is an instance of ANY_ORDERED, but this does not prove nonemptiness over every ordered field. Similarly, a C-point of `x^2+1=0` cannot become a claim about every characteristic-zero field.

Recommended design: one field vocabulary with separate pure judgments for (1) concrete compatible extension, (2) quantified certificate instantiation, and (3) witness transport. Universal EMPTY can instantiate down to an instance; an instance-level proof cannot generalize upward just because its field belongs to the class. A rational witness can have uniform characteristic-zero reach, but that must follow from its rational coordinates.

This is a stop against the literal B2 rule under B5, not evidence that a new model axis is necessary. Resolve it on paper using existing point-universe and witness-field data before changing the kernel.

### The existing point universe and witness field remain load-bearing

`about: Q`, `compute_in: Q`, `point_universe: ALGEBRAIC_CLOSURE` may carry the point i of `x^2+1=0`. Comparing only model.about values Q <= R would license a false real existence conclusion if the existing point-universe guard were relaxed indiscriminately. Conversely, Q(i) as a field of definition does not mean every individual point requires i: the point x=0 may descend, but doing so requires an actual witness/compatibility check.

Define precisely whether BASE/closure is relative to `about` or the exact presentation domain, and how the allowed combinations are interpreted. Missing is not implicitly BASE. Use the existing `witness_field`, exact coordinate evidence, selected embedding, and target point scope for X11. A real label or an unverified isolating interval cannot certify realness.

X5 also needs compatible coefficient maps. The two selected images of a in `a^2=17` define the same abstract field, but `y^2=a` has real solutions at the positive image and none at the negative image. Abstract field inclusion cannot copy an embedding-sensitive statement. Retain the independent selected-root receipt and map checks. Treat “both embeddings” as two checked instantiations or an explicitly verified invariant certificate, not a new field name.

### Reach must be earned and bound

- `ORDERED` is appropriate for an actual uniform ordered-field contradiction, such as the appropriate rational SOS/Positivstellensatz identity. A sign calculation at one selected root is not automatically such a result.
- `CHAR_0` must retain coefficient interpretation and chart/guard assumptions. Non-rational coefficients require compatible embeddings; localization never removes the chart-cover obligation.
- `FIELD_SPECIFIC(F)` is a bound statement, not the fallback for evidence that proves nothing.
- `NONE` must explicitly include failed/capped search and the inappropriate use of `NO_RATIONAL_POINT_SEARCH`. Otherwise B3 maps its current false boolean to FIELD_SPECIFIC and **X6 remains licensed**.
- Separate mathematical scope from evidence authority. A custom author-declared reach must not impersonate verifier-issued reach or turn a timeout into a certificate. Declared/cited theorems need visible provenance, while VERIFIED authority requires current exact replay.

Positive characteristic is already supported and cannot disappear in epoch 12. For example, the equation `2*x-1=0` has unit ideal after reduction modulo 2, but has the rational solution 1/2. Migrating a modular base-changing certificate to unrestricted CHAR_0 would invent a false theorem. Preserve the existing finite-field/reduction semantics and add explicit migration controls; do not use a field extension rule for reduction modulo p.

Migration also needs to preserve historical readability without conferring current authority, name ambiguous number-field spellings that lack embedding information, reject contradictory old/new fields, stale relevant receipts, and list every inferred reach. Syntactic recognition of `Q(sqrt 17)` does not choose an embedding.

## Additional findings from the broader review

### P1: a BASE_EXTENSION-only fix leaves alternate type paths

Fresh in-memory mutations of the frozen B2 graph to NECESSARY_CONDITION and RESTRICTION also fold and report `INF` clean, with witness/containment debt only. These are not independently checked counterexamples with verified witnesses; they demonstrate that the structural field boundary is absent across those edge types too.

Phase B must define endpoint-scope preconditions for every point-carrying edge and check CLI, MCP, probe, verifier/reload, and inference paths against them. A polynomial identity over the computation field alone must not authenticate the field-valued point map. EQUIVALENCE, partitions, `same_as`, and multi-edge paths belong in the negative matrix as well. Keep the kernel model-blind by passing validated semantic facts through one authority-binding boundary.

### P2: semantic model changes are misclassified as AMEND

`kernel.MODEL_LICENSING_FIELDS` contains only `ring_vars` and `generators`. Direct calls to the actual classifier label changes to legacy field, point universe, characteristic, open conditions, and embedding as `AMEND` with no moved fields. A full native fold also accepts changing BASE to ALGEBRAIC_CLOSURE under AMEND. This is a confirmed classification defect; it does not by itself prove stale evidence is accepted, because stale-model and fingerprint checks provide additional defenses.

Add a small Phase A guard fix for existing semantic fields, with regression controls for under-declared AMEND and legitimate prose-only amendment. In B, add the new field/reach attributes to supersession and to the relevant verifier input fingerprints. Audit claim witness data and family/evidence dependencies in the same bounded field inventory; do not infer completeness from the current tuple lists.

### Acceptance and lifecycle are part of the implementation

The existing CI workflow runs only the deterministic non-live selection on Linux; it does not run the DK runner or a pinned CAS lane. Three successful repeats are not a substitute for failing on every unexpected attempt. The original shell runner records the check exit after declare and can show exit 0 after a refused declaration against an empty graph. The new acceptance runner must capture declare, verify, and check statuses separately, together with the fold/verdict/finding content.

Do not leave an intentionally red historical runner as the release gate. Preserve all old observations and add prewritten post-fix assertions/delta contracts so the release gate is green only for the expected repairs. Capture full stdout/stderr for each D2 attempt. Pin Singular's package/build as well as its headline version and record the execution environment.

No package-wide refactor is justified by this review. The architecture already separates mathematical checking, authority binding, and derived views well enough to make the repairs locally. New schema fields must be accounted for in closed format validation, migration, semantic fingerprints, supersession, schema/help, export/publication classification, and the Lean epoch shadow where applicable.

## Proposed implementation sequence

1. **Freeze acceptance inputs.** Import the bounded DK controls by pinned source commit and LF digest. Keep originals immutable, add intended post-fix assertions, and document exact command exits. Add open-slot and semantic-AMEND negative controls before code. Keep bulky campaign material in the companion repository.
2. **Guard PR, v0.32.** D1 refuses unsupported family premises with a useful discharge; D3 refuses disposition-only fields on wrong claim kinds while preserving legal family PREDICATE `asserts_count`; fix semantic model AMEND grading. No family-to-model theorem bridge yet.
3. **Witness and history PR.** Replace nesting proportional to ring dimension with a bounded-depth simultaneous constant substitution. `cas.substitute_and_reduce` already demonstrates Singular map declarations through CASProgram; reuse that boundary or equivalent safe generation. Preserve rational/finite-field coordinate validation, completeness, equation/guard polarity, backend provenance, and inconclusive behavior. Test 96, 97, 138, 174, 1024 variables, negative witness/guard controls, and three repeated live boundary runs. Document source construction cost and arithmetic/term budgets rather than promising unbounded computation. Fix history for all supported supersedable entity types and its model-inclusive tally.
4. **Operational affordances PR.** Define UNRESOLVED as non-authoritative operational state, with stable family/locus identity, reason enum, structured budget value/unit, attempt identity, and explicit resolution/replacement history. It contributes no coverage and cannot satisfy an open premise. State its graph-format/storage compatibility decision. For `check --seam unchecked`, use an explicit accounting-rule selection, durable JSON `unchecked` status, and the one-line text banner. Never advertise omitted transports as clean/verified or let this mode clear full-check hook baselines or issue evidence authority. Malformed graphs still refuse; specify which structural semantic refusals remain unavoidable at load time. Keep scope migrations and the P0 relaxation out of A.
5. **Ship A and run bounded T2.** Preserve D-E5-GAP first, actual misuse outcomes, and the six-chain delta. Pick one queued bounded customer task separately; measure changed decisions/open premises and custody commits per accepted claim, with 189 as the pinned DK comparison count. This review does not select or launch a new math campaign.
6. **Epoch-12 design gate.** Write the concrete field/quantifier rules, model/witness interpretation, per-certificate migration table, mixed family/model composition contract, and expected discharges first. Require the controls below before implementation. Then implement B in small authority-boundary changes, replay the DK ledger, maintain Lean parity, and write SEAM.md from actual checked examples.

Lane Watch's `directive` event belongs in the separate `math-research/infrastructure/agent-observer` project. Keep it independently first in implementation scheduling, as requested by the packet. Define timestamp, immutable text, recommendation-at-time, event identity/author/source, replay order, and display behavior there; a directive is not theorem evidence. No Lane Watch action or message was sent during this review.

## Mandatory additions to the epoch-12 test matrix

| Control | Expected |
|---|---|
| R witness for x^2-2 -> ANY_ORDERED | Refuse universal generalization; Q counterexample retained. |
| C witness for x^2+1 -> ANY_CHAR_0 or R | Refuse. |
| Q-defined closure witness i -> R through each edge type | Refuse unsupported point transport; preserve P0. |
| Exact rational witness -> R; exact real-embedded K witness -> R | License with compatible model, point universe, and coefficient maps. |
| ORDERED uniform certificate -> R and Q; same certificate -> C | License first two; refuse C unless independently justified. |
| Selected-root sign receipt -> other root or universal reach | Refuse absent an independently checked invariant/uniform argument. |
| Covered real chart versus missing boundary; localized receipt not verified | License only the appropriately covered, currently justified case. |
| `NO_RATIONAL_POINT_SEARCH`, timeout, cap, stale or missing certificate | Cannot produce EMPTY authority; operational UNRESOLVED is the repair path for unfinished work. |
| Old true certificate in characteristic 2 for 2*x-1 -> CHAR_0 | Refuse authority upgrade; retain finite-characteristic semantics. |
| Ambiguous K string, contradictory about/compute fields, unknown/missing universe | Explicit refusal or documented non-authoritative legacy reading; no guessed real embedding. |
| Reach/embedding/about/compute change after a VERIFIED receipt | Old authority stale; semantic supersession required. |
| Family premise order permutations, enumeration debt, EXCLUSIONS-only evidence, stale enumeration, open E5 | No crash, no authority gain, no disappearance of the open slot. |
| EMPTY/NONEMPTY/IDENTITY/PREDICATE across every edge and mixed path | Preserve justified scheme-side, profile-split, and identity-descent semantics. |

## Decisions to settle

The recommended narrow A interpretation is **crash refusal now, successful family/model composition in B**. This follows T1's frozen fixture contract, but amends A1's broader wording.

For the later composition contract, “minimum authority” needs an exact definition. `established_by` is provenance, not a numeric order, and the existing `ladder` describes evidence quality without itself licensing transports. Preserve premise evidence direction, current verification status, and enumeration obligations separately; do not turn a minimum ladder value into theorem authority.

For B, accept **one field vocabulary with distinct extension and quantifier-instantiation judgments**, while retaining existing point-universe/witness/embedding information. If the literal “one order relation does everything” constraint is non-negotiable, stop B with the explicit counterexamples above.

UNRESOLVED needs a concrete operational schema and compatibility choice before coding; its no-authority requirement is settled. STALE_OVERLAP on the present DK pair should be deferred without requiring a new layer vocabulary to justify the deferral.
