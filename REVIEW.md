# Current review brief

This is the attack surface for the current release. The full historical review
through v0.18 is preserved in `HISTORY/REVIEW-through-v0.18.md`.

**Version <!--version-->0.35.0<!--/version-->, graph format
<!--graph-format-->8<!--/graph-format-->, kernel epoch
<!--kernel-epoch-->12<!--/kernel-epoch-->, and
<!--checks-->1771<!--/checks--> collected checks.**

## Highest-risk claim

For a cold campaign read, run `gp review`. It is the checked-seam equivalent
of `gp check --history --full`: current authority debt, full carried detail,
and findings retained on superseded generations are all visible without
requiring a returning agent to remember the safe flag combination. Plain
`gp check` remains the concise enforcement-oriented surface.

For v0.34, attack the new semantic seams. A certificate declaration must never
mint effective reach; only a current, model-bound verifier receipt may do so.
Try every otherwise-licensed point edge with incompatible `about`,
`point_universe`, and selected embeddings, including `same_as`. Attack
historical migration with misleading booleans and unknown certificate names.
For `family_bridge`, vary premise order and independently remove exact
enumeration, proved coverage, exhibited membership, and the model binding. The
frozen DK E5 gap must remain open under EXCLUSIONS-only evidence.

For v0.33, attack the fold-time boundary itself. Every verdict subject must
pass through `authority.check`, `bind`, and `project`; stale evidence and failed
representation replay must project nothing; negative elimination and point-lift
proof objects must not erase earlier accepted authority. Ordinary callers must
not mint the sealed receipt types, and folding must not serialize them or change
the graph bytes. The source-shape gate and all-subject characterization matrix
live in `tests/test_architecture.py` and `tests/test_authority_binding.py`.

For v0.32, attack the simultaneous Singular point map with false points,
coordinate references, guards and large rings; the live release controls
cover 96/97, 138, 174 and 1024 variables. Check that non-COUNT rejection
retains repaired history, and that semantic model edits propagate RELICENSE.
The separate work log must never license a claim: malformed logs refuse,
resolutions are operational, and unchecked receipts cannot become full-check
baselines. Frozen DK findings and open-premise slots are pinned in
`tests/fixtures/dk_retrodiction/` and `tests/test_guard_release.py`.

Grand Portage now has a small semantic kernel and a nontrivial certifying-
checker trust base. Review both separately. A correct transport table does not
repair a parser, canonicalizer, cofactor replay, fingerprint binding, or
authority-projection defect.

v0.29 added a selected-embedding trust boundary. Attack `model.embedding`'s
closed REAL/COMPLEX shapes, exact rational bounds, identity-map endpoint
comparison, asymmetric-selection handling, semantic endpoint fingerprints,
and the distinction between a genuine polynomial field automorphism and an
identity of selected images. A required edge id must never substitute for the
real map payload or either endpoint definition.

v0.30 separates the ordered producer from an independent
`selected_real_interval_v2` receipt checker. Attack
`REAL_CLOSURE`/REAL-embedding coupling, endpoint roots, repeated roots, Sturm
variation counts, polynomial gcd zero detection, rational interval enclosure,
degree/coefficient/refinement budgets, native execution provenance, and
fold-time receipt replay. Mutating a chain, variation count, selected interval,
or sign must fail before authority activates. An invalid isolator or undecided sign must remain
`UNVERIFIED`; a nontrivial automorphism must not transport a sign predicate;
and direct incompatible sign claims should create debt without guessing which
claim is false.

v0.31 adds a release-critical scope parser and historical-format read boundary.
Attack field-relative `EMPTY` claims with missing, non-field, noncanonical,
oversized, composite, and implementation-drifted scopes. Formats 1--4 must not
acquire an implementation field they never carried; formats 5--6 must preserve
and validate theirs without demanding equality to the current binary. Neither
direct read nor migration may turn malformed history into current authority.

v0.31.1 closes the adjacent model-typing bypass. Attack field-relative
`EMPTY` claims whose owner model omits either `coefficient_domain` or
`point_universe`, including historical graphs and migrated logs. The checker
must report current `UNSOUND_PREMISE` debt without making old logs unreadable.
A typed model is necessary but not sufficient evidence: this patch does not
infer that a combinatorial certificate proves geometric emptiness.

v0.31.2 makes a retained `VERIFIED_DERIVED` identity cofactor equation the
authority boundary instead of the reader's ambient Singular installation.
Attack the receipt's target, ordered ring variables, exact model generators,
cofactor count, coefficients, characteristic, and input fingerprint. A
different or unavailable local backend must not change the folded answer; a
malformed receipt must never inherit this backend-independent path.

The other new v0.30 authority is `simple_number_field_v1`. Attack the
irreducibility check, quotient reduction, rational-function denominator
inverse, exact coordinate coverage, equation/guard polarity, witness/model
fingerprint binding, and the `ALGEBRAIC_CLOSURE`-only boundary. A witness field
must never become the model coefficient field by implication, and a BASE or
ordered extension witness must fail closed.

Finally attack verdict lifecycle: a latest `UNVERIFIED` attempt must remain an
actionable seam and must be retried by a later batch. Native authority is legal
only for a closed verifier-native contract; fake or injected CAS answers must
be recorded at most as inconclusive history.

v0.25 makes implementation identity and distributed campaign custody a release
boundary. Attack source commit/dirty reporting, format-5 graph provenance,
MCP/CLI identity agreement, backend freshness across process restart, absolute
root pinning, finding-receipt fingerprints, and immutable format migration.
Historical `unavailable` backend identities must remain stale.

v0.24 added a second release-critical boundary: `public-snapshot-v1.json` and
`scripts/public_snapshot.py` decide which exact Git blobs enter the public
mirror. Attack its classification precedence, path normalization, required-file
set, generated receipt, and refusal of unclassified paths independently from
the mathematical kernel.

## Backend identification and execution custody

The argv-keyed Singular identity cache retains failed probes for the process
lifetime. A later computation can complete while authority remains unavailable.
Attack recovery by retaining an execution with an unavailable identity, then
successfully identifying the backend: the old frozen artifact must keep its old
identity. Never let a later aggregate identity rehabilitate unidentified runs.
`tests/test_backend.py::test_later_backend_identity_does_not_rewrite_earlier_execution`
pins artifact immutability with a non-authoritative adapter; it is not a proof
that an argv/version probe identifies the exact binary used by every process.

`execute` currently snapshots identity after the process returns; `provenance`
also reads the current identity when aggregating. An argv cache cannot detect
binary replacement at that path. Before adding automatic probe retries, require
per-execution identity agreement, mixed-trace refusal, and retained controls for
replacement/recovery. No retry-policy or native-authority change is made here.

## Read-only IR-v2 experiment

Attack `project_v2` for invented context, manufactured requirement discharge,
process-level identity copied into per-execution slots, and stale receipts
reported current. Its JSON is DERIVED_READ_MODEL_ONLY with graph effect NONE;
PROJECTABLE is a data skeleton, never an earned runtime licence. Check both
Lean-name dictionaries for drift and distinguish UNKNOWN from countermodels.
The corpus triggers the missing-context stopping condition, so no epoch/format
recommendation follows from this run. See docs/IR-V2-PROJECTION-REPORT.md.

## 1. Authority binding

Attack every path that turns a checked report into graph authority:

- mutate the model after producing evidence;
- change coefficient domain or point universe;
- reorder ring variables, generators, guards, or intermediate states;
- replay a certificate across charts or semantically similar model ids;
- preserve a verifier verdict while changing its representation;
- mix current and stale verdicts across supersession or merge;
- attempt to promote standalone evidence whose authority boundary says none.

The key positive control is exact replay against the same model fingerprint.
The key negative control is a locally verified result that still cannot travel
to a parent without a licensed transport or exhaustive cover.

## 2. Exact checker

Treat the polynomial representation, parser, canonicalizer, sparse arithmetic,
budgets, and certificate expanders as part of the trusted implementation.
Differentially attack them with external CAS systems as untrusted oracles:

- variable permutations and simultaneous substitutions;
- reordered generators and equivalent cofactor families;
- characteristic changes and inadmissible denominators;
- sparse/infix and Laurent/export round trips;
- large coefficients, exponents, term counts, and boundary budgets.

A bounded search miss is typed ignorance, never refutation.

## 3. Transport semantics

The transport table remains the most concentrated mathematical risk. In
particular review identity variance, point-universe scope, coefficient-domain
expressibility, partial maps, mapped predicate pullback, partition
recombination, and image-closure asymmetry.

Mapped `ring_iso` authority is no longer an unaudited boolean: current
verification checks both ideal pullbacks and both inverse-map compositions.
Attack the verifier and its graph binding rather than the obsolete declaration-
only design.

## 4. Merge and identity

The v0.19 fan-out assay now exercises two valid branches creating different ids
or normal forms for the same mathematical object. It confirms:

- differently normalized redeclarations of one id refuse with a field diff;
- cross-branch supersession exposes consumers still anchored to the old model;
- stale and current verdicts compose with only the current one effective.

It also exposes the remaining seam: exact affine objects under different ids
merge cleanly and require an explicit alias-audit view. GP correctly does not
infer full mathematical identity from names or a heuristic signature.

## 5. Read surfaces

Ask a cold reader:

- what is established;
- what is intentionally carried;
- what is stale or refused;
- why a conclusion is licensed;
- what the first unresolved authority seam is.

Compare the answer with the folded graph and accepted baseline. Projection and
visualization are useful only if they improve that answer without becoming a
second source of truth.

## 6. Extracted campaign review

The signed-off JC attack surfaces through v0.27 moved with their fixtures and
replay machinery to the optional
[`grandportage-jc-campaign`](https://github.com/wstrinz/grandportage-jc-campaign)
companion. Its `CAMPAIGN-REVIEW.md` preserves the historical brief verbatim.
The core review surface is now deliberately domain-neutral.

## 7. Project-level falsification

`KILL-CRITERIA.md` remains binding. A6 is now live: validators have dedicated
test suites and the certifying checker is a real trust surface. The relevant
question is no longer whether validators are tiny, but whether they remain
bounded replay checkers, share a small exact substrate, resist differential
attacks, and compose into conclusions worth their cost.
