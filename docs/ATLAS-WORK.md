# Atlas work record

Started 2026-09-13 against local v0.34.0, graph format 8, kernel epoch 12,
commit c89d055. This executes the transport-atlas packet with the corrections
identified in review. It is not a release declaration.

## Work sequence

1. Establish source-backed dictionaries and enumerate all 56 kernel cells,
   conditional alternatives, context gates, and multi-premise inference forms.
2. Extend the non-authoritative Lean shadow: bounded reach instantiation,
   stability restriction, relational transfer, witness custody, and ordered
   certificate interpretation. State every assumed algebraic premise.
3. Repair demonstrated GP read-surface drift and add executable reach parity.
   Preserve graph format, kernel epoch, and transport licences unless a
   reproduced soundness defect demands separate treatment.
4. Produce the mapping, findings, and a bounded broader research program.
5. Run Python checks, Lean build, cross-language parity, and documentation
   checks. Record the next-release implications and remaining proof boundaries.

## Corrections to the supplied packet

- StableUnder is already relation-parametric. Instantiation over a class and
  extension from one concrete field are different operations.
- A replayed equality can survive a context change while its contradiction
  interpretation does not. NONE is absent authority, not a countermodel.
- Every binary relation induces the powerset adjunction used by GP.
- Equality needs different relation structure from existence. Witness custody
  is stronger than existential nonemptiness; HOL types cannot model empty
  solution sets without an explicit model predicate.
- Coordinate-ring claims need an algebraic dictionary, not a presumption of
  inexpressibility or novelty. Missing correspondence is not a kernel defect.
- Audit check.py's field gate and evidence binding, not only kernel.py.
- Distinguish proved interface laws from discharged algebraic interpretations,
  runtime parity, conservative refusal, and unverified literature assignments.

## Progress

- Baseline: 73 focused Python tests passed; Lean build passed, 28 jobs.
- Found a reproducible read-surface defect: gp table still presents historical
  Boolean scope as the current certificate summary, including ORDERED_SOS_CERT.
- Completed [the 56-cell mapping](ATLAS-MAPPING-V0.md), including conditional
  alternatives, context/evidence gates, and multi-premise forms. A regression
  test compares its complete inventory with the live kernel table.
- Added `Atlas.lean`, aggregate import, executable `AtlasParity.lean`, and the
  fail-closed Python comparison. The new CI job builds Lean and runs parity.
- Corrected `gp table` to describe certificate policy ceilings and current
  verifier-earned reach. The historical Boolean registry remains compatible
  and is explicitly marked legacy in the authority manifest.
- Wrote [the research program](PRESERVATION-ATLAS-PROGRAM.md), updated the theory
  ledger, and linked the work from CURRENT.md. No version, format, epoch,
  transport licence, or verifier behavior changed.

## Initial validation

- Initial full Python run: 1,683 passed, 59 live skipped, one failure because
  adding a regression test made marked documentation counts stale.
- After the complete eight-test addition and `gp docs`: 1,691 passed, 59 live
  skipped, zero failures, 110.99 seconds. All 1,750 collected tests are accounted
  for by this run plus the separately required live lane.
- Focused atlas/authority tests: 16 passed. Final inventory recheck: 7 passed.
- Lean build: 29 jobs passed. Only the pre-existing LaurentLowering
  unnecessarySimpa and Exhaustive unusedVariables warnings remain.
- Cross-language comparison: all 139 canonical reach/extension decisions agree.
- `gp docs`: every marked span agrees at 1,750 checks. `git diff --check` passed.
- Hosted CI has not run in this local session. Passing static checks alone is
  not a full release validation.

## Initial live diagnosis

The initial required live run reached the JC dm4 materializer after reporting
four failures, then stopped producing test-level output and was interrupted.
That invocation did not complete the 59-test live lane. All 59 tests subsequently
have passing results across the completed prefix and isolated runs below; this
is not a claim that one uninterrupted full live invocation passed.

The structured-condition test passed alone (27.45 seconds). Three authority
tests reproduced their refusals together: the backend was non-authoritative,
despite successful algebraic computation. Inspection showed that the existing
Singular version probe caches unavailable results for the process lifetime.
Running the probe with a 120-second timeout, without changing GP source or
acceptance rules, identified Singular 4.2.1; all three authority tests then
passed (32.59 seconds). This supports a transient identification failure
amplified by caching, rather than a defect in the new table explanation.

The 16 live tests after the stalled materializer were then run separately with
successful backend identification: 16 passed, 81 deselected, in 60.37 seconds.
Together with the completed prefix and four successful isolated reruns, this
accounted for 58 passing live tests.

The isolated materializer then PASSED in 791.73 seconds (13 minutes 11 seconds),
with successful backend identification first. Process inspection showed new
Singular invocations during the quiet interval. The implementation independently
checks 17 retained generators, with separate reduction and cofactor-producing
calls per membership. The observed silence was not evidence of deadlock. The
initial description of a stall should be read as lack of test-level progress,
not a diagnosed process deadlock or mathematical failure.

Final accounting: 1,691 deterministic tests plus all 59 live tests have passing
results, covering all 1,750 collected checks. Live authority identification
needed a longer probe in this environment; the existing process-wide cache of
unavailable identities remains a reliability follow-up. Recovery must preserve
per-execution provenance rather than bless older unattested answers. No backend
or verifier change was made in this work.

## Disposition

This is an unreleased candidate for a small GP improvement plus a first research
slice. The mapping records no reproduced false licence. It does record a
conservative IMAGE_CLOSURE/ALONG/EMPTY opportunity, with the evidence needed for
a future extension. The next research experiment should formalize one
certificate's polynomial evaluation and interpretation before building a broad
requirements solver. No release tag, publication, or remote push was performed
for that initial slice.

## Certificate-interpreter continuation for review

The user authorized proceeding with certificate interpretation and composition,
and committing and pushing the results for review. The continuation is prepared
on `atlas/certificate-interpreter` against `origin/master` in the private
`wstrinz/grand-portage-workspace` repository. No public-mirror release is implied.

- `CertificateInterpreter.lean` proves a small equational calculus sound under
  evaluation, then derives ordered contradiction from an explicit derivation.
  The x²+1 certificate has a supplied derivation; ordinary integers discharge
  every algebraic and ordering premise. Gaussian-integer evaluation retains the
  equality and supplies a root while ruling out the ordering.
- The formal sample is serialized by `InterpreterParity.lean`, replayed by the
  Python SOS checker, and compared with the fixture used by graph tests.
- Seven new tests exercise declaration versus replay, the ANY_ORDERED → R → Q
  path, point-context refusal, incompatible final targets, graph-construction
  refusal of a changed point universe, rejected proof input, stale receipt
  binding, and drift to a different valid certificate.
- The bounded proof and remaining parser/rational-normalization obligations are
  described in [CERTIFICATE-INTERPRETER-V0](CERTIFICATE-INTERPRETER-V0.md).
- Focused graph/comparison tests: 7 passed. Lean build: 30 jobs passed, retaining
  only the two pre-existing linter warnings. Both executable comparison gates
  passed. The initial cold interpreter-executable attempt timed out at 120
  seconds; direct execution and subsequent normal gate runs succeeded.
- Final deterministic suite: `python -m pytest -q -m "not live"` passed all
  1,698 selected tests, with 59 live tests deselected, in 211.26 seconds. The
  collection is now 1,757 checks, and `gp docs` synchronized every marked span.

The production Python changes remain exactly the previously validated CLI and
legacy-registry clarification. The new continuation changes proofs, executable
example comparison, tests, CI, and documentation. It introduces no transport
licence, verifier change, graph migration, version bump, or kernel epoch change.
The earlier 59 passing live tests remain the live evidence for that same
production code; the deterministic suite is rerun for this expanded collection.
Hosted check results and the review URL belong to the pull request record.
