# Grand Portage cold web review: consolidated proof frontier

## Review posture

Review this repository as an independent cold reader. Do not assume that a
later file, newer timestamp, positive producer verdict, or narrower-looking
scope supersedes another record. The question is whether the new bundle
creates one honest current research boundary from several immutable derived
receipts without granting graph authority.

The repository base before this milestone is Grand Portage `825a0c8`. The
working milestone adds `frontier-bundle/v1`; use the checked files and tests,
not this packet, as the implementation authority.

## Read first

1. `CURRENT.md`, especially **Active release discipline** and **Derived proof
   frontier**.
2. `ARCHITECTURE.md`, especially **Adapters and read surfaces**.
3. `grandportage/frontier.py` and `grandportage/frontier_bundle.py`.
4. `fixtures/frontier/current_v1.json`.
5. `review/frontier-current-v1.json`.
6. The three bound consumer receipts:
   - `review/jc-h3-h8-c79-frontier-v1.json`
   - `review/jc-h3-depth6-frontier-v1.json`
   - `review/jc-h3-pin-ablation-frontier-v1.json`
7. `tests/test_frontier_bundle.py` and
   `tests/test_current_frontier_bundle.py`.

The CLI replay is:

```text
python -m grandportage.cli frontier-bundle fixtures/frontier/current_v1.json
```

## Intended result

The three receipts contain two repeated semantic IDs:

1. `JC.H3.B0.SOURCE.EXCLUSION` is open in both H8/c7_9 and pin-ablation views
   at exact scope `JC.H3.B0.FULL`. The manifest records `AGREE_OPEN`; it remains
   one open item.
2. `JC.H3.C79.SOURCE.FACE81.PIN_ABLATION` is open in the older H8/c7_9 view
   and `RESOLVED_TO_SCOPED_RESULTS` in the handback view at the same exact
   scope. The manifest records `SUPERSEDE` and names ten existing replacement
   items. It does not infer that the replacements are all closed.

The expected current count is 20 items: 12 open and 8 resolved. The output
must remain `DERIVED_READ_MODEL_ONLY` with graph effect `NONE`.

## Adversarial questions

Please try to falsify each statement:

- Receipt ordering and timestamps cannot resolve an overlap.
- Every repeated item requires exactly one explicit resolution.
- `AGREE_OPEN` refuses a scope mismatch, status mismatch, closed observation,
  or incomplete receipt list.
- `SUPERSEDE` refuses a non-open prior state, false current status, omitted
  receipt, repeated current/prior receipt, missing replacement, or self
  replacement.
- Receipt byte drift refuses before aggregation; CRLF/LF checkout differences
  alone do not drift the declared LF-normalized digest.
- The compact receipt's `open_items` must agree exactly with its item
  observations.
- The bundle cannot mutate a graph, create a verifier verdict, infer scope
  containment, source sufficiency, H3, or `(75,125)`.
- The checked current receipt regenerates exactly.

Look especially for a way an old open item could disappear without a valid
current closed observation, or a closed local result could erase a wider open
obligation.

## Research-boundary question

After the correctness review, rank the smallest actionable next artifacts
from the 12 open items. The leading candidates currently appear to be:

1. `JC.H3.SOURCE.TARGET_PAIR_TO_NORMALIZED_LAURENT_ROOT`
2. `JC.H3.C22_C710.NORMALIZED_LINE.RESULTANT_ROOTS`
3. `JC.H3.C22_C710.NONNORMALIZED_TRANSPORT`
4. `JC.H3.C21.RELAXATION`

Do not recommend a new graph relation, claim kind, or evidence schema unless
you can name a current composition gap that existing surfaces cannot express.
Do not request a math-stuff release gate merely to make this GP-derived view
green.

## Requested response format

Return:

1. `VERDICT: PASS`, `FAIL`, or `INCONCLUSIVE`.
2. Findings ordered by severity, with exact file and line references.
3. Any missing mutation or ambiguity that could change the verdict.
4. A ranked next-artifact recommendation with the smallest exact deliverable
   and explicit authority ceiling.
5. A short list of claims the bundle correctly refuses to make.

If there are no actionable findings, say so explicitly. Keep implementation
review separate from mathematical speculation.
