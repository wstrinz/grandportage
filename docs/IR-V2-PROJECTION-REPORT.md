# IR-v2 projection: stopping condition reached

**No epoch-13 or new-format recommendation is issued.** The packet requires a
stop if more than a small minority of nodes would need invented fields. The
prototype fixes that threshold at 10% missing model contexts. The measured
fraction is 72/73 (98.6%); it reports gaps instead of filling them.

## Corpus and counts

`review/ir-v2-projection/index.json` lists every source, source SHA-256 (CRLF normalized to LF), adapter,
report path, and category count. `python scripts/project_ir_corpus.py` reproduces
reports without writing any graph. The inventory found ten stored event files
under fixtures/tests/fixtures/examples, plus two existing ARR15 model payloads,
the ordered atlas sample, and a literal existing Cloquet/Match4 regression.
Twelve inputs loaded; two historical negative fixtures were correctly refused
(missing family bridge and COUNT-only fields on a PREDICATE).

| Category | Projectable skeleton | Unprojectable |
|---|---:|---:|
| Model context | 1 | 72 |
| Claim | 1 | 99 |
| Conditional step profile | 28 | 3 |
| Evidence | 0 | 32 |
| Binding | 0 | 0 |
| Inference licence tree | 0 | 33 |

Of the 33 inference attempts, 15 remain clean under the current checker on
the loaded snapshot; none reconstructs a complete IR proof tree. Conditional
step projection preserves the kernel cell and references the applicable
check.py gate functions; it does not claim the gate predicates or atlas
justification have been proved. The JSON-to-Lean interpretation is an external
premise. Both dictionaries of Lean declaration names are mechanically checked.

## Reasons, ranked and qualified

1. **Missing interpretation context:** `about` has 185 occurrences across
   model/claim/licence rows; missing generators and ring variables have 172
   each. These are dependency-propagated counts, not 185 distinct models.
   Computation field and point universe each have 171; characteristic has 113.
2. **Missing structured predicate interpretation:** 58 occurrences. A prose
   statement cannot be assigned a formula merely because its kind is PREDICATE.
3. Leaf receipts are missing in 33 licence rows; actual requirement discharge
   is absent in all 32 evidence rows. Eight COUNT projections also lack an IR
   claim-kind adapter. Nonlocal partition/family composition is explicitly
   outside this first IR tree adapter, not a newly discovered runtime defect.

`PROFILE_FROM_TAG` is **21/21 = 100%** of tagged certificate declarations or
receipts encountered. Here all 21 are declarations: there are **no retained
verdict receipts** in the loaded corpus. Other operational evidence remains
separate in the denominator. The flag identifies attempted tag-based profile
recovery; the projector leaves actual discharge null and never mints a profile.
This is not a measurement that 100% of GP's real verifiers are tag-driven.

## What the result does and does not decide

Most measured sources are format 0 or 7, not full format-8 campaign snapshots.
The four format-8 wrappers package existing fixture data in memory and explicitly
record synthetic ids/meta; they do not supply absent mathematical context. The
ARR15 inputs are model payloads and the Cloquet input is one regression, not
complete live campaigns. Historical events use the existing compatibility
reader semantics. Native binary identity is not re-probed; conclusions are
relative to the loaded portable snapshot, never a new native authority audit.
Mutation tests separately exercise a real verifier-native ordered receipt,
input drift, graph-byte preservation, and refusal to manufacture profiles.

The strongest argument against treating these failures as justification for a
new format is **corpus mismatch**: legacy sketches and a deliberately incomplete
IR (COUNT/family/partition/rational gaps) explain much of the deficit. Conversely,
relabeling reach alone cannot represent the checked incomparable requirement
profiles or model-indexed observations. These two facts delimit the question;
they do not settle a storage migration.

Stop here as required. A subsequent experiment needs a representative retained
format-8 campaign snapshot with receipts, supplied without semantic backfilling,
and must distinguish source-data gaps from missing IR adapters. Only after that
measurement should a graph-format recommendation be considered.
