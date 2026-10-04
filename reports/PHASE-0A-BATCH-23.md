# Phase 0a — portable section receipt controls

GP-X255–257 add a valid section acceptance control, stale proof-edit refusal and fresh-binding false-identity refusal. Inputs contain exact rational source/target rings, equations, section images, proof rows and any previously bound rows; they contain no legacy graph events or verdict constants. The adapter constructs the historical native graph and reads actual freshness/fold results independently of the expected verdict.

The valid receipt projects authority. The edited receipt with its old fingerprint remains stale. The false cofactor with fresh producer metadata projects VERIFIED_SECTION and is retained as KNOWN_DIFFERENCE, class section_cofactor_not_replayed_under_fresh_producer_binding. Its expected REFUSE is unchanged. This differs from the five conservative-refusal differences already retained.

The question is section evidence admission, not a complete inference: no separate no-invention verdict is supplied. Producer execution metadata is fabricated from the frozen test fixture; no actual backend run or live attack is claimed. The separately retained section diagnostic independently expands the row and verifies that the altered cofactor is false. The replay-only successor needs arithmetic checking at admission, not merely a fresh fingerprint.

Total: 298 cases, 85 expected ACCEPT and 213 expected REFUSE. Full replay: 289 agreements, six known differences, one diagnostic observation, one pending case and one unsupported case. No ERROR or REVIEW_REQUIRED. All 295 prior case files remain byte-identical, and runner, route, adapter and case hashes match the final replay.

Replay: oracle-runs/20260928T132445125437Z.json. An initial schema validation stopped before replay because scope_or_region contained prose rather than its enum; the metadata was corrected to N/A without changing expectations or mathematical inputs.

Current source coverage remains 57 partial / 311 unreviewed. Phase 0 is active; the manifest and later Lean-spike prerequisites remain open.
