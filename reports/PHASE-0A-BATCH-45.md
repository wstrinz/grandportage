# Phase 0a — coefficient validation and error boundaries

Read the entire coefficient-expansion validator and dedicated tests, plus the coefficient CLI handler. Earlier GP-X27–34 cover selected/complete rows, overflow, invented rows and packing constraints. The existing Batch 3 XML contains 18 passing coefficient instances; names and hash are retained in COEFFICIENT-REVIEW.json, with no redundant suite run.

Complete coverage requires every index through the declared degree and exact row agreement; selected coverage never grants the converse. Both modes reject actual overflow above the degree. The test named selected_rows_may_omit_overflow uses degree two and omits the degree-two row, so it exercises an unselected in-bound coefficient rather than permitting out-of-bound support. Images, source equations and rows have different permitted variable sets; canonical packing also refuses shared coordinates between bounded inputs.

Four new direct/CLI controls reproduce a robustness defect. A coverage list reaches membership in a Python set before type validation and raises TypeError; the CLI does not catch it. An invalid string receives the normal CoefficientExpansionError and CLI code 2, while the valid control accepts. Superscript digit U+00B2 passes isdigit but fails int conversion: direct validation raises ValueError, which the CLI catches and reports as failure. No malformed input was accepted and no mathematical authority was created.

Proposed fix: validate coverage type before membership, require ASCII canonical row-key syntax before conversion, and normalize malformed-input failures to the domain error. Retain both direct API and CLI controls. A crash must not be silently classified as ordinary refusal in corpus extraction. Frozen source remains unchanged.

COEFFICIENT-ERROR-BOUNDARY.json records exact inputs, exceptions, output text and hashes. Separate parser/substitution budgets do not establish a cumulative request-cost bound; that and the arithmetic dependency remain open. Corpus stays 348 with unchanged replay. Coverage is 71 partial / 297 unreviewed; no fully semantic review claim. Phase 0 active.
