# Phase 0a — frontier status and observation identity

Fully read frontier.py, test_frontier.py and the complete CLI frontier handler. Eight source tests and four synthetic direct-API controls pass. The module accepts supplied records rather than loading the graph: its discharge/evidence assertions are not mathematical checking.

Unknown nonempty status FAILED defaults to CLOSED in item observations when frontier_state is absent. Explicit OPEN preserves the obligation. Proposed repair: require explicit state or an exhaustive typed mapping, with unknown status refused or left open according to an explicitly selected policy. This is a research display/aggregation risk, not a kernel proof admission.

Historical input fingerprints deliberately exclude discharge overlays and source descriptors. The same historical item has identical history identity before/after a discharge while the open set changes. Consumers needing full observation identity must bind the complete report; propose distinct names and a separate observation fingerprint. No hash collision is alleged.

Premise propagation requires exact scope exports and literal DISCHARGED; VERIFIED does not propagate even though both are classified closed. Direct discharges require evidence names but do not resolve those names. does_not_discharge is descriptive. Historical objects are preserved through normalization/copying, while returned dictionaries remain mutable. General cyclic/nonmonotone status semantics are not established by the eight tests or bounded iteration and remain outside any adopted 0.50 kernel design.

All 352 corpus cases remain unchanged and validate. No replay adapter, frozen source, campaign input, CAS, Lean work or publication changed. Source coverage is partial, and Phase 0 remains active.
