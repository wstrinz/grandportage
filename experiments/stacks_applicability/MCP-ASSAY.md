# TheoremSearch MCP assay

**Run:** 2026-07-31
**Endpoint:** `https://api.theoremsearch.com/mcp`
**Source filter:** `Stacks Project`
**Authority:** none

Three fuzzy JC-shaped queries were sent through the public `theorem_search`
MCP tool. The results below are observations about discovery quality, not
mathematical evidence and not part of the pinned theorem shelf.

| Query shorthand | Relevant result | Rank | Score |
| --- | --- | ---: | ---: |
| finite module element in every ideal power | `00IP` | 1 | 0.730 |
| compatible nonempty finite truncation tower | `01Z2` | 3 | 0.638 |
| lci gives a two-term cotangent complex | `0D0K`, `0FV0`, `0FV6` | 1--3 | 0.689--0.657 |

An almost statement-level inverse-limit query returned `01Z2` first with score
0.891. The fuzzy version still found it, but ranked two neighboring limit
results higher. The lci query found mathematically relevant sibling results but
did not return the proposed `08SL` in its top three.

This is the desired discovery behavior and the reason it cannot be authority:

- recall is useful even when the exact anticipated tag is not first;
- neighboring results may expose a better formulation;
- rank and score are unstable search outputs;
- the official tag statement and its hypotheses still need inspection; and
- a pinned local source remains necessary for reproducibility.

The sidecar therefore accepts official four-character Stacks tag URLs from the
MCP response, marks the entire response `authority: NONE`, and refuses to copy
scores or generated slogans into a theorem pin.
