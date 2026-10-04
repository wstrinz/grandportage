# Legacy conservatisms identified during Phase 0

GP 0.50 has no kernel yet. These are observed v0.37 conditional-rule refusals.

| Cases | Missing sufficient condition | Evidence |
|---|---|---|
| GP-A08b / GP-A08c | p-integral certificate or witness with valid reduction | Exact controls and oracle table replay |
| GP-X03 | Exact image closure of an empty source | Frozen discharge register and oracle table replay |
| GP-X08 | Independent membership certificate in the target ideal | Exact target replay and oracle table replay |

Details and raw outcomes: reports/PHASE-0A-BATCH-1.md and reports/ORACLE-RESULTS.json.

# 3a profile conservatisms (G3a review §3, 3a.1)

Sound refusals where a weaker sufficient condition exists. Each entry names the condition not used.

| Where | Refused | Sufficient condition not used | Status |
|---|---|---|---|
| R2/R3 IN_IDEAL guard obligations | A loose guard without its own C1 certificate, even when it already occurs among the tight guards | A loose guard in `T.guards` is trivially a unit in `K[x][1/g_T]` | Costs one trivial certificate per shared guard |
| R2/R3 for NOT_IN_IDEAL(h), h ≠ 1 | Inclusion or map transport | NOT_IN_IDEAL(h) transports where its witness system does | NOT_IN_IDEAL(1) transports (3a.1 step 4) |
| COVER | R2/R3 transport of a COVER claim | Re-deriving the cover on the new system with a split tree | COVER is consumed by R4-by-cover; it is re-proved, never transported (3a.1 step 5) |
| COVER split trees | Trees over 255 nodes | A larger budget | Resource bound, like `maxExponent` |
| `proper` base checker | Characteristics where the two sample points give equal values (a² − a sampled at 0 and 2 is refused in characteristic 2) | Any pair of points where the values differ there, or a leading-coefficient argument | The adapter samples 0 and the first integer giving a different value |
| R1 | IN_IDEAL ⇒ VANISHES_ON across different systems | R1 composed with R2 on the tight system | Compose explicitly |
| `contra` | Contradictions between different presentations of one locus (EMPTY on S vs NONEMPTY on S′ with locus S′ ⊆ locus S) | A C4 inclusion certificate inside the conflict check | Only same-system pairs, plus VANISHES_ON(h) vs NONEMPTY with guard h |

Not conservatism. IN_IDEAL transport needs ideal-level equation obligations, because VANISHES_ON gives only radical membership. EMPTY does not move S→T along a map (GP-X360).

The runner's refutation report uses `Scope.overlaps`, which is executable and unproved. It only labels refusals and never admits anything.
