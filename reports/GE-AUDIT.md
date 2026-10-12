# Gate GE statement-fidelity audit

- **Commit:** `c70598be15a6e4eb45c8908fb65196429a417557` (workspace master).
- **Emit:** 1825 of 1891 claims in 33 shards; 62 EMPTY deferred, 4 unsupported. All 99 emitted files match `comparator-MANIFEST.json`, and the emitted manifest is byte-identical to the committed one.
- **Seed:** 20261009 (`random.Random`, claims sorted by ledger key). The draw took 5 from map, 2 from point and 2 from bridge/source, then 11 uniformly from the rest.
- **Result:** 20 of 20 faithful. **Zero defects.**

| Key | Theorem | Class | Verdict |
|---|---|---|---|
| 635 | realizable_C9_38_x7 | map-p | faithful |
| 1387 | realizable_C9_265_x2 | map-p | faithful |
| 458 | realizable_C9_29_x3 | map-p | faithful |
| 1020 | realizable_C9_221_x3 | map-p | faithful |
| 290 | realizable_C8_39_x5 | map-p | faithful |
| 663 | realizable_C9_87_q | point-s | faithful |
| 1873 | realizable_C9_363_p199 | point-p | faithful |
| 41 | realizable_AG23_in_chi_3 | bridge | faithful |
| 24 | realizable_U36_in_chi_5 | bridge | faithful |
| 206 | realizable_C8_12_q | point-s | faithful |
| 967 | realizable_C9_137_q | point-s | faithful |
| 1413 | realizable_C9_307_x5 | map-p | faithful |
| 1647 | realizable_C9_273_q | point-s | faithful |
| 1389 | realizable_C9_265_x5 | map-p | faithful |
| 548 | realizable_C9_21_q | point-s | faithful |
| 553 | realizable_C9_21_p11 | point-p | faithful |
| 721 | realizable_C9_171_x3 | map-p | faithful |
| 637 | realizable_C9_44_x2 | map-p | faithful |
| 1123 | realizable_C9_114_x3 | map-p | faithful |
| 815 | realizable_C9_118_x2 | map-p | faithful |

**Method.** For each claim, I read the Lean statement and recorded a one-sentence reading in `work/readings.json`. Only then did I open the ledger. I then compared four things:
- the hypotheses with the ledger's kind and scope;
- the `lines_*` with the matroid file, mapping element i to `Fin` index i−1 (by script for every claim, and by hand for four);
- the line data with the conditions for a simple rank-3 linear space;
- the claim's status (held).

**Checks beyond the sample**, all of which pass:
- All 1825 theorems: hypotheses, scope lists, lines, encoding digest and held status.
- All 33 configs: no `definition_names` holes, and `theorem_names` exactly match the challenge theorems.
- All challenge files: only `import Mathlib` and one shared `RealizesRank3`, with no instances, notation, axioms, metaprogramming or sorried definitions.
- Source000 and MapOut000, read in full because the sample drew neither class.

**Pitfalls checked:**
- From the brief: wrong lines, wrong quantifiers, vacuity, degenerate witnesses, junk values, unfaithful vocabulary and out-of-scope imports.
- From Lane O: P01–P26 and P30–P41.

**For Will (not defects):**
1. **The quantifier on NOT_IN_IDEAL(1).** It is stated for *every* algebraically closed field of the scope. This is equivalent to "an algebraically closed field" because ACF_p is complete, and it is the stronger form.
2. **The challenges state realizability directly.** They do not depend on ENCODING-FRAME. CATALOG-COMPLETE affects χ coverage, not any single statement.
3. **`RealizesRank3` is faithful because the line data is a valid linear space.** The encoder enforces this, and every emitted claim passes it.

Lean was not run.
