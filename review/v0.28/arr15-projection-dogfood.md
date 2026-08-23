# ARR15 compact-projection dogfood

Authority: `DERIVED_READ_MODEL_ONLY`

Graph effect: `NONE`

## Tool feedback

The canonical ARR15 graph contained 452 records and 702,238 bytes with raw
SHA-256 `16edf1434bfdd660f0d3f89786590b5f6c053f8e162c8701f65c455470445dcd`.
The compact projection selected all 452 records, omitted none, and produced
179,162 bytes with projection fingerprint
`sha256:a2f2cde3e17d9048a6fa0ada96738c5de8b13f3549a9ed3d11bbea6c8355e3d6`.

The first real invocation exposed a filesystem defect: an exact output path
failed when its parent directory did not yet exist. The writer now creates the
declared parent, and a regression test covers that behavior.

The projection is substantially smaller, but its current rows expose only line
number, byte count, digest, key names, and label. They omit the values needed to
review event kind, status, scope, relation, and authority. It is therefore a
content-addressed digest index, not yet a semantic review projection. A future
revision should add a deliberately bounded allowlist of semantic fields while
remaining reconstructible from the graph.

## Campaign observation

No object-level ARR15 conclusion is drawn from this projection. Even with every
record selected, the omitted values prevent a cold reviewer from determining
which results are current, stale, refused, or licensed. That limitation is a
tool finding, not evidence about the campaign's mathematics.
