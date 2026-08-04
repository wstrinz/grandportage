# Consolidation assays

These are derived, non-authoritative stress tests for repository seams that
became load-bearing before v0.19.

`merge_assay.py` creates four genuine two-log fan-outs from shared prefixes.
It measures alias debt, differently normalized redeclarations, supersession
across branches, and stale/current verdict coexistence. Its main new finding is
that semantically identical objects under different ids merge cleanly and need
an explicit alias-audit view; GP does not pretend it can infer mathematical
identity from names.

`differential_affine.py` compares the exact internal polynomial normalizer to
an untrusted Singular oracle over a deterministic sparse corpus. Disagreement
is a test failure; agreement does not grant graph authority.
