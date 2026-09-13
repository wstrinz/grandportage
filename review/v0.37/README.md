# v0.37.0: licence explanations and scalar division safety

Ships the merged read-only `gp explain` command, corpus intake, and Lean
family/partition and observation results, together with the nonconstant-divisor
repair. Raw variable division is refused before CAS execution; a denominator
guard does not turn polynomial quotient into rational evaluation.

Upgrade boundary: Singular adapter implementation 5 requires replay of older
CAS-backed receipts to regain authority. Verifier-native receipts are unchanged.
Graph format 8 and kernel epoch 12 are unchanged. No campaign corpus is published;
the three-campaign measurement remains BLOCKED-ON-CORPUS and no storage change
is inferred from it.

The implementation entering the release passed 1,748 non-live checks, all 63
native Singular checks and 39 Lean build jobs in both repositories. The release
PR reruns those gates; the published wheel is independently installed and checked.
