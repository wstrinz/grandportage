# Stacks applicability audit: JC-KRULL-INTERSECTION-AUDIT

- Theorem: [00IP](https://stacks.math.columbia.edu/tag/00IP)
- Pinned Stacks commit: `a04446e57ec1fbc252a871afcec7752fb2807b14`
- Statement SHA-256: `a14ec52c326702ac9e2d6340d5d95797be2073670f6c0e0642ae6f007e689caf`
- JC context: proposed source-cover intersection module for the JC H3 depth tower
- Intended conclusion: a persistent source-cover discrepancy class vanishes
- Decision: **REFUSED_MISSING_HYPOTHESES**
- Graph effect: **NONE**

## Exact pinned statement

```tex
Let $R$ be a Noetherian local ring. Let $I \subset R$ be
a proper ideal. Let $M$ be a finite $R$-module.
Then $\bigcap_{n \geq 0} I^nM = 0$.
```

## Hypothesis accounting

| Hypothesis | Exact premise | Status | GP binding / reason |
| --- | --- | --- | --- |
| `ring_noetherian_local` | $R$ is a Noetherian local ring | **MISSING** | The campaign does not yet bind the proposed coefficient ring as the relevant Noetherian local ring. |
| `ideal_proper` | $I \subset R$ is a proper ideal | **MISSING** | No exact GP claim identifies and proves proper the ideal defining the proposed adic filtration. |
| `module_finite` | $M$ is a finite $R$-module | **MISSING** | The source-cover discrepancy module has not been constructed or proved finite over that ring. |

## Application-specific bridge premises

These are needed to use the theorem in this JC context even though they are not hypotheses in the printed Stacks statement.

| Premise | Statement | Status | GP binding / reason |
| --- | --- | --- | --- |
| `class_in_every_power` | the discrepancy class lies in $I^nM$ for every $n \geq 0$ | **OPEN** | Finite-depth compatibility receipts do not yet form a theorem or checked family for every depth. |
| `class_identified` | the class whose vanishing is sought is an element of the declared module $M$ | **UNSUPPORTED** | The current exact-affine GP graph has no first-class module element or source-cover intersection object. |

## Authority boundary

This sidecar records discovery, source pinning, and premise accounting. It does not create or amend a GP claim, edge, inference, verdict, or kernel rule. Even `READY_FOR_GP_REVIEW` requires an explicit reviewed translation into the campaign graph.
