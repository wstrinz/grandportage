# Stacks applicability audit: JC-DEPTH7-LCI-COTANGENT-AUDIT

- Theorem: [08SL](https://stacks.math.columbia.edu/tag/08SL)
- Pinned Stacks commit: `a04446e57ec1fbc252a871afcec7752fb2807b14`
- Statement SHA-256: `a94d2424b7be238fbb19602528f65e3f10ad331e0be37e17e172bb1a854cae5f`
- JC context: proposed reduced depth-7 source-boundary presentation
- Intended conclusion: the relevant cotangent complex is perfect with tor amplitude in $[-1,0]$
- Decision: **REFUSED_MISSING_HYPOTHESES**
- Graph effect: **NONE**

## Exact pinned statement

```tex
Let $A \to B$ be a local complete intersection map.
Then $L_{B/A}$ is a perfect complex with tor amplitude in $[-1, 0]$.
```

## Hypothesis accounting

| Hypothesis | Exact premise | Status | GP binding / reason |
| --- | --- | --- | --- |
| `map_lci` | $A \to B$ is a local complete intersection map | **MISSING** | The current depth-7 computation has not yet produced a checked lci claim for the selected map. |

## Application-specific bridge premises

These are needed to use the theorem in this JC context even though they are not hypotheses in the printed Stacks statement.

| Premise | Statement | Status | GP binding / reason |
| --- | --- | --- | --- |
| `presentation_identified` | the selected map $A \to B$ exactly represents the reduced JC source-boundary problem | **OPEN** | Depth-7 extraction is still running and the source-to-boundary presentation is not frozen. |
| `obstruction_problem_identified` | the proposed deformation or obstruction question is governed by $L_{B/A}$ | **MISSING** | Tag 08SL supplies amplitude after lci; it does not itself identify or annihilate a JC obstruction class. |

## Authority boundary

This sidecar records discovery, source pinning, and premise accounting. It does not create or amend a GP claim, edge, inference, verdict, or kernel rule. Even `READY_FOR_GP_REVIEW` requires an explicit reviewed translation into the campaign graph.
