# Census extension covers (HW61 G-5)

A sibling note to [M4-CENSUS-SEMANTICS.md](M4-CENSUS-SEMANTICS.md). It states what a held extension-cover claim means. Code: `census/GPCensus/ExtensionCheck.lean` (generator and checker, plain `Nat` lists, no Hex types) and `census/GPCensus/Extension.lean` (statement and soundness).

## The statement

An extension-cover claim is an ordinary census **NONE** claim at the single parameter `n + 1`. It needs no new statement kind. Its predicate is `Extension.extPred n t k F`, a first-order census formula built from three inputs:
- a base graph H on `n` vertices, given as graph6 and read into the adjacency table `t`;
- a degree `k`;
- a pattern list F, where each pattern has edges and optional *required non-edges*.

The formula holds of a graph G on `n + 1` vertices when G has distinct vertices `z 0, …, z n` such that:
- for `i ≠ j < n`, `z i ~ z j` exactly when `i ~ j` in H. So H is an induced copy on `z 0..z(n-1)`;
- `z n` has degree exactly `k`;
- G contains no pattern of F. A pattern is contained when some injective map of its vertices sends every pattern edge to an edge and every required non-edge to a non-edge.

**NONE of this formula on `n + 1` vertices** reads: every graph obtained from H by adding one vertex adjacent to exactly `k` of H's vertices contains a pattern of F. Containment is as a subgraph, not necessarily induced. Required non-edges are the one induced condition, and only on the named pairs.

Two uses:
- **Forbidden graphs** have no required non-edges. They need only heredity (L1, P3): a unit-distance embedding restricts to subgraphs.
- **TU gadgets** carry their distinguished pair as a required non-edge. A TU hit refutes G only at a proved maximum edge count (L2): if G with that pair added would beat a proved bound.

The statement says nothing about which inference turns a hit into "not unit-distance". That inference belongs to the spine rule (G-2) and its premises.

## The receipt (`extcover`)

The receipt carries H, `k`, F and one hit per neighbourhood. A hit is a neighbourhood, a pattern index and a vertex map.

**Coverage is by construction.** The checker iterates the Lean generator `combos n k` and compares each listed neighbourhood with the generated one. What is proved about the generator:
- it lists exactly the `k`-subsets (`mem_combos`), each once (`nodup_combos`), `binom n k` of them (`length_combos`, with `binom 21 4 = 5985` and `binom 21 5 = 20349` by `decide`);
- `combos_eq_flatMap` splits it into shards by largest element.

A receipt that omits or relabels a neighbourhood is refused.

**Patterns.** The certificate's base, `k` and patterns must reproduce the claim's formula exactly. A receipt built for a different pattern list is therefore refused. The runner script `tools/gp50_extcover.py run` also refuses a pattern file whose SHA-256 differs from its pin. That hash check is custody, not trusted checking.

**Soundness.** `Extension.extCover_sound` proves that an accepted hit list leaves no model of the formula. `Profile.reach_sound` carries this to `Holds` at `n + 1`, and `fold_held_meaning` carries it to every held claim. Standard axioms only.

## Reach

The receipt reaches the one parameter `n + 1`, for the one base H. Several things stay outside the claim:
- that H ranges over every relevant base (P6, P8: AMP Theorem 1(c), premise P7);
- that the patterns are non-unit-distance (P9);
- that a TU hit refutes (L2, P4).
