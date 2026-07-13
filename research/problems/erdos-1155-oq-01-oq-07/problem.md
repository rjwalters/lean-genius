# Problem: Generalize triangle removal to K_r-removal process

## Statement

### Plain Language

Generalize the triangle removal process (Erdős #1155, BFL 2015) to K_r-cliques
for arbitrary r ≥ 3. The K_r-removal process starts with K_n, repeatedly removes
all edges of a uniformly random r-clique, and halts when the graph is K_r-free.
Let f_r(n) be the expected remaining edge count. The conjectured exponent is
2 - 2/(r+1): equals 3/2 for r=3 (BFL), 8/5 for r=4, 5/3 for r=5, and approaches
2 as r → ∞.

### Formal Statement

For r ≥ 3, define the K_r-removal process on K_n. Conjecture:

$$
f_r(n) \asymp n^{2 - 2/(r+1)}
$$

i.e., there exist constants 0 < c₁ ≤ c₂ such that
c₁·n^α ≤ f_r(n) ≤ c₂·n^α for all large n, where α = 2 - 2/(r+1).

## Classification

```yaml
tier: A
significance: 7
tractability: 5
tags:
  - erdos
  - graph-theory
  - random-graphs
  - generalization
  - seeker-selected
```

**Significance**: 7/10
**Tractability**: 5/10

## Why This Matters

1. Generalizes BFL (2015) f_3(n) = n^{3/2 + o(1)} to arbitrary r-cliques
2. Connects random combinatorial processes to Kruskal–Katona-type thresholds
3. Provides clean structural framework: exponent strictly monotone, bounded
4. Decomposes into modular subgoals (upper Θ, lower Θ, ratio convergence)

## Status

**Phase**: COMPLETED (framework only — main conjecture remains open for r ≥ 4)

The Lean formalization (`Proofs/Erdos1155OQ01OQ07.lean`, 356 lines, 3 axioms,
0 sorries, 21 theorems) builds the complete structural framework:
- Axiomatized `kCliqueRemovalEdges` with non-negativity and the C(n,2) bound
- Computable `kRemovalExponent r = 2 - 2/(r+1)` with verified values at r=3,4,5
- Strict monotonicity, bounds 1 ≤ α < 2, convergence α → 2 as r → ∞
- Generalized conjecture `kRemoval_conjecture` and `kRemoval_bfl_type` Props
- Equivalence: conjecture ↔ (upper Θ-bound ∧ lower Θ-bound)
- Limit characterization: f_r(n)/n^α → L > 0 implies the conjecture
- Implication: conjecture → BFL-type n^{α±ε} bound (technical centerpiece)

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| erdos-1155 | Parent: original triangle removal problem statement |
| erdos-1155-oq-01 | Parent OQ: r=3 triangle exact asymptotics (BFL 2015) |
| erdos-1155-oq-01-oq-01 | Sibling: ratio convergence f(n)/n^{3/2} → L for r=3 |
| erdos-1155-oq-01-oq-06 | Sibling: terminal Turán ratio f(n)/(n²/4) for r=3 |

## Open Future Directions

- Prove r = 4 case: f_4(n) ≍ n^{8/5} (analogous to BFL for r = 3)
- Connect K_r-removal rates to Ramsey multiplicity in dense graphs
- Investigate whether BFL second-moment / DE-method machinery generalizes
