# Problem: Counting and Removal Lemma

**Slug**: szemeredi-counting
**Created**: 2026-03-21
**Status**: Active
**Source**: marquee-initiative
**Initiative**: Szemeredi Regularity and Applications (Phase 3)

## Problem Statement

### Formal Statement

**Counting Lemma:** Let $(V_1, V_2, V_3)$ be a triple of vertex sets in a graph $G$ with each pair $(V_i, V_j)$ being $\varepsilon$-regular with density $d_{ij}$. Then the number of triangles with one vertex in each $V_i$ satisfies:

$$
|\text{triangles}| = (1 \pm f(\varepsilon)) \cdot d_{12} d_{13} d_{23} \cdot |V_1| |V_2| |V_3|
$$

where $f(\varepsilon) \to 0$ as $\varepsilon \to 0$.

**Triangle Removal Lemma:** For every $\delta > 0$ there exists $\gamma > 0$ such that every graph on $n$ vertices with at most $\gamma n^3$ triangles can be made triangle-free by removing at most $\delta n^2$ edges.

### Plain Language

The Counting Lemma says that epsilon-regular pairs behave like random graphs for the purpose of counting subgraphs: the number of copies of a fixed graph (like a triangle) in regular triples is approximately what you would expect if edges were placed independently at random. The Triangle Removal Lemma, a powerful consequence, says that a graph with few triangles can be made triangle-free by removing few edges.

### Why This Matters

The Counting and Removal Lemmas are the key applications of the Regularity Lemma. The Triangle Removal Lemma implies Roth's theorem (encode 3-APs as triangles in a tripartite graph), giving a beautiful connection between graph theory and additive combinatorics. These results are the bridge between the structural Regularity Lemma and arithmetic applications.

## Dependencies

| Direction | Problem | Relationship |
|-----------|---------|-------------|
| **Depends on** | szemeredi-regularity | Uses regularity to count subgraphs |
| **Blocks** | szemeredi-full | Full theorem uses counting/removal |

## Known Results

### What's Already in Mathlib

- `SimpleGraph` triangle counting via `SimpleGraph.cliqueFree`
- `Finset.card` for counting
- Basic graph density operations

### What Needs to Be Built

- Counting lemma for regular triples (triangle count approximation)
- General graph counting lemma (arbitrary subgraphs in regular tuples)
- Triangle removal lemma from counting + regularity
- Graph removal lemma (general subgraph version)

### Our Goal

Formalize the triangle counting lemma for regular triples and derive the triangle removal lemma. The counting lemma is the technical core; the removal lemma follows by applying regularity and then counting.

## Initial Thoughts

### Potential Approaches

1. **Direct counting in regular triples**
   - Why it might work: Standard argument, follows directly from epsilon-regularity definition
   - Risk: Bookkeeping of error terms across three pairs

2. **Via embedding lemma first**
   - Why it might work: The embedding lemma is more general and implies counting
   - Risk: Additional generality adds complexity

3. **Hypergraph approach**
   - Why it might work: Unifies all subgraph counting results
   - Risk: Much harder, overkill for triangles

### Key Difficulties

- Error propagation through the counting argument
- Connecting triangle removal to arithmetic progressions
- Managing the epsilon parameters through multiple applications
- The removal lemma requires choosing gamma as a function of delta via regularity

## Tractability Assessment

**Difficulty**: Very Hard
**Tractability**: 4/10
**Significance**: 8/10

**Justification**:
- The counting lemma itself is not too hard given regularity infrastructure
- The removal lemma is an elegant but non-trivial application
- Depends entirely on having a working regularity lemma formalization
- High value as the key bridge between graph theory and additive combinatorics

**Estimated Effort**:
- Exploration: 2 days (after regularity is done)
- Implementation: 7-10 days

## References

### Papers
- Ruzsa & Szemeredi (1978) - "Triple systems with no six points carrying three triangles"
- Komlos & Simonovits (1996) - "Szemeredi's Regularity Lemma and its applications"
- Fox (2011) - "A new proof of the graph removal lemma"

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Basic`
- `Mathlib.Combinatorics.SimpleGraph.Clique`
- `Mathlib.Order.Partition.Finpartition`

## Metadata

```yaml
tags:
  - szemeredi
  - combinatorics
  - graph-theory
  - regularity
  - marquee-phase-3
related_proofs:
  - szemeredi-regularity
  - roth-theorem-k3
difficulty: very-hard
source: marquee-initiative
initiative: szemeredi-regularity-phase-3
created: 2026-03-21
```
