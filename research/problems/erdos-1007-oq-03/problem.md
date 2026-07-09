# Problem: Computational Complexity of Determining Graph Dimension

**Slug**: erdos-1007-oq-03
**Created**: 2026-07-09T15:40:16-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{Is } \mathrm{DIM}(G, d) := \bigl[\, \dim(G) \le d \,\bigr] \in \mathsf{NP\text{-}hard}\ ?
\qquad \dim(G) = \min\{\, d : \exists f\colon V \to \mathbb{R}^d,\ \|f(u)-f(v)\|_2 = 1\ \forall\, uv \in E \,\}
$$

### Plain Language

The dimension of a graph $G$ is the smallest Euclidean dimension $d$ in which $G$ can be drawn so that every edge is exactly a unit-length segment. This problem asks whether deciding "is $\dim(G) \le d$?" (equivalently, computing $\dim(G)$) is computationally intractable — specifically whether it is NP-hard. Deciding embeddability amounts to asking whether a system of quadratic equations $\|f(u)-f(v)\|^2 = 1$, one per edge, has a real solution, which places the problem in the realm of the existential theory of the reals.

### Why This Matters

Erdős, Harary, and Tutte introduced graph dimension in 1965, and the exact extremal values (e.g. minimum edges for dimension 4 being 9, uniquely $K_{3,3}$) were settled only recently by House (2013) and Chaffee–Noble (2016). Those results describe *what* the extremal graphs look like, but say nothing about *how hard it is to compute* the dimension of an arbitrary input graph. Establishing NP-hardness (or worse, $\exists\mathbb{R}$-hardness) would explain why closed-form extremal answers are so difficult to obtain in general, and would connect graph dimension to the well-studied complexity of geometric realizability problems such as unit-distance representability and graph rigidity.

## Known Results

### What's Already Proven

- $\dim(K_{n+1}) = n$ via regular simplex embeddings, and the extremal values $e(1)=1, e(2)=3, e(3)=6, e(4)=9, e(5)=15$ — Erdős–Harary–Tutte (1965), House (2013), Chaffee–Noble (2016).
- The related decision problem "unit-distance graph in $\mathbb{R}^2$" and many geometric realizability questions are $\exists\mathbb{R}$-complete (hence NP-hard) — Schaefer, *Complexity of Some Geometric and Topological Problems* (2009).
- Graph rigidity and Euclidean distance matrix completion problems, close cousins of dimension computation, have known hardness results (Saxe, 1979, on embeddability of weighted graphs in $\mathbb{R}^d$).

### What's Still Open

- Whether the specific decision problem $\dim(G) \le d$ is NP-hard, and whether it lies in NP at all (membership is unclear because certificates may require irrational, high-precision coordinates).
- The exact complexity class: is it NP-complete, $\exists\mathbb{R}$-complete, or something between, and does hardness hold for fixed $d$ versus $d$ part of the input?

### Our Goal

Formalize in Lean 4 the framework needed to state the NP-hardness question precisely: a decision-problem encoding of graph dimension, the reduction target (feasibility of the quadratic unit-distance system), and a skeleton reduction from a known NP-hard problem. The concrete deliverable is a rigorous statement of `graphDimensionDecision` and its relationship to real-solvability of the edge-distance equation system, leaving the hardness reduction itself as the open theorem.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1007 | Parent problem: defines graph dimension and unit-distance embeddings; this OQ studies the complexity of computing that dimension | Unit-distance embedding structure, `graphDimension` via `Nat.find`, axiomatized extremal bounds |
| erdos-135 | Both connect graph combinatorics to Euclidean distance geometry; distinct-distance counting shares the algebraic-distance-system flavor | Distance geometry, extremal counting |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Reduce from a known NP-hard geometric problem (e.g. unit-distance graph recognition or Euclidean embeddability of a weighted graph).
   - Why it might work: Schaefer's $\exists\mathbb{R}$-completeness results already handle unit-distance realizability; adapting the gadget graphs to force a *specific* dimension could transfer hardness.
   - Risk: Forcing an exact dimension (not just $\le d$ realizability) requires rigidity gadgets that pin the embedding, which are delicate to construct and formalize.

2. **Approach B**: Cast the decision problem inside the existential theory of the reals and argue $\exists\mathbb{R}$-hardness directly.
   - Why it might work: The edge equations $\|f(u)-f(v)\|^2 = 1$ are literally polynomial constraints, so the problem is natively an $\exists\mathbb{R}$ instance.
   - Risk: Establishing hardness (not just membership) still needs a reduction; and $\exists\mathbb{R}$ machinery is not formalized in Mathlib.

### Key Difficulties

- NP membership is genuinely unclear: an optimal embedding may require coordinates that are algebraic numbers of high degree, so a polynomial-size certificate is not obvious.
- Distinguishing "embeddable in $\le d$" from "dimension exactly $d$" requires ruling out lower-dimensional embeddings, a universally quantified (co-NP-flavored) condition.

### What Would a Proof Need?

- Key lemma 1: A faithful encoding of `graphDimensionDecision (G, d)` as feasibility of a finite polynomial system over $\mathbb{R}$.
- Key lemma 2: A gadget construction that forces any unit-distance embedding of a target graph to realize a prescribed dimension.
- Technical requirements: A Lean model of decision problems / reductions, plus a formal statement of an $\exists\mathbb{R}$- or NP-complete source problem to reduce from.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- Full NP-hardness (or $\exists\mathbb{R}$-hardness) proofs for geometric realizability are research-level and rely on intricate gadget constructions not present in Mathlib.
- Similar problems (unit-distance recognition, weighted-graph embeddability) are known hard, giving a plausible route, but the reductions are nontrivial to formalize.
- Mathlib has real-analysis and Euclidean-space infrastructure but no complexity-theory (NP, reductions, $\exists\mathbb{R}$) framework, so much scaffolding must be built.

**Estimated Effort**:
- Exploration: 1–2 days to survey complexity encodings and rigidity gadgets.
- If tractable: 2–4 weeks to formalize the decision-problem framework and a skeleton reduction.
- If hard: unknown — a complete formal NP-hardness proof may be a multi-month effort.

## References

### Papers
- Erdős, P.; Harary, F.; Tutte, W. T., "On the dimension of a graph", *Mathematika* 12 (1965) — foundational definition of graph dimension.
- House, R. L., "A 4-dimensional graph has at least 9 edges", *Discrete Mathematics* 313 (2013) — extremal result for dimension 4.
- Schaefer, M., "Complexity of Some Geometric and Topological Problems", *Graph Drawing* (2009) — $\exists\mathbb{R}$-completeness of geometric realizability, including unit-distance representations.
- Saxe, J. B., "Embeddability of weighted graphs in $k$-space is strongly NP-hard", *Proc. Allerton Conf.* (1979) — hardness of Euclidean embeddability of weighted graphs.

### Online Resources
- https://erdosproblems.com/1007 — Erdős Problem #1007 statement and status.
- https://en.wikipedia.org/wiki/Existential_theory_of_the_reals — background on the $\exists\mathbb{R}$ complexity class relevant to distance-system feasibility.

### Mathlib
- `Mathlib.Analysis.InnerProductSpace.EuclideanDist` — Euclidean distance in $\mathbb{R}^n$, needed to state unit-distance constraints.
- `Mathlib.Combinatorics.SimpleGraph.Basic` — simple graph structure for encoding input instances.

## Metadata

```yaml
tags:
  - erdos
  - graph-theory
  - geometry
  - dimension
  - unit-distance
  - embedding
  - complexity
related_proofs:
  - erdos-1007
  - erdos-135
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:40:16-07:00
```
