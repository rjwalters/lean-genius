# Problem: Erdős #1155 OQ2 — Limiting Distribution of f(n)/n^{3/2}

**Slug**: erdos-1155-oq-02
**Created**: 2026-04-23
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

Let $f(n)$ = number of edges removed in the triangle-removal process on $K_n$ (repeatedly remove all 3 edges of a random triangle until no triangles remain).

**Question (Erdős #1155 OQ2):** Does $f(n)/n^{3/2}$ converge in distribution as $n \to \infty$? To what limiting distribution?

### Plain Language

The triangle-removal process terminates in $\Theta(n^{3/2})$ steps, but the normalized count $f(n)/n^{3/2}$ — does it concentrate around a constant, or fluctuate with a non-trivial limit law?

### Why This Matters

An open question in probabilistic combinatorics. Formalizing a concentration result (variance bound, second-moment method) would be tractable and would advance Lean's probabilistic graph theory infrastructure.

## Known Results

### What's Already Proven
- $f(n) = \Theta(n^{3/2})$ — established and formalized in `erdos-1155`

### What's Still Open
- Exact constant: $f(n) \sim c \cdot n^{3/2}$?
- Limiting distribution of $f(n)/n^{3/2}$
- Logarithmic corrections

### Our Goal
Formalize a partial result: either a concentration inequality (variance bound), or a formal statement of the convergence question with proper probabilistic infrastructure in Lean 4.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `erdos-1155` | Parent: triangle-removal $\Theta(n^{3/2})$ bound |

## Initial Thoughts

### Potential Approaches

1. **Concentration via second-moment method**: Show $\text{Var}[f(n)/n^{3/2}] \to 0$, implying concentration around the mean.

2. **Formal infrastructure**: Define the random process formally in Lean (probability measure on triangle-removal sequences), state the distributional question without proving it.

3. **Martingale approach**: Show $f(n)/n^{3/2}$ is approximately a martingale and apply Azuma-Hoeffding.

### Key Difficulties
- Formalizing random processes on graphs in Lean 4 / Mathlib
- The probability space for the process is non-trivial to define

## Tractability Assessment

**Difficulty**: Challenging — open problem; only partial results are achievable

**Estimated Effort**:
- Concentration result formalization: 1-2 weeks
- Full distributional limit: open, not tractable

## Metadata

```yaml
tags:
  - erdos
  - combinatorics
  - graph-theory
  - probability
  - seeker-selected
related_proofs:
  - erdos-1155
difficulty: challenging
source: proof-suggestion
created: 2026-04-23
```

**Significance**: 6/10
**Tractability**: 5/10
