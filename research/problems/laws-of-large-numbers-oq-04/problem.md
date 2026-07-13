# Problem: Glivenko-Cantelli Theorem -- Uniform Convergence of Empirical Distributions

**Slug**: laws-of-large-numbers-oq-04
**Created**: 2026-03-30
**Status**: Active
**Source**: gallery-gap (open question from laws-of-large-numbers proof)

## Problem Statement

### Formal Statement

**Glivenko-Cantelli (1933)**: Let $X_1, X_2, \ldots$ be i.i.d. with CDF $F$. The empirical CDF $F_n(x) = \frac{1}{n}\sum_{i=1}^n \mathbf{1}_{X_i \leq x}$ satisfies:

$$\sup_{x \in \mathbb{R}} |F_n(x) - F(x)| \to 0 \quad \text{a.s.}$$

### Plain Language

The Law of Large Numbers says sample averages converge. Glivenko-Cantelli is the uniform version: the entire empirical distribution converges uniformly to the true CDF. Foundation of nonparametric statistics.

### Why This Matters

Foundation of Kolmogorov-Smirnov tests, bootstrap methods, and empirical process theory. Natural extension from point convergence (LLN) to uniform convergence.

## Known Results

### What's Already Proven

- `laws-of-large-numbers`: WLLN and SLLN (axiomatized, 1 axiom)
- Mathlib has measure theory and probability foundations

### Our Goal

Formalize the Glivenko-Cantelli theorem as a uniform strengthening of the SLLN.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| laws-of-large-numbers | Direct parent, axiomatized | WLLN, SLLN, measure theory |
| central-limit-theorem | Related convergence theorem | Characteristic functions |

## Suggested First Steps

1. Define empirical CDF in Lean using Mathlib's measure theory
2. State the theorem as uniform a.s. convergence
3. Consider DKW inequality approach as alternative proof strategy

## Metadata

```yaml
tags: [probability, convergence, measure-theory, statistics]
related_proofs: [laws-of-large-numbers, central-limit-theorem]
difficulty: medium-high
source: gallery-gap
created: 2026-03-30
```

**Significance**: 7/10
**Tractability**: 5/10
