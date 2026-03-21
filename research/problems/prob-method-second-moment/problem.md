# Problem: Second Moment / Variance Method

**Slug**: prob-method-second-moment
**Created**: 2026-03-21
**Status**: Active
**Source**: marquee-initiative
**Initiative**: Probabilistic Method Library (Phase 1)

## Problem Statement

### Formal Statement

$$
\text{Chebyshev: } \Pr[|X - \mu| \geq t] \leq \frac{\text{Var}(X)}{t^2}
$$
$$
\text{Paley-Zygmund: } \Pr[X > 0] \geq \frac{\mathbb{E}[X]^2}{\mathbb{E}[X^2]}
$$

### Plain Language

The second moment method uses variance to prove that random variables are concentrated around their mean, or that they are positive with high probability. While the first moment method shows "something good exists," the second moment method shows "something good is typical."

### Why This Matters

Concentration inequalities are the workhorse of modern combinatorics and theoretical CS. The second moment method is the entry point to Chernoff bounds, martingale concentration, and threshold phenomena in random graphs.

## Dependencies

| Direction | Problem | Relationship |
|-----------|---------|-------------|
| **Depends on** | prob-method-expectation | Uses expectation framework |
| **Blocks** | prob-method-applications | Concentration for applications |

## Known Results

### What's Already in Mathlib

- `ProbabilityTheory.variance` — variance definition
- `ProbabilityTheory.meas_ge_le_mul_pow_variance` — Chebyshev-type bound

### What Needs to Be Built

- Paley-Zygmund inequality
- Second moment method for existence proofs
- Applications to random graph thresholds

## Tractability Assessment

**Difficulty**: Medium
**Tractability**: 7/10
**Significance**: 8/10

## References

### Papers
- Alon & Spencer - "The Probabilistic Method" Ch. 4

### Mathlib
- `Mathlib.Probability.Variance` — variance
- `Mathlib.Probability.Moments` — moments

## Metadata

```yaml
tags:
  - probabilistic-method
  - combinatorics
  - analysis
  - marquee-phase-1
difficulty: medium
source: marquee-initiative
initiative: probabilistic-method-library
created: 2026-03-21
```
