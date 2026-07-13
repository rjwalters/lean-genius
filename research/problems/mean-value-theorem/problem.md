# Problem: Vector-Valued Mean Value Theorem

**Slug**: mean-value-theorem
**Created**: 2026-03-06
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\|f(b) - f(a)\| \leq (b - a) \cdot \sup_{t \in (a,b)} \|f'(t)\|
$$

for $f : [a,b] \to E$ continuous on $[a,b]$, differentiable on $(a,b)$, where $E$ is a normed space.

### Plain Language

The classical MVT says f(b) - f(a) = f'(c)(b-a) for some c. For vector-valued functions, equality fails in general (e.g., f(t) = (cos t, sin t) on [0, 2pi]). Instead, we get a norm inequality: the displacement is bounded by the interval length times the supremum of the derivative norm.

### Why This Matters

The vector-valued MVT (mean value inequality) is a cornerstone of functional analysis. It yields Lipschitz estimates, uniqueness of ODEs (Picard), and is used throughout differential geometry and PDE theory.

## Known Results

### What's Already Proven

- Scalar MVT — `proofs/Proofs/MeanValueTheorem*.lean`
- Mathlib likely has `Convex.norm_image_sub_le_of_norm_deriv_le` or similar

### What's Still Open

- Explicit vector-valued formalization in our gallery
- Connection showing scalar MVT as corollary of vector-valued inequality

### Our Goal

Formalize the vector-valued MVT inequality, connect it to the scalar case, and demonstrate applications (e.g., Lipschitz bounds).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| mean-value-theorem | Source — scalar case | Rolle's theorem, continuity/differentiability |

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Well-known result, likely partially in Mathlib
- Scalar case exists to build on
- Standard proof via Hahn-Banach or direct integration

## Metadata

```yaml
tags:
  - analysis
  - functional-analysis
  - mean-value-theorem
  - normed-spaces
related_proofs:
  - mean-value-theorem
difficulty: medium
source: gallery-gap
created: 2026-03-06
```
