# Problem: Dirichlet Conditions for Fourier Pointwise Convergence

**Slug**: fourier-series-oq-03
**Created**: 2026-03-06
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
f \in BV[-\pi, \pi] \implies S_N f(x) \to \frac{f(x^+) + f(x^-)}{2} \text{ as } N \to \infty
$$

where $S_N f(x) = \sum_{n=-N}^{N} \hat{f}(n) e^{inx}$ is the N-th partial Fourier sum.

### Plain Language

If a periodic function has bounded variation (its total oscillation is finite), then its Fourier series converges at every point to the average of the left and right limits. Formalize this using Mathlib's piecewise-smooth framework.

### Why This Matters

The Dirichlet convergence theorem is the cornerstone of Fourier analysis. It bridges the gap between L² convergence (Parseval, already in Mathlib) and pointwise convergence, which is what engineers and physicists use in practice.

## Known Results

### What's Already Proven

- Fourier series basics — `fourier-series` (gallery proof)
- Mathlib has `MeasureTheory.Lp`, Fourier transform on `ℝ` and `AddCircle`
- Parseval's theorem exists in Mathlib

### What's Still Open

- Pointwise convergence under Dirichlet conditions
- Riemann-Lebesgue lemma formalization
- Dirichlet kernel analysis

### Our Goal

Prove pointwise convergence of Fourier series for BV functions using Mathlib's measure theory and analysis infrastructure.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| fourier-series | Base Fourier theory | L² theory, coefficients |

## Initial Thoughts

### Potential Approaches

1. **Via Dirichlet kernel**: Analyze D_N(x) = sin((2N+1)x/2)/(2sin(x/2)), show it's an approximate identity under BV
   - Why it might work: Classical and well-documented approach
   - Risk: Requires careful analysis of oscillatory integrals

2. **Via Fejér kernel first**: Prove Cesàro convergence (Fejér), then upgrade to pointwise for BV
   - Why it might work: Fejér kernel is positive, easier to handle
   - Risk: Extra step, though Fejér may already be in Mathlib

### Key Difficulties

- BoundedVariation may need definition or extension in Mathlib
- Dirichlet kernel singularity analysis
- Handling left/right limits at discontinuities

### What Would a Proof Need?

- Key lemma 1: Riemann-Lebesgue lemma (∫f·sin(nt)→0)
- Key lemma 2: Dirichlet kernel reproduces partial sums
- Key lemma 3: Jordan's test — BV functions have convergent Fourier series
- Technical requirements: BV function space, one-sided limits

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Classical result with well-known proofs
- Mathlib has strong measure theory and integration
- Main question is what BV/piecewise infrastructure exists

## References

### Mathlib
- `Analysis.Fourier.AddCircle` — Fourier coefficients on the circle
- `MeasureTheory.Function.LpSpace` — Lp spaces
- `Analysis.BoundedVariation` — if it exists

## Metadata

```yaml
tags:
  - analysis
  - harmonic-analysis
  - fourier-series
  - convergence
  - bounded-variation
related_proofs:
  - fourier-series
difficulty: medium
source: gallery-gap
created: 2026-03-06
```

**Significance**: 7/10
**Tractability**: 6/10
