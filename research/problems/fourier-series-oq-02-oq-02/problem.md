# Problem: Fourier Coefficient Decay — fourierCoeff_sq_summable_of_holder via p-Series

**Slug**: fourier-series-oq-02-oq-02
**Created**: 2026-04-23T11:40:52+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
f \in C^\alpha(\mathbb{T}),\ \alpha > \tfrac{1}{2} \implies \sum_{n \neq 0} |\hat{f}(n)|^2 < \infty
$$

Prove `fourierCoeff_sq_summable_of_holder` in Lean 4: Hölder continuous functions with exponent $\alpha > 1/2$ have square-summable Fourier coefficients, using Mathlib's p-series convergence.

### Plain Language

Hölder continuous functions have Fourier coefficients decaying like $|n|^{-\alpha}$. When $\alpha > 1/2$, the series of squared coefficients converges (since $\sum |n|^{-2\alpha}$ is a convergent p-series with exponent $2\alpha > 1$).

The `fourier-series-oq-02` gallery entry establishes the coefficient decay bound but leaves the squared summability open, pending connection to Mathlib's p-series API.

### Why This Matters

Closes a concrete sorry in the gallery by connecting Hölder decay bounds to Mathlib's summability infrastructure. Provides a reusable result for harmonic analysis work and demonstrates the Mathlib p-series API in practice.

## Known Results

### What's Already Proven

- `fourier-series-oq-02`: $|\hat{f}(n)| \leq C |n|^{-\alpha}$ for Hölder-$\alpha$ functions (possibly with sorries)
- Mathlib: `Real.summable_pow_div_add` or similar, Parseval's theorem for $L^2$

### What's Still Open

- Connecting the Hölder decay bound to p-series convergence in Lean 4
- Completing `fourierCoeff_sq_summable_of_holder`

### Our Goal

Prove the squared summability via:
1. Decay bound: $|\hat{f}(n)| \leq C \cdot |n|^{-\alpha}$
2. p-series: $\sum n^{-2\alpha}$ converges for $2\alpha > 1$
3. Comparison: $\sum |\hat{f}(n)|^2 \leq C^2 \sum n^{-2\alpha} < \infty$

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `fourier-series-oq-02` | Parent proof with Hölder decay | Fourier analysis, Hölder continuity |
| `fourier-series` | Base gallery entry | Fourier series basics |

## Initial Thoughts

### Potential Approaches

1. **Comparison with p-series**: Use `Summable.of_nonneg_of_le` to bound the squared series by a convergent p-series.
   - Why it might work: Standard comparison lemma exists in Mathlib
   - Risk: May need to handle $n=0$ separately; integer vs natural index

2. **Direct Mathlib API**: Find `summable_one_div_pow` or `Real.summable_pow_div` with the right signature.
   - Why it might work: Mathlib has extensive summability theory
   - Risk: Multiple summability formulations to navigate

### Key Difficulties

- Finding the exact Mathlib p-series lemma with the right type signature
- Checking if `fourier-series-oq-02` decay bound itself has sorries that block this
- Summing over $\mathbb{Z}$ vs $\mathbb{N}$ (Fourier series uses integer indices)

### What Would a Proof Need?

- Key lemma 1: `|fourierCoeff f n| ≤ C * ‖(n : ℤ)‖^(-α)` from the gallery
- Key lemma 2: `Summable (fun n : ℤ => ‖(n : ℝ)‖^(-2*α))` for `α > 1/2`
- Technical: `Summable.of_nonneg_of_le` or `summable_of_summable_norm`

## Tractability Assessment

**Difficulty**: Medium-Low

**Justification**:
- Mathematically a straightforward comparison test
- Mathlib has extensive summability theory for this
- Main challenge: API discovery and index type matching
- No new mathematics needed — clean Lean 4 formalization

**Estimated Effort**:
- Exploration: 1-2 days (check gallery proof state, find Mathlib APIs)
- If tractable: 2-3 days (formalize comparison chain)

## References

### Papers
- Zygmund, A. (1959), "Trigonometric Series", Vol. I — Hölder continuity and Fourier decay

### Mathlib
- `Mathlib.Analysis.Fourier.FourierTransform` — Fourier coefficient definitions
- `Mathlib.Topology.Algebra.InfiniteSum.Basic` — summability
- `Mathlib.Analysis.SpecificLimits.Basic` — p-series convergence

## Metadata

```yaml
tags:
  - analysis
  - fourier-series
  - holder-continuity
  - harmonic-analysis
  - summability
  - p-series
related_proofs:
  - fourier-series
  - fourier-series-oq-02
difficulty: medium-low
source: gallery-gap
created: 2026-04-23T11:40:52+02:00
```

**Significance**: 6/10
**Tractability**: 6/10
