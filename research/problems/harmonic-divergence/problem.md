# Problem: Divergence Rate of sum 1/(n log n)

**Slug**: harmonic-divergence-oq-02
**Created**: 2026-03-30
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{Does } \sum_{n=2}^{N} \frac{1}{n \log n} \text{ have a closed-form asymptotic analogous to } H_N \sim \ln N \text{?}
$$

Known: $\sum_{n=2}^{N} \frac{1}{n \log n} \sim \log \log N$ by the integral test (Cauchy condensation). The goal is to formalize the precise asymptotic expansion with error terms.

### Plain Language

The harmonic series $\sum 1/n$ diverges like $\ln n$. The series $\sum 1/(n \log n)$ also diverges, but much more slowly — like $\log \log n$. We want to formalize this asymptotic relationship in Lean 4, proving that the partial sums grow as $\log \log N + C + O(1/\log N)$ for some constant $C$.

### Why This Matters

- Natural extension of the harmonic divergence proof already in the gallery
- Tests Lean's analysis library for iterated logarithm asymptotics
- Connects to the Mertens theorems (sum of 1/(p) ~ log log x over primes)

## Known Results

### What's Already Proven

- `harmonic-divergence` — Divergence of the harmonic series (verified, mathlib badge, 181 lines)
- Mathlib has `Real.tendsto_sum_range_one_div_nat_succ_atTop` for harmonic divergence
- Integral test / Cauchy condensation available in Mathlib

### What's Still Open

- Precise asymptotic with constant term for $\sum 1/(n \log n)$
- Connection to prime-counting asymptotics (Mertens' theorems)

### Our Goal

Formalize in Lean 4: $\sum_{n=2}^{N} \frac{1}{n \log n} = \log \log N + C + O(1/\log N)$ where $C$ is a computable constant, or at minimum prove $\sum_{n=2}^{N} \frac{1}{n \log n} - \log \log N$ converges.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| harmonic-divergence | Parent proof, divergence of $\sum 1/n$ | Partial sums, Mathlib analysis |
| basel-problem | Convergent series formalization | Series evaluation techniques |

## Initial Thoughts

### Potential Approaches

1. **Euler-Maclaurin summation**: Apply Euler-Maclaurin to $f(x) = 1/(x \log x)$
   - Why it might work: Standard technique for asymptotic expansions of sums
   - Risk: Euler-Maclaurin may not be in Mathlib yet

2. **Integral comparison**: Compare $\sum 1/(n \log n)$ with $\int_2^N dx/(x \log x) = \log \log N - \log \log 2$
   - Why it might work: Direct, elementary, only needs monotonicity
   - Risk: Getting the error term tight requires careful bounding

### Key Difficulties

- Mathlib's support for iterated logarithms and their asymptotics
- Bounding the difference between sum and integral precisely

### What Would a Proof Need?

- Key lemma: $\int_n^{n+1} \frac{dx}{x \log x} \leq \frac{1}{n \log n} \leq \int_{n-1}^{n} \frac{dx}{x \log x}$ for $n \geq 3$
- Antiderivative: $\int \frac{dx}{x \log x} = \log \log x + C$
- Telescoping to get the asymptotic

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Integral test approach is completely standard
- Mathlib has the prerequisite analysis infrastructure
- Parent proof (harmonic-divergence) provides a template

**Estimated Effort**:
- Exploration: 1-2 days
- If tractable: 3-5 days

## References

### Mathlib
- `Mathlib.Analysis.PSeries` — p-series convergence/divergence
- `Mathlib.Analysis.SpecificLimits.Basic` — specific limit results
- `Mathlib.MeasureTheory.Integral.IntervalIntegral` — integral comparison

## Metadata

```yaml
tags:
  - analysis
  - series
  - divergence
  - asymptotics
related_proofs:
  - harmonic-divergence
  - basel-problem
difficulty: medium
source: gallery-gap
created: 2026-03-30
```
