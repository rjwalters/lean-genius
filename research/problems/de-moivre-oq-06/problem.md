# Problem: Finite Geometric Sum of Complex Exponentials and the Lagrange Trigonometric Identity

**Slug**: de-moivre-oq-06
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: de-moivre

## Problem Statement

### Formal Statement

$$
\sum_{k=0}^{n-1} e^{ik\theta} = \frac{e^{in\theta}-1}{e^{i\theta}-1}
\quad(e^{i\theta}\neq 1),
\qquad
\sum_{k=0}^{n-1}\cos(k\theta) = \tfrac12 + \frac{\sin\!\big((n-\tfrac12)\theta\big)}{2\sin(\theta/2)}.
$$

### Plain Language

By De Moivre's theorem each term $(\cos\theta + i\sin\theta)^k = e^{ik\theta}$, so the
partial sums $\sum_{k=0}^{n-1} e^{ik\theta}$ form a **finite geometric series**. Summing it
in closed form and taking real/imaginary parts yields Lagrange's classical trigonometric
identities — the Dirichlet-kernel closed forms for $\sum\cos(k\theta)$ and
$\sum\sin(k\theta)$. This packages De Moivre's theorem with the finite geometric series to
expose the analytic engine behind Fourier partial sums.

### Why This Matters

No sibling addresses this: oq-05 ("roots of unity sum to zero") is the degenerate special
case $\theta = 2\pi/n$ where the numerator $e^{in\theta}-1$ vanishes. Mathlib has no
Dirichlet-kernel / Lagrange trig-identity result, so this is a genuine gap that composes
two verified gallery pieces (De Moivre + geometric series).

## Known Results

### What's Already Proven

- Parent `de-moivre` is verified (0-axiom).
- Mathlib has `geom_sum_eq`, `Complex.exp_nat_mul`, and `Complex.exp_ofReal_mul_I_re/_im`.

### What's Still Open

- The target theorems below (currently `sorry`).

### Our Goal

Prove the sketch below as a verified (0-axiom) child. Category: **composition /
specialization**.

## Target Lean Sketch

```lean
open Complex Real Finset

/-- Geometric sum of complex exponentials (De Moivre + geom_sum_eq). -/
theorem geom_sum_exp (θ : ℝ) (n : ℕ) (h : Complex.exp (θ * I) ≠ 1) :
    ∑ k ∈ range n, Complex.exp (k * θ * I)
      = (Complex.exp (n * θ * I) - 1) / (Complex.exp (θ * I) - 1) := by
  sorry -- exp(k*θ*I) = exp(θ*I)^k via Complex.exp_nat_mul, then geom_sum_eq

/-- Cosine partial sum as the real part of the closed form. -/
theorem sum_cos_eq_re (θ : ℝ) (n : ℕ) (h : Complex.exp (θ * I) ≠ 1) :
    ∑ k ∈ range n, Real.cos (k * θ)
      = ((Complex.exp (n * θ * I) - 1) / (Complex.exp (θ * I) - 1)).re := by
  sorry -- push .re through the finite sum; Complex.exp_ofReal_mul_I_re

/-- Lagrange / Dirichlet-kernel closed form (sin(θ/2) ≠ 0). -/
theorem lagrange_sum_cos (θ : ℝ) (n : ℕ) (h : Real.sin (θ/2) ≠ 0) :
    ∑ k ∈ range n, Real.cos (k * θ)
      = 1/2 + Real.sin ((n - 1/2) * θ) / (2 * Real.sin (θ/2)) := by
  sorry -- half-angle: multiply by e^{-iθ/2}, take real part, field_simp/ring
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `de-moivre` | Parent: De Moivre's theorem | complex exponentials |
| `de-moivre-oq-05` | Sibling: roots of unity sum to zero (degenerate case) | roots of unity |
| `geometric-series` | Provides the finite-sum engine | geometric series |

## Tractability Assessment

**Difficulty**: Medium

**Significance**: 6/10  |  **Tractability**: 7/10  |  **Tier**: B

**Justification**: Parts 1-2 are short mechanical compositions (De Moivre + `geom_sum_eq`,
push `.re` through the sum). The Lagrange capstone needs half-angle bookkeeping (rewrite
$e^{i\theta}-1 = e^{i\theta/2}(e^{i\theta/2}-e^{-i\theta/2})$) closed with `field_simp`/`ring`.

### Suggested First Steps

1. Prove `geom_sum_exp` via `Complex.exp_nat_mul` then `geom_sum_eq h n`.
2. Prove `sum_cos_eq_re` by pushing `.re` through `Finset.sum` and evaluating each term
   with `Complex.exp_ofReal_mul_I_re`.
3. Prove the Lagrange form by the half-angle multiplication and real-part extraction.

## References

### Mathlib

- `geom_sum_eq` — Algebra/Field/GeomSum.lean
- `Complex.exp_nat_mul` — Analysis/Complex/Exponential.lean
- `Complex.exp_mul_I`, `Complex.exp_ofReal_mul_I_re`, `Complex.exp_ofReal_mul_I_im` — Analysis/Complex/Trigonometric.lean

### Literature

- Lagrange's trigonometric identity; Dirichlet kernel in Fourier analysis.

## Metadata

```yaml
tags:
  - complex-analysis
  - trigonometry
  - de-moivre
  - fourier-analysis
  - geometric-series
related_proofs:
  - de-moivre
  - de-moivre-oq-05
  - geometric-series
difficulty: medium
source: proof-suggestion
created: 2026-07-01
```
