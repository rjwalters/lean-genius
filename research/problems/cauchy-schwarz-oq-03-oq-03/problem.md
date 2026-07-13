# Problem: Lp Interpolation Inequality (Log-Convexity of Lp Norms)

**Slug**: cauchy-schwarz-oq-03-oq-03
**Created**: 2026-07-01T08:49:18-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\|f\|_r \le \|f\|_p^{\theta}\,\|f\|_q^{1-\theta}, \qquad \frac{1}{r} = \frac{\theta}{p} + \frac{1-\theta}{q},\ \ \theta \in [0,1].
$$

### Plain Language

The map $s \mapsto \log \|f\|_{1/s}$ is convex: the $L^r$ norm at an interpolated exponent is controlled by a weighted geometric mean of the $L^p$ and $L^q$ norms. Equivalently, $L^p$ norms are log-convex in $1/p$.

### Why This Matters

Interpolation of $L^p$ norms is a workhorse of analysis (Riesz–Thorin, Marcinkiewicz interpolation, PDE estimates). It is the natural extension of the parent Hölder entry: Hölder gives the two-exponent product bound, and this interpolation inequality is its log-convexity refinement. Formalizing it strengthens the gallery's real-analysis coverage.

## Known Results

### What's Already Proven

- Hölder's inequality — parent entry `cauchy-schwarz-oq-03` (Hölder as Cauchy–Schwarz generalization).
- Mathlib `MeasureTheory` has `lintegral`/`eLpNorm` Hölder lemmas and `inner_le_nnorm_mul_nnorm`.
- Young's inequality for products (`Real.inner_le_nnorm`, `Real.add_pow_le_pow_mul_pow_of_sq_le_sq` style bounds).

### What's Still Open

- A packaged gallery statement/derivation of the three-exponent interpolation bound from Hölder.
- Handling the general measure-space `eLpNorm` version vs. the finite-sum (sequence) version.

### Our Goal

Derive the interpolation inequality from Hölder applied to the factorization $|f|^r = |f|^{r\theta}\cdot|f|^{r(1-\theta)}$ with conjugate exponents $\tfrac{p}{r\theta}$ and $\tfrac{q}{r(1-\theta)}$. Target the sequence/finite version first (aligns with the existing Cauchy–Schwarz bridge), then optionally the measure version.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cauchy-schwarz-oq-03 | Parent: Hölder inequality | conjugate exponents, Young |
| cauchy-schwarz | Base inner-product inequality | discriminant / sum of squares |
| cauchy-schwarz-integral | Integral form bridge | L² inner product |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Split `|f|^r = |f|^{rθ} · |f|^{r(1-θ)}` and apply Hölder with exponents `p/(rθ)` and `q/(r(1-θ))` (which are conjugate exactly when `1/r = θ/p + (1-θ)/q`).
   - Why it might work: reduces directly to the already-formalized Hölder inequality.
   - Risk: verifying the conjugacy `rθ/p + r(1-θ)/q = 1` and non-degenerate exponent side conditions.

2. **Approach B**: Prove log-convexity of `p ↦ log‖f‖_{1/p}` via Hölder on two points, then read off the interpolation bound.
   - Why it might work: conceptually clean; convexity packaging may already exist.
   - Risk: more scaffolding than the direct split.

### Key Difficulties

- Establishing the exponent conjugacy arithmetic over `ℝ≥0∞` / `ℝ`.
- Choosing the finite-sum vs. measure-theoretic setting to match Mathlib's most usable Hölder lemma.

### What Would a Proof Need?

- Key lemma 1: Hölder for the chosen setting (`inner_le_Lp_mul_Lq` / `eLpNorm` Hölder).
- Key lemma 2: exponent conjugacy `θ·r/p + (1-θ)·r/q = 1`.
- Technical requirements: `Real.rpow` manipulation, nonnegativity/side conditions.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The proof is a standard one-line-idea reduction to Hölder, already in the gallery.
- Mathlib's `rpow` and Hölder APIs supply the pieces.
- Main friction is exponent bookkeeping and the finite-vs-measure choice.

**Estimated Effort**:
- Exploration: 1 day
- If tractable: 3–5 days
- If hard: 1–2 weeks (full measure-space generality)

## References

### Papers
- Hardy, Littlewood, Pólya, *Inequalities* — interpolation of means.

### Online Resources
- https://en.wikipedia.org/wiki/Lp_space#Interpolation — statement and proof sketch.

### Mathlib
- `Mathlib.Analysis.MeanInequalities` / `Mathlib.Analysis.MeanInequalitiesPow` — Hölder, `rpow` inequalities, `inner_le_Lp_mul_Lq`.

## Metadata

```yaml
tags:
  - analysis
  - inequalities
  - Lp-spaces
related_proofs:
  - cauchy-schwarz-oq-03
  - cauchy-schwarz-integral
difficulty: medium
source: gallery-gap
created: 2026-07-01T08:49:18-07:00
```

**Significance**: 6/10
**Tractability**: 6/10
