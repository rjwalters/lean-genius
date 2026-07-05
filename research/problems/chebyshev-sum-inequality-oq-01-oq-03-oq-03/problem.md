# Problem: Covariance corollary Cov(f(X),g(X)) ≥ 0 for monotone f, g

**Slug**: chebyshev-sum-inequality-oq-01-oq-03-oq-03
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

Let $X$ be uniform on $[a,b]$ and let $f, g : [a,b] \to \mathbb{R}$ be both monotone in the same direction (both nondecreasing or both nonincreasing). Then

$$
\operatorname{Cov}(f(X), g(X)) = \mathbb{E}[f(X)g(X)] - \mathbb{E}[f(X)]\,\mathbb{E}[g(X)] \ge 0,
$$

equivalently the continuous Chebyshev integral inequality
$$
\frac{1}{b-a}\int_a^b f\,g\,dx \;\ge\; \left(\frac{1}{b-a}\int_a^b f\,dx\right)\left(\frac{1}{b-a}\int_a^b g\,dx\right).
$$

### Plain Language

Similarly-ordered functions are positively correlated: if $f$ and $g$ both increase, then a uniformly random point makes $f(X)$ and $g(X)$ move together, so their covariance is nonnegative. This is the probabilistic face of the Chebyshev sum/integral inequality proved in the parent.

### Why This Matters

This is the simplest, cleanest instance of the FKG-type "positive correlation of monotone observables." Formalizing it bridges the parent's Chebyshev inequality to a probability-theory statement and sets up the connection to the FKG inequality.

## Known Results

### What's Already Proven

- The Chebyshev sum/integral inequality — parent proof `chebyshev-sum-inequality-oq-01-oq-03` (verified).
- Mathlib probability infrastructure: `ProbabilityTheory.variance`, `covariance`, uniform measure on an interval, `MeasureTheory.integral` over `Icc`.

### What's Still Open

- The explicit covariance-form corollary in this repository.
- The precise link statement to the FKG inequality (the FKG connection may be recorded as a remark rather than fully formalized).

### Our Goal

Derive $\operatorname{Cov}(f(X), g(X)) \ge 0$ for similarly-ordered monotone $f, g$ and $X$ uniform on $[a,b]$, directly from the parent's Chebyshev integral inequality, and state (at minimum) how it specialises the FKG inequality on the totally-ordered lattice $[a,b]$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| chebyshev-sum-inequality-oq-01-oq-03 | Parent: verified Chebyshev integral inequality | rearrangement, integral bounds |
| chebyshev-sum-inequality-oq-01 | Discrete Chebyshev sum inequality and setup | sorted-sequence pairing |

## Initial Thoughts

### Potential Approaches

1. **Reduce to the parent integral inequality**: Expand $\operatorname{Cov}$ as $\mathbb{E}[fg] - \mathbb{E}[f]\mathbb{E}[g]$ and identify it with the difference in the parent's inequality, scaled by $1/(b-a)$.
   - Why it might work: the covariance form is algebraically identical to the parent's statement after normalizing the measure.
   - Risk: matching Mathlib's `covariance`/`integral` API to the parent's formulation.

2. **Direct via the "two independent copies" identity**: $2\operatorname{Cov}(f(X),g(X)) = \mathbb{E}[(f(X)-f(Y))(g(X)-g(Y))]$ for i.i.d. $X,Y$, and the integrand is $\ge 0$ by comonotonicity.
   - Why it might work: conceptually clean, `≥ 0` pointwise then integrate.
   - Risk: setting up the product measure / independent copy in Mathlib.

### Key Difficulties

- Selecting the right Mathlib formalization of "uniform on $[a,b]$" and its `covariance`.
- Integrability side conditions (monotone functions on a compact interval are integrable — available but must be invoked).

### What Would a Proof Need?

- Key lemma 1: parent Chebyshev integral inequality in a form matching $\int fg \ge \frac{1}{b-a}\int f \int g$.
- Key lemma 2: covariance = $\mathbb{E}[fg] - \mathbb{E}[f]\mathbb{E}[g]$ for the uniform measure.
- Technical requirements: integrability of monotone $f,g$ on `Icc a b`, measure normalization.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The core inequality is already verified; this is largely a restatement in probability language.
- Main cost is Mathlib API plumbing (`covariance`, uniform measure), not new mathematics.
- The "two independent copies" identity is a well-trodden Mathlib-friendly route if the direct reduction is fiddly.

**Estimated Effort**:
- Exploration: hours
- If tractable: 2–4 days

## References

### Papers
- Hardy, Littlewood, Pólya, *Inequalities*, §2.17 — Chebyshev's inequality.
- Fortuin, Kasteleyn, Ginibre (1971) — the FKG inequality.

### Online Resources
- Wikipedia: "Chebyshev's sum inequality" and "FKG inequality".

### Mathlib
- `Mathlib.Probability.Variance` / `covariance` — covariance definition.
- `MeasureTheory.integral`, uniform measure on `Icc` — expectation setup.

## Metadata

```yaml
tags:
  - inequalities
  - probability
  - covariance
  - fkg
related_proofs:
  - chebyshev-sum-inequality-oq-01-oq-03
  - chebyshev-sum-inequality-oq-01
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 5/10
**Tractability**: 7/10
