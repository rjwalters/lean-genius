# Problem: Asymptotic decay $c_n \sim \sqrt{2/(\pi n)}$ for the Buffon hyperplane constant

**Slug**: buffons-needle-oq-01-oq-02-oq-02
**Created**: 2026-06-15
**Status**: Active
**Source**: proof-suggestion <!-- open question of gallery proof buffons-needle-oq-01-oq-02 -->

## Problem Statement

### Formal Statement

In the higher-dimensional Buffon problem (a convex body / needle dropped on a stationary
arrangement of parallel hyperplanes in $\mathbb{R}^n$), the proportionality constant $c_n$
relating expected crossings to mean width carries a dimension factor built from Gamma
functions, of the form
$$
c_n = \frac{\Gamma\!\left(\frac{n}{2}\right)}{\sqrt{\pi}\,\Gamma\!\left(\frac{n+1}{2}\right)}
\quad\text{(up to the parent proof's normalization).}
$$
The goal is to prove the asymptotic decay rate
$$
c_n \sim \sqrt{\frac{2}{\pi n}} \qquad (n \to \infty).
$$

### Plain Language

Buffon's needle generalizes to higher dimensions, where the chance of crossing a hyperplane
involves a constant that depends on the dimension through Gamma functions. As the dimension
grows, that constant shrinks. We want to prove it shrinks like $\sqrt{2/(\pi n)}$ — a clean
square-root decay — by applying Gamma-function asymptotics.

### Why This Matters

The asymptotic pins down the large-dimension behavior of the integral-geometry constant,
closing a stated open question of the parent proof. The proof exercises Mathlib's Gamma-ratio
asymptotics (`Real.Gamma_div_Gamma`-type estimates), a reusable tool for hypergeometric and
volume-of-ball constants.

## Known Results

### What's Already Proven

- The parent proof `buffons-needle-oq-01-oq-02` derives the higher-dimensional crossing
  constant via Cauchy–Crofton / mean-width and identifies its closed Gamma-function form.
- Mathlib has `Real.Gamma`, `Real.Gamma_add_one`, the Legendre duplication formula
  (`Real.Gamma_mul_Gamma_add_half` / `Real.Gamma_nat_eq_...`), and Stirling-type asymptotics
  for the factorial (`Stirling.factorial_isEquivalent`).

### What's Still Open

- The asymptotic equivalence $c_n \sim \sqrt{2/(\pi n)}$ itself, i.e. the limit
  $\sqrt{n}\,c_n \to \sqrt{2/\pi}$.
- A Lean form of the Gamma-ratio asymptotic
  $\Gamma(x)/\Gamma(x+\tfrac12) \sim x^{-1/2}$ as $x \to \infty$, specialized to $x = n/2$.

### Our Goal

Prove $\lim_{n\to\infty}\sqrt{n}\,c_n = \sqrt{2/\pi}$ (equivalently the `IsEquivalent`
statement), using the Gamma duplication formula and Stirling/Wallis asymptotics already in
Mathlib, after first confirming the parent proof's exact closed form for $c_n$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| buffons-needle-oq-01-oq-02 | Parent: higher-dim constant, closed form | Cauchy–Crofton, mean width |
| buffons-needle | Base geometric probability | integral geometry |
| stirling-formula | Gamma/factorial asymptotics | Stirling, Wallis |

## Initial Thoughts

### Potential Approaches

1. **Gamma-ratio via duplication + Stirling**: rewrite $c_n$ using the duplication formula,
   reduce to a ratio of factorials/central binomial, and apply `Stirling.factorial_isEquivalent`
   and the Wallis product to extract $\sqrt{2/(\pi n)}$.
   - Risk: assembling the `Asymptotics.IsEquivalent` chain through several rewrites.

2. **Direct $\log\Gamma$ asymptotic**: use the asymptotic expansion of $\log\Gamma$ to get
   $\log c_n = -\tfrac12\log n + \tfrac12\log(2/\pi) + o(1)$, then exponentiate.
   - Risk: Mathlib's `log Gamma` asymptotic coverage may be thinner than the factorial route.

### Key Difficulties

- Bridging $\Gamma(n/2)/\Gamma((n+1)/2)$ to factorial/central-binomial asymptotics for even
  and odd $n$ uniformly.
- Managing `IsEquivalent` / `Tendsto` plumbing through the duplication rewrite.

### What Would a Proof Need?

- Exact closed form of $c_n$ from the parent proof.
- Gamma duplication formula and Stirling/Wallis asymptotics (in Mathlib).
- A clean `IsEquivalent` or `Tendsto (sqrt n * c n) atTop (𝓝 (sqrt (2/π)))` target.

## Tractability Assessment

**Difficulty**: Medium–High

**Justification**:
- The closed form is known; the work is asymptotic analysis with Mathlib's Gamma/Stirling API.
- The main risk is `IsEquivalent` bookkeeping and even/odd uniformity, not a missing theorem.

**Estimated Effort**:
- Exploration: days
- If tractable: weeks

## References

### Papers
- Classical integral-geometry references (Santaló, *Integral Geometry and Geometric Probability*).

### Mathlib
- `Mathlib/Analysis/SpecialFunctions/Gamma/...` — `Real.Gamma`, duplication formula.
- `Mathlib/Analysis/SpecialFunctions/Stirling.lean` — factorial asymptotics; Wallis product.
- `Mathlib/Analysis/Asymptotics/...` — `IsEquivalent`.

## Metadata

```yaml
tags:
  - probability
  - geometric-probability
  - integral-geometry
  - asymptotics
  - gamma-function
related_proofs:
  - buffons-needle-oq-01-oq-02
  - buffons-needle
  - stirling-formula
difficulty: high
source: proof-suggestion
created: 2026-06-15
```

**Significance**: 5/10
**Tractability**: 4/10
