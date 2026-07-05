# Problem: Higher moments of the Eulerian descent statistic

**Slug**: geometric-series-oq-07-oq-01-oq-01-oq-01-oq-01-oq-01-oq-01
**Created**: 2026-07-01
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{For } D_n = \#\{\text{descents of a uniform } \sigma \in S_n\},\quad
\mathbb{E}[D_n] = \tfrac{n-1}{2},\ \operatorname{Var}(D_n) = \tfrac{n+1}{12},
$$
$$
\text{compute } \mathbb{E}\big[(D_n - \mathbb{E} D_n)^k\big] \text{ for } k \ge 3 \text{ and show } \frac{D_n - \mathbb{E} D_n}{\sqrt{\operatorname{Var} D_n}} \xRightarrow{d} \mathcal N(0,1).
$$

### Plain Language

The descent statistic on permutations is counted by the Eulerian numbers $\left\langle{n\atop k}\right\rangle$. The parent line already computed the mean and variance of the descent count via a "moment-transfer" recurrence engine. This problem pushes the same engine to the third and higher central moments, and then uses them to establish asymptotic normality of the standardized descent count.

### Why This Matters

Eulerian numbers and the descent distribution are a cornerstone of algebraic combinatorics. A machine-checked derivation of the full moment sequence — and the resulting CLT for descents — closes the distributional theory of this gallery line and connects it to the general theory of sums of independent indicator variables.

## Known Results

### What's Already Proven

- Mean $\mathbb{E}[D_n] = (n-1)/2$ (parent entry).
- Variance $\operatorname{Var}(D_n) = (n+1)/12$ (parent entry).
- The moment-transfer recurrence relating $\sum_k \left\langle{n\atop k}\right\rangle k^m$ across $m$ (parent entry).

### What's Still Open

- Closed forms for the third and fourth central moments.
- Asymptotic normality of the standardized descent count.

### Our Goal

Derive the third central moment (expected $0$ by the symmetry $\left\langle{n\atop k}\right\rangle = \left\langle{n\atop n-1-k}\right\rangle$) and the fourth central moment, then either invoke a Lindeberg/Lyapunov CLT via the representation of $D_n$ as a sum of dependent-but-controllable indicators, or a moment-convergence argument matching the Gaussian moments.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| geometric-series descent line (parent) | moment-transfer engine | generating functions, recurrence |
| composition-parts-choose moment ladder | analogous higher-moment computation | symmetry involution, moment ladder |

## Initial Thoughts

### Potential Approaches

1. **Moment ladder**: extend the parent recurrence to $\mathbb{E}[D_n^3], \mathbb{E}[D_n^4]$, then convert to central moments.
   - Why it might work: the engine is already built; only more rungs are needed.
   - Risk: algebra grows; need `Finset.sum` manipulation discipline.

2. **Symmetry shortcut**: the descent distribution is symmetric about $(n-1)/2$, so all odd central moments vanish; only even moments need work.
   - Why it might work: kills the third moment in one line (matches the composition-parts skewness pattern).
   - Risk: proving the exact Eulerian symmetry in Lean.

### Key Difficulties

- Turning raw moments into central moments cleanly.
- The CLT step: choosing between an indicator-sum Lindeberg argument and moment convergence.

### What Would a Proof Need?

- Key lemma 1: Eulerian symmetry $\left\langle{n\atop k}\right\rangle = \left\langle{n\atop n-1-k}\right\rangle$.
- Key lemma 2: third and fourth raw moments from the recurrence.
- Technical requirements: `Finset.sum`, `Nat.choose`/Eulerian API, possibly `ProbabilityTheory` CLT lemmas.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The moment computation reuses an existing engine; the odd-moment vanishing is a symmetry corollary (mirrors composition-parts skewness = 0 already shipped).
- The CLT half is genuinely harder in Lean and may be scoped out to a follow-up.
- Mathlib has `ProbabilityTheory.centralMoment` and CLT infrastructure.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable (moments only): 3–5 days
- If hard (full CLT): unknown

## References

### Papers
- Carlitz, Eulerian numbers and polynomials (1959).
- Bona, Combinatorics of Permutations, Ch. on descents.

### Online Resources
- https://en.wikipedia.org/wiki/Eulerian_number — moments of the descent statistic.

### Mathlib
- `Mathlib.Probability.Moments` — central moments.
- `Mathlib.Probability.CLT` (if available) — central limit theorem.

## Metadata

```yaml
tags:
  - combinatorics
  - eulerian-numbers
  - descent-statistic
  - moments
  - recurrence
related_proofs:
  - composition-parts-choose
  - geometric-series
difficulty: medium
source: gallery-gap
created: 2026-07-01
```

**Significance**: 5/10
**Tractability**: 6/10
