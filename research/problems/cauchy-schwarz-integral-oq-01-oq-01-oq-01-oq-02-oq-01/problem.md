# Problem: Power Mean Chain Inequality (n-variable)

**Slug**: cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02-oq-01
**Created**: 2026-04-04T00:00:00Z
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{For positive reals } x_1, \ldots, x_n \text{ and exponents } p_1 \leq p_2 \leq \cdots \leq p_k,
$$
$$
M_{p_1}(x_1,\ldots,x_n) \leq M_{p_2}(x_1,\ldots,x_n) \leq \cdots \leq M_{p_k}(x_1,\ldots,x_n)
$$
where $M_p(x_1,\ldots,x_n) = \left(\frac{x_1^p + \cdots + x_n^p}{n}\right)^{1/p}$ for $p \neq 0$, with $M_0 = $ geometric mean.

### Plain Language

The power mean $M_p$ of $n$ positive reals is non-decreasing in the exponent $p$. This generalizes the classical chain min ≤ HM ≤ GM ≤ AM ≤ QM ≤ max to arbitrary exponents and arbitrary number of variables.

### Why This Matters

The parent proof `cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02` proved this chain for **two** positive reals (n=2) and five specific means (HM, GM, AM, QM). This extension to **n variables** and **arbitrary exponents** closes an important gap in the gallery's inequality theory and connects to Jensen's inequality for convex functions.

## Known Results

### What's Already Proven (in this gallery)

- `cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02`: min ≤ HM ≤ GM ≤ AM ≤ QM ≤ max for n=2
- `cauchy-schwarz-integral-oq-01-oq-01-oq-01`: AM-GM inequality for n variables
- `cauchy-schwarz-integral`: Cauchy-Schwarz integral form

### What's Still Open

- Full n-variable power mean monotonicity in p for general exponents
- Equality conditions: M_p = M_q iff all x_i are equal
- Limiting cases: M_0 = GM, M_{-∞} = min, M_{+∞} = max

### Our Goal

Formalize M_p(x_1,...,x_n) ≤ M_q(x_1,...,x_n) for p ≤ q in Lean 4, for arbitrary n and positive reals. Start with a key special case (e.g., AM ≥ GM for n variables, or M_1 ≥ M_{1/2}) and build up.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02 | Direct parent: 2-variable chain | nlinarith, sqrt_monotone |
| cauchy-schwarz-integral-oq-01-oq-01-oq-01 | AM-GM n-variable | Finset.prod, induction |
| cauchy-schwarz-integral | Integral Cauchy-Schwarz | MeasureTheory |

## Initial Thoughts

### Potential Approaches

1. **Jensen's Inequality Route**: M_p ≤ M_q iff φ(M_p) ≤ M_q where φ(t) = t^{q/p} is convex for q > p > 0. Use `ConvexOn` from Mathlib.
   - Why it might work: Mathlib has Jensen's inequality for finite sums
   - Risk: Need to handle p=0 (GM) as a limiting case separately

2. **Direct Algebraic Approach**: For specific pairs (p,q), expand and apply AM-GM or Cauchy-Schwarz directly.
   - Why it might work: Works for small n or specific exponent pairs
   - Risk: Does not generalize easily

3. **Hölder's Inequality Route**: M_p ≤ M_q follows from Hölder with exponents q/p and q/(q-p).
   - Why it might work: Mathlib has Hölder's inequality
   - Risk: Need careful formulation for discrete sums

### Key Difficulties

- Defining M_p cleanly in Lean for all real p, including p=0 limit
- Handling the general n-variable case (Finset summation)
- Convexity arguments need `ConvexOn` and Jensen for finite sums

### What Would a Proof Need?

- Key lemma 1: `powerMean_mono`: for p ≤ q and positive reals, M_p ≤ M_q
- Key lemma 2: Jensen for finite sums with convex φ
- Technical requirements: `Finset.sum`, `Real.rpow`, `ConvexOn ℝ`

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The 2-variable case is already done; n-variable requires Finset machinery
- Mathlib has `NNReal.pow_arith_mean_le_arith_mean_pow` (Power Mean inequality)
- Check if Mathlib's `MeanInequalities` already has this

**Estimated Effort**:
- Exploration: 1-2 hours (Mathlib search)
- If tractable: 1-2 days
- If hard: pivot to a specific subclaim

## References

### Mathlib Modules to Check
- `Mathlib.Analysis.MeanInequalities` — power mean, AM-GM, Hölder
- `Mathlib.Analysis.MeanInequalitiesPow` — `NNReal.pow_arith_mean_le_arith_mean_pow`
- `Mathlib.Analysis.InnerProductSpace.Basic` — Cauchy-Schwarz
- `Mathlib.Analysis.Calculus.MeanValue` — convexity tools

## Metadata

```yaml
tags:
  - inequalities
  - power-means
  - analysis
  - classical
related_proofs:
  - cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02
  - cauchy-schwarz-integral-oq-01-oq-01-oq-01
difficulty: medium
source: gallery-gap
created: 2026-04-04T00:00:00Z
```
