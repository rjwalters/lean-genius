# Problem: Integral representations of π from ∫₀¹ xᵐ(1-x)ⁿ/(1+x²) dx

**Slug**: area-of-circle-oq-03-oq-02-oq-02-oq-01-oq-03
**Created**: 2026-07-01
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
I(m,n) = \int_0^1 \frac{x^m (1-x)^n}{1+x^2}\, dx = A_{m,n} + B_{m,n}\,\pi + C_{m,n}\,\ln 2,
$$
with explicit rationals $A_{m,n}, B_{m,n}, C_{m,n} \in \mathbb{Q}$; the parent's Dalzell integral $\int_0^1 \frac{x^4(1-x)^4}{1+x^2}\,dx = \tfrac{22}{7} - \pi$ is the case $(m,n) = (4,4)$.

### Plain Language

The famous Dalzell integral $\int_0^1 x^4(1-x)^4/(1+x^2)\,dx = 22/7 - \pi$ proves $\pi < 22/7$ because the integrand is positive. The parent line formalized this single case. This problem generalizes: for arbitrary exponents $m, n$, the integral $I(m,n)$ evaluates to a rational combination of $1$, $\pi$, and $\ln 2$. We seek the general closed form and the rational coefficients, giving a systematic family of rational $\pi$-approximations and bounds.

### Why This Matters

These integrals turn positivity of a polynomial-over-$(1+x^2)$ integrand into sharp rational bounds on $\pi$. A general formula, machine-checked, yields an infinite family of certified inequalities $\pi \lessgtr p/q$ and connects the Dalzell trick to the theory of Beukers-style integral representations of constants.

### What's Already Proven

- Dalzell case $(4,4)$: $\int_0^1 \frac{x^4(1-x)^4}{1+x^2}\,dx = \frac{22}{7} - \pi$ and hence $\pi < 22/7$ (parent).
- The polynomial-division reduction that produces the rational + arctan + log terms (parent, for $(4,4)$).

### What's Still Open

- The general evaluation $I(m,n)$ and the coefficient formulas $A_{m,n}, B_{m,n}, C_{m,n}$.
- A recurrence in $m, n$ that drives the general case from base cases.

### Our Goal

Establish a recurrence (e.g. reduce $I(m,n)$ to $I(m-2,n)$ and lower via $x^2 = (1+x^2) - 1$) and prove that every $I(m,n)$ lands in $\mathbb{Q} + \mathbb{Q}\pi + \mathbb{Q}\ln 2$, then recover the parent as $(4,4)$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| area-of-circle Dalzell integral (parent) | the (4,4) base case | integral reduction, arctan, positivity |
| leibniz-pi / arctan-series | π from arctan integrals | `∫ 1/(1+x²) = arctan` |

## Initial Thoughts

### Potential Approaches

1. **Reduction recurrence via $x^2 = (1+x^2) - 1$**: split $x^m = x^{m-2}(1+x^2) - x^{m-2}$ to peel the denominator, expressing $I(m,n)$ through a polynomial integral (rational) plus lower $I$.
   - Why it might work: exactly the parent's polynomial-division step, iterated.
   - Risk: binomial bookkeeping in $(1-x)^n$ grows; careful `Finset.sum` handling needed.

2. **Expand $(1-x)^n$ by the binomial theorem**, reducing to $\sum_k \binom{n}{k}(-1)^k I(m+k, 0)$, and evaluate the one-parameter family $I(j,0)$ by a single recurrence.
   - Why it might work: collapses two indices to one.
   - Risk: sign/coefficient tracking through the binomial sum.

### Key Difficulties

- Managing the arctan (→ $\pi$) and log boundary terms symbolically in Lean.
- Proving the recurrence's base cases $I(0,0), I(1,0)$ ($= \pi/4$, $= \tfrac12\ln 2$).

### What Would a Proof Need?

- Key lemma 1: $\int_0^1 \frac{dx}{1+x^2} = \pi/4$ and $\int_0^1 \frac{x\,dx}{1+x^2} = \tfrac12\ln 2$.
- Key lemma 2: the peeling recurrence $I(m,n) \to$ polynomial integral $+ I(m-2,n)$.
- Technical requirements: `intervalIntegral`, `Real.arctan`, `Real.log`, `MeasureTheory` FTC lemmas.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The parent already carries the exact machinery for the $(4,4)$ instance; generalization is a recurrence.
- Base integrals are standard Mathlib results (`integral_one_div_one_add_sq`).
- Symbolic handling of the $\ln 2$ term adds bookkeeping but no deep obstruction.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 4–7 days
- If hard: 1–2 weeks (if the general closed form resists a clean recurrence)

## References

### Papers
- D. P. Dalzell, On 22/7 (1944), J. London Math. Soc.
- S. K. Lucas, Integral proofs that 355/113 > π (2005).

### Online Resources
- https://en.wikipedia.org/wiki/Proof_that_22/7_exceeds_π — the Dalzell integral and generalizations.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Integrals` — `integral_one_div_one_add_sq`, arctan integrals.
- `Mathlib.MeasureTheory.Integral.FundThmCalculus` — FTC for interval integrals.

## Metadata

```yaml
tags:
  - pi
  - integral
  - rational-approximation
  - dalzell
  - bounds
related_proofs:
  - area-of-circle
  - leibniz-pi
difficulty: medium
source: gallery-gap
created: 2026-07-01
```

**Significance**: 5/10
**Tractability**: 6/10
