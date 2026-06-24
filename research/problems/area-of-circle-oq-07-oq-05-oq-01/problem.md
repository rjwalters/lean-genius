# Problem: General Even Gaussian Moment by Induction

**Slug**: area-of-circle-oq-07-oq-05-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\int_{\mathbb{R}} x^{2n}\, e^{-x^2}\, dx \;=\; \frac{(2n-1)!!\,\sqrt{\pi}}{2^{n}}, \qquad n \in \mathbb{N},
$$
proved by induction on $n$ via the integration-by-parts recursion $I_n = \frac{2n-1}{2} I_{n-1}$, with base case $I_0 = \sqrt{\pi}$.

### Plain Language

We want the closed form for all even moments of the standard (unnormalized) Gaussian weight $e^{-x^2}$. The odd moments vanish by symmetry; the even moment of order $2n$ equals the double factorial $(2n-1)!! = 1\cdot 3\cdot 5\cdots(2n-1)$ times $\sqrt\pi / 2^n$. Integration by parts on $x^{2n} e^{-x^2}$ generates the recursion $I_n = \frac{2n-1}{2} I_{n-1}$, and induction from the Gaussian integral $I_0 = \sqrt\pi$ gives the formula. The parent entry handles the second moment ($n=1$); this generalizes to all $n$.

### Why This Matters

Gaussian moments are foundational across probability (moments of the normal distribution), mathematical physics (harmonic oscillator), and analysis. The double-factorial recursion is a clean example of how integration by parts yields a complete moment sequence, and it underlies the moment-generating function of the normal law.

## Known Results

### What's Already Proven

- Parent `area-of-circle-oq-07-oq-05` establishes the second moment $\int x^2 e^{-x^2}\,dx = \sqrt\pi/2$.
- Mathlib `integral_gaussian` gives $\int e^{-b x^2} = \sqrt{\pi/b}$, providing the base case.
- Gallery `area-of-circle-oq-07-oq-04-*` entries develop Gaussian/Fubini machinery.

### What's Still Open

- The general even-moment closed form for arbitrary $n$, by induction, in Lean.
- A clean statement of the double-factorial recursion as a reusable lemma.

### Our Goal

State $\int_{\mathbb{R}} x^{2n} e^{-x^2}\,dx = (2n-1)!!\sqrt\pi/2^n$ and prove it by induction, deriving the IBP recursion $I_n = \frac{2n-1}{2}I_{n-1}$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| area-of-circle-oq-07-oq-05 | Direct parent: second moment base case | Gaussian integral / IBP |
| area-of-circle-oq-07-oq-04-oq-01 | Gaussian as 2-D area via Fubini | Fubini, polar |

## Initial Thoughts

### Potential Approaches

1. **IBP recursion + induction**: Prove $I_n = \frac{2n-1}{2}I_{n-1}$ from `integral_mul_deriv` / IBP, then induct.
   - Why it might work: Mathlib has integration-by-parts and the Gaussian base case.
   - Risk: integrability side-conditions for $x^{2n}e^{-x^2}$ at each step.

2. **Differentiation under the integral**: Differentiate $\int e^{-b x^2}$ repeatedly in $b$.
   - Why it might work: directly produces moments.
   - Risk: justifying differentiation under the integral sign in Lean is heavy.

### Key Difficulties

- Establishing integrability of $x^{2n}e^{-x^2}$ and the vanishing boundary terms in IBP.
- Encoding the double factorial $(2n-1)!!$ and matching it to the recursion.

### What Would a Proof Need?

- Key lemma: IBP recursion $\int x^{2n}e^{-x^2} = \frac{2n-1}{2}\int x^{2(n-1)}e^{-x^2}$.
- Key lemma: integrability of $x^{2n}e^{-x^2}$ over $\mathbb{R}$.
- Technical requirements: Gaussian base case, double-factorial arithmetic.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Base case and Gaussian machinery already in Mathlib and the parent entry.
- The induction is standard; integrability lemmas for polynomial × Gaussian exist (`Integrable` of Gaussian-decaying functions).
- Similar moment computations appear in the area-of-circle gallery line.

**Estimated Effort**:
- Exploration: 1 day
- If tractable: a few days

## References

### Papers
- Standard probability texts — moments of the normal distribution and double factorials.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Gaussian` — `integral_gaussian`, integrability of Gaussian × polynomial.
- `Mathlib.MeasureTheory.Integral.IntegrationByParts` — IBP on $\mathbb{R}$.

## Metadata

```yaml
tags:
  - analysis
  - gaussian-integral
  - moments
related_proofs:
  - area-of-circle-oq-07-oq-05
  - area-of-circle-oq-07-oq-04-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
