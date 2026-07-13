# Problem: Half-line Gaussian moments (first and second absolute moments)

**Slug**: area-of-circle-oq-07-oq-02-oq-02
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For every $b > 0$:

$$
\int_{0}^{\infty} x \, e^{-b x^2}\,dx = \frac{1}{2b},
\qquad
\int_{0}^{\infty} x^2 \, e^{-b x^2}\,dx = \frac{1}{4b}\sqrt{\frac{\pi}{b}}.
$$

### Plain Language

The parent entry (`area-of-circle-oq-07-oq-02`) evaluates the half-line Gaussian
$\int_0^\infty e^{-bx^2}\,dx = \tfrac12\sqrt{\pi/b}$. This leaf computes the next two moments of
the half-line Gaussian: the **first absolute moment** $1/(2b)$ (an elementary closed form, the
integrand being an exact derivative) and the **second moment** $\sqrt{\pi/b}/(4b)$ (via
integration by parts reducing to the parent's value). Together these give the mean and variance of
the half-normal distribution.

### Why This Matters

These moments are the building blocks of the half-normal/Maxwell distributions and of Gaussian
integral identities generally. The first moment is a clean exact-derivative computation; the
second illustrates the integration-by-parts recursion $M_{k+2} = \tfrac{k+1}{2b} M_k$ that
generates all Gaussian moments.

## Known Results

### What's Already Proven

- Parent `area-of-circle-oq-07-oq-02`: $\int_0^\infty e^{-bx^2}\,dx = \tfrac12\sqrt{\pi/b}$ (verified).
- Sibling `area-of-circle-oq-07-oq-05-oq-01`: even Gaussian moment $\int_{\mathbb R} x^{2n} e^{-x^2}$ family.
- Mathlib `integral_gaussian`, `integral_mul_gaussian`-style lemmas and `Real.Gamma` half-integer values.

### What's Still Open

- The two half-line moments stated above (this entry).

### Our Goal

Prove both half-line moment formulas for all $b > 0$: the first via the exact antiderivative
$-\tfrac{1}{2b}e^{-bx^2}$ and the FTC/`MeasureTheory.integral_Ioi` tools, the second via
integration by parts reducing to the parent's half-line value.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| area-of-circle-oq-07-oq-02 | Direct parent; half-line Gaussian value | Gaussian integral, even symmetry |
| area-of-circle-oq-07-oq-05-oq-01 | Sibling; even Gaussian moments | Gamma half-integer, moment recursion |

## Initial Thoughts

### Potential Approaches

1. **First moment via exact derivative**: $\tfrac{d}{dx}\!\left[-\tfrac{1}{2b}e^{-bx^2}\right] = x e^{-bx^2}$;
   evaluate the improper integral over $(0,\infty)$ via `integral_Ioi_of_hasDerivAt_of_tendsto` /
   `MeasureTheory.integral_Ioi_eq...`, with the boundary term $\to 0$.
2. **Second moment via parts**: write $x^2 e^{-bx^2} = x \cdot (x e^{-bx^2})$ and integrate by parts,
   the boundary term vanishes, leaving $\tfrac{1}{2b}\int_0^\infty e^{-bx^2} = \tfrac{1}{2b}\cdot\tfrac12\sqrt{\pi/b}$.

### Key Difficulties

- Handling improper integrals on `Ioi 0` and vanishing boundary terms cleanly in Mathlib.
- Integrability side-conditions for the integration-by-parts lemma.

### What Would a Proof Need?

- Key lemma 1: `HasDerivAt` for the antiderivative and a `Tendsto ... atTop (𝓝 0)` boundary fact.
- Key lemma 2: `MeasureTheory.integral_mul_deriv_eq_deriv_mul` (integration by parts on `Ioi`).
- Reuse parent's half-line Gaussian value.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- First moment is an elementary exact-derivative computation.
- Second reduces by one integration by parts to the parent's already-verified value.
- Mathlib has the FTC-on-`Ioi` and parts machinery; main friction is integrability bookkeeping.

**Estimated Effort**:
- Exploration: hours
- If tractable: 2–4 days

## References

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral` — Gaussian integral values.
- `Mathlib.MeasureTheory.Integral.IntegralEqImproper` — `Ioi` improper integrals and FTC.
- `Mathlib.MeasureTheory.Integral.Parts` — integration by parts.

## Metadata

```yaml
tags:
  - analysis
  - integration
  - gaussian
  - moments
related_proofs:
  - area-of-circle-oq-07-oq-02
  - area-of-circle-oq-07-oq-05-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
