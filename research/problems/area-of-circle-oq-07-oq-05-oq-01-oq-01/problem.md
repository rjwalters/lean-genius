# Problem: Vanishing of the odd Gaussian moments ∫ x^{2n+1} e^{-x²} dx = 0

**Slug**: area-of-circle-oq-07-oq-05-oq-01-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For every $n \in \mathbb{N}$,
$$
\int_{-\infty}^{\infty} x^{2n+1} e^{-x^2}\, dx \;=\; 0,
$$
and hence the full moment sequence is
$$
\int_{-\infty}^{\infty} x^{k} e^{-x^2}\, dx \;=\;
\begin{cases} (k-1)!!\,\sqrt{\pi}/2^{k/2}, & k \text{ even},\\[2pt] 0, & k \text{ odd}.\end{cases}
$$

### Plain Language

The parent entry (`area-of-circle-oq-07-oq-05-oq-01`) computes the **even** Gaussian moments
$\int_{\mathbb R} x^{2n} e^{-x^2}\,dx = (2n-1)!!\sqrt\pi/2^n$. This leaf handles the **odd** moments:
the integrand $x^{2n+1} e^{-x^2}$ is an odd function, so its integral over the whole line vanishes by
symmetry. Combined with the parent, this gives the complete moment sequence for all $k$.

### Why This Matters

The odd moments vanishing is the analytic reason the centered Gaussian has zero mean and zero
skewness (and all odd central moments zero). Together with the parent's even-moment formula it closes
the full moment table $\int_{\mathbb R} x^k e^{-x^2}\,dx$ for every $k$ — the complete moment data of
the (unnormalized) standard Gaussian.

### Why the integral is $0$

$f(x) = x^{2n+1} e^{-x^2}$ satisfies $f(-x) = -f(x)$ (odd power times the even Gaussian factor).
The integral of an odd, integrable function over a symmetric domain $\mathbb R$ is $0$.

## Known Results

### What's Already Proven

- Parent `area-of-circle-oq-07-oq-05-oq-01`: even moments $\int_{\mathbb R} x^{2n} e^{-x^2}\,dx = (2n-1)!!\sqrt\pi/2^n$ (verified).
- Sibling `area-of-circle-oq-07-oq-05-oq-01-oq-02`: scaled even moments with rate $a > 0$.
- Mathlib: integrability of Gaussian-weighted polynomials and `MeasureTheory.integral_eq_zero_of_odd` (odd-function integral lemma).

### What's Still Open

- The odd-moment vanishing and the assembled full moment sequence (this entry).

### Our Goal

Prove $\int_{\mathbb R} x^{2n+1} e^{-x^2}\,dx = 0$ from oddness of the integrand (Mathlib's
odd-function integral lemma plus integrability of $x^{2n+1}e^{-x^2}$), then state the combined
even/odd moment sequence as a corollary of the parent.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| area-of-circle-oq-07-oq-05-oq-01 | Direct parent; even Gaussian moments | double factorial, IBP recursion |
| area-of-circle-oq-07-oq-05-oq-01-oq-02 | Sibling; scaled even moments | change of variables |
| area-of-circle-oq-07-oq-02-oq-02 | Cousin; half-line Gaussian moments | integral_Ioi |

## Initial Thoughts

### Potential Approaches

1. **Odd-function symmetry**: show $x \mapsto x^{2n+1} e^{-x^2}$ is odd and integrable, then apply
   Mathlib's `integral_eq_zero_of_odd` (or `MeasureTheory.integral_comp_neg` + antisymmetry).
   - Why it might work: the vanishing is purely a symmetry statement; Mathlib has a direct lemma.
   - Risk: discharging the integrability side condition for $x^{2n+1} e^{-x^2}$ (Gaussian decay
     dominates any polynomial — `integrable_polynomial_mul_exp_neg_sq` style lemma).

### Key Difficulties

- Verifying integrability of the polynomial-times-Gaussian integrand to license the odd-integral lemma.

### What Would a Proof Need?

- Key lemma 1: $f(x) = x^{2n+1} e^{-x^2}$ is odd (`Odd`/`Function.Odd`).
- Key lemma 2: $f$ is integrable over $\mathbb R$ (Gaussian decay).
- Key lemma 3: odd integrable function ⟹ integral $0$.
- Corollary: assemble the full even/odd moment sequence with the parent.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- A one-step symmetry argument over an established Mathlib lemma; the only real work is the
  integrability side condition, which has standard Gaussian-decay support.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1 day

## References

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral` — Gaussian integrability lemmas.
- `Mathlib.MeasureTheory.Integral.*` — `integral_eq_zero_of_odd` / odd-function integral over ℝ.

## Metadata

```yaml
tags:
  - analysis
  - gaussian-integral
  - moments
  - symmetry
related_proofs:
  - area-of-circle-oq-07-oq-05-oq-01
  - area-of-circle-oq-07-oq-05-oq-01-oq-02
  - area-of-circle-oq-07-oq-02-oq-02
difficulty: low
source: gallery-gap
created: 2026-06-24
```
