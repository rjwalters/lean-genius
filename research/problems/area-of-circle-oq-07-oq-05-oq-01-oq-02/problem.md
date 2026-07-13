# Problem: Scaled Gaussian even moments ∫ x^{2n} e^{-a x²} dx = (2n-1)‼·√(π/a) / (2a)^n

**Slug**: area-of-circle-oq-07-oq-05-oq-01-oq-02
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For $a > 0$ and $n \in \mathbb{N}$,
$$
\int_{-\infty}^{\infty} x^{2n} e^{-a x^2}\, dx \;=\; (2n-1)!!\,\sqrt{\frac{\pi}{a}}\,\frac{1}{(2a)^n}.
$$

### Plain Language

The parent entry (`area-of-circle-oq-07-oq-05-oq-01`) proves the unit-scale even moment
$\int_{\mathbb R} x^{2n} e^{-x^2}\,dx = (2n-1)!!\,\sqrt{\pi}/2^n$. This leaf generalizes the
exponent rate to an arbitrary $a > 0$, tracking how the double-factorial recursion picks up powers
of $a$ under the substitution $x \mapsto x/\sqrt{a}$.

### Why This Matters

The scaled Gaussian moment is the workhorse identity behind Gaussian-integral normalization,
moment-generating functions of the normal distribution, and heat-kernel computations. Exhibiting the
clean dependence on the rate $a$ — total mass $\sqrt{\pi/a}$ scaled by $(2n-1)!!/(2a)^n$ — completes
the moment table started by the parent and the half-line sibling.

### Why $(2n-1)!!\,\sqrt{\pi/a}/(2a)^n$

Substitute $u = \sqrt{a}\,x$, so $x = u/\sqrt a$, $dx = du/\sqrt a$, and
$x^{2n} = u^{2n} a^{-n}$. Then $\int x^{2n} e^{-a x^2}dx = a^{-n}\cdot a^{-1/2}\int u^{2n} e^{-u^2}du
= a^{-n-1/2}\,(2n-1)!!\,\sqrt{\pi}/2^n = (2n-1)!!\,\sqrt{\pi/a}/(2a)^n$.

## Known Results

### What's Already Proven

- Parent `area-of-circle-oq-07-oq-05-oq-01`: $\int_{\mathbb R} x^{2n} e^{-x^2}\,dx = (2n-1)!!\sqrt\pi/2^n$ (verified).
- Sibling `area-of-circle-oq-07-oq-02-oq-02`: half-line Gaussian first/second moments (verified).
- Mathlib: `integral_gaussian`, `integral_rpow_mul_exp_neg_mul_sq`, and the change-of-variables API.

### What's Still Open

- The arbitrary-rate generalization $a > 0$ via the rescaling substitution (this entry).

### Our Goal

Prove the scaled even-moment formula for all $a > 0$ by reducing to the parent's $a = 1$ case through
the substitution $x \mapsto x/\sqrt a$ (Mathlib `MeasureTheory.integral_comp_smul` / `Measure.integral_comp_mul_left`
style), then collecting the $a$-powers with `field_simp`/`ring` and `Real.sqrt` lemmas.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| area-of-circle-oq-07-oq-05-oq-01 | Direct parent; unit-scale even moment | double factorial, IBP recursion |
| area-of-circle-oq-07-oq-02-oq-02 | Sibling; half-line Gaussian moments | integral_Ioi, change of variables |
| area-of-circle-oq-07 | Ancestor; Gaussian integral √π | integral_gaussian |

## Initial Thoughts

### Potential Approaches

1. **Rescaling substitution to the parent's $a=1$ moment**: change variables $u=\sqrt a\,x$ and pull
   out $a^{-n-1/2}$.
   - Why it might work: the parent fully handles the double-factorial structure; only the scaling
     bookkeeping is new.
   - Risk: getting the `Real.sqrt`/`rpow` algebra right ($a^{-1/2} = 1/\sqrt a$, $(2a)^n = 2^n a^n$)
     and matching Mathlib's change-of-variables lemma orientation.

2. **Direct induction via integration by parts** mirroring the parent, carrying $a$ through the
   recurrence $I_n = \tfrac{2n-1}{2a} I_{n-1}$.
   - Fallback if the substitution route is awkward in Lean.

### Key Difficulties

- `Real.sqrt` arithmetic on $\sqrt{\pi/a} = \sqrt\pi/\sqrt a$ and combining with the $2^n a^n$ denominator.
- Choosing the correct Mathlib change-of-variables lemma for the linear rescale.

### What Would a Proof Need?

- Key lemma 1: the parent even moment at $a = 1$.
- Key lemma 2: linear change of variables $u = \sqrt a\, x$ for the Gaussian integrand.
- Final: `field_simp`/`ring` plus `Real.sqrt_div`/`Real.sqrt_mul` to assemble the closed form.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The hard analytic core (double-factorial even moment) is inherited verified; the new content is a
  single rescaling substitution plus square-root algebra.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–3 days

## References

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral` — `integral_gaussian`, scaled Gaussian integrals.
- `Mathlib.MeasureTheory.Integral.*` — change-of-variables / `integral_comp_mul_left`.

## Metadata

```yaml
tags:
  - analysis
  - gaussian-integral
  - moments
  - double-factorial
related_proofs:
  - area-of-circle-oq-07-oq-05-oq-01
  - area-of-circle-oq-07-oq-02-oq-02
  - area-of-circle-oq-07
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
