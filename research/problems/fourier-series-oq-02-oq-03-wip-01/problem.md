# Problem: Complete Sharp Constant in Fourier Coefficient Decay Bound

**Slug**: fourier-series-oq-02-oq-03-wip-01
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
|\hat{c}_n(f)| \le \tfrac{1}{2}\, C \left(\frac{T}{2|n|}\right)^{\alpha}, \qquad f \in C^{0,\alpha}(\mathbb{T}),\ n \neq 0,
$$
with the constant $1/2$ shown to be sharp via extremal sawtooth functions.

### Plain Language

For a Hölder-continuous periodic function of exponent alpha, the size of its n-th
Fourier coefficient decays at least like |n|^{-alpha}, with an explicit constant.
This problem is about pinning down and proving the *sharp* value of that constant
(1/2) — showing both that the bound holds and that it cannot be improved, using
extremal (sawtooth-type) functions that nearly attain equality.

### Why This Matters

Sharp constants in Fourier decay bounds are the quantitative core of approximation
theory and harmonic analysis. Formalizing a sharp constant (not just an order of
magnitude) exercises Mathlib's integration and Hölder-continuity APIs and yields a
reusable, precisely-stated lemma.

## Known Results

### What's Already Proven

- The source entry `fourier-series-oq-02-oq-03` proves structural properties of the
  Fourier coefficients of Hölder functions and states the sharpness claim.
- Order-of-magnitude decay |ĉ_n| = O(|n|^{-α}) is standard.

### What's Still Open

- The exact/sharp value of the constant and the matching lower bound.
- The extremal-sawtooth construction certifying sharpness.

### Our Goal

Complete the work-in-progress source proof `fourier-series-oq-02-oq-03`: close the
remaining `sorry`s establishing the upper bound with constant 1/2 and the extremal
construction demonstrating the constant cannot be lowered.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| fourier-series-oq-02-oq-03 | Direct parent WIP proof being completed | Fourier coefficients, Hölder bounds |
| fourier-series | Base Fourier-series formalization | orthogonality, integration |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Integration-by-parts / modulus-of-continuity estimate for the
   upper bound.
   - Why it might work: Standard route to the constant via a shift-and-average trick.
   - Risk: Bounding the Hölder difference integral tightly to get exactly 1/2.

2. **Approach B**: Explicit sawtooth Fourier expansion for the lower bound.
   - Why it might work: Sawtooth coefficients are computable in closed form.
   - Risk: Formalizing the limiting extremal family in Lean.

### Key Difficulties

- Getting the *exact* constant rather than an order bound.
- Formalizing the extremal / near-extremal function family.

### What Would a Proof Need?

- Key lemma 1: The shift-average bound |ĉ_n| ≤ (1/2) C (T/2|n|)^α.
- Key lemma 2: Sawtooth coefficients realizing (near-)equality.
- Technical requirements: Mathlib Fourier and interval-integration API.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The upper bound is a bounded, self-contained estimate.
- The sharpness direction is more delicate but well understood classically.
- Mathlib has Fourier-coefficient and integration infrastructure.

**Estimated Effort**:
- Exploration: hours
- If tractable: days
- If hard: 1-2 weeks (sharpness side)

## References

### Papers
- Zygmund, "Trigonometric Series" — Hölder classes and coefficient decay.

### Online Resources
- Standard harmonic-analysis notes on Fourier decay of Lipschitz/Hölder functions.

### Mathlib
- `Mathlib.Analysis.Fourier.*` — Fourier coefficients on the circle.
- `Mathlib.MeasureTheory.Integral.*` — interval integration.

## Metadata

```yaml
tags:
  - analysis
  - harmonic-analysis
  - fourier-series
  - holder-continuity
  - sharp-constants
related_proofs:
  - fourier-series-oq-02-oq-03
  - fourier-series
difficulty: medium
source: gallery-gap
created: 2026-07-04
```
