# Problem: Fourier Transform of Gaussian in Lean 4 via Mathlib

**Slug**: area-of-circle-oq-05-oq-03
**Tier**: B | **Significance**: 7/10 | **Tractability**: 6/10
**Category**: extension
**Source**: gallery-gap
**Status**: Active (OBSERVE)

## Problem Statement

### Formal Statement

Prove that the Fourier transform of the standard Gaussian is another Gaussian:

$$
\int_{-\infty}^{\infty} e^{itx} \cdot \frac{e^{-x^2/2}}{\sqrt{2\pi}} \, dx = e^{-t^2/2}
$$

The exact Lean target from `CentralLimitTheorem.lean`:
```lean
axiom gaussian_fourier_identity (t : ℝ) :
  ∫ x : ℝ, Complex.exp (Complex.I * ↑t * ↑x) ∂stdGaussian =
  Complex.exp (-(↑t : ℂ)^2 / 2)
```
where `stdGaussian` is the standard Gaussian measure on ℝ.

### Plain Language

The Gaussian function is its own Fourier transform (up to normalization). This is the
self-duality property of the Gaussian. Key computation: completing the square in
$itx - x^2/2 = -\tfrac{1}{2}(x-it)^2 - t^2/2$, factoring out $e^{-t^2/2}$, then
recognizing the remaining integral as the Gaussian integral $\sqrt{2\pi}$.

## Why This Matters

**Critical gap**: `proofs/Proofs/CentralLimitTheorem.lean` axiomatizes this identity.
Proving it would eliminate the `gaussian_fourier_identity` axiom from the CLT proof,
strengthening the gallery's `central-limit-theorem` entry.

## Known Mathlib Lemmas to Investigate

- `MeasureTheory.integral_gaussian_complex` — may exist in `Mathlib.Analysis.SpecialFunctions.Gaussian`
- `Real.integral_gaussian` — `∫ x, exp (-b * x^2) = √(π / b)` for b > 0
- `MeasureTheory.GaussianFourier` module or similar
- `ProbabilityTheory.gaussianFourierTransform` — check if exists
- `integral_comp_add_right`, `integral_comp_mul_right` — for contour-shift steps

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| area-of-circle-oq-05 | Parent: Gaussian integral ∫ e^{-x²} dx = √π |
| area-of-circle-oq-05-oq-01 | Polar-coordinate proof of Gaussian integral (4 sorries) |
| central-limit-theorem | Uses `gaussian_fourier_identity` as axiom — this would remove it |

## Known Results

- `gaussian_integral_eq_sqrt_pi` in `AreaOfCircleOQ05.lean`: ∫ e^{-x²} dx = √π
- `Real.integral_gaussian` in Mathlib: ∫ x, exp (-b * x^2) = √(π / b)
- The CLT proof uses the axiom at `CentralLimitTheorem.lean:100`

## Approach Strategy

**Primary**: Check if Mathlib already has a direct formalization:
  - `Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform` (may exist)
  - `MeasureTheory.integral_mul_left` + completing-the-square algebraic manipulation

**Fallback**: Prove directly:
  1. Complete the square: $itx - x^2/2 = -(x-it)^2/2 - t^2/2$
  2. Factor out $e^{-t^2/2}$
  3. Shift integration variable $u = x - it$ (using `integral_comp_add_right`)
  4. Apply Gaussian integral result to get $\sqrt{2\pi}$ normalization
  5. Conclude

## Metadata

```yaml
tags:
  - analysis
  - fourier
  - gaussian
  - mathlib
  - central-limit-theorem
related_proofs:
  - area-of-circle-oq-05
  - area-of-circle-oq-05-oq-01
  - central-limit-theorem
difficulty: medium
source: gallery-gap
tier: B
significance: 7
tractability: 6
```
