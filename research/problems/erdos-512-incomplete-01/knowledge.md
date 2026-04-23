# Knowledge: erdos-512-incomplete-01

## Problem Summary

**Goal**: Fill 2 sorry gaps in the Erdős #512 Aristotle companion file.

**Current state**:
- `Erdos512Problem.lean`: 1 sorry — `L2_norm` (Parseval's theorem, line 194)
- `Erdos512Aristotle.lean`: 2 sorries — `expSumNorm_continuous` and `L1norm_le_card`

**Note**: The Aristotle file header is outdated — `L1norm_upper_bound` in the main file is
already proved (no sorry). Only `L2_norm` remains there.

## Architecture

```
expSumNorm A θ = Complex.abs (expSum A θ)
expSum A θ = A.sum (fun n => expTwoPiI (n * θ))
expTwoPiI x = Complex.exp (2 * π * x * I)
```

Already proved (no sorry):
- `expSum_bound`: |expSum A θ| ≤ A.card (triangle + |e^{2πiθ}|=1)
- `L1norm_upper_bound`: ∫₀¹ |expSum| dθ ≤ A.card (continuity + monotone integral)
- All periodic properties, norm facts, etc.

## Session 2026-04-23 — Results (Session 1)

**Outcome**: progress
**Sorries closed**: 2 (`expSumNorm_continuous`, `L1norm_le_card` in Aristotle file)

**Key proofs**:
- `expSumNorm_continuous`: standard tactic chain — `Complex.continuous_abs.comp` →
  `continuous_finset_sum` → `Complex.continuous_exp.comp` → `fun_prop`
- `L1norm_le_card`: continuity → `integrableOn_compact` → `setIntegral_mono_on` →
  `set_integral_const` with `Real.volume_Icc`
  Both proofs mirror the inline proof in `L1norm_upper_bound` (main file lines 105-131).

**Remaining**:
- `L2_norm` (Parseval): `∫₀¹ |∑_{n∈A} e(nθ)|² dθ = |A|`
  Strategy: expand via double sum + character orthogonality `∫₀¹ e^{2πikθ} dθ = [k=0]`
  This requires more Fourier analysis infrastructure in Mathlib.

## Mathlib API Notes

- `Complex.continuous_abs.comp` — continuity of complex abs composed with continuous fn
- `continuous_finset_sum` — finite sum of continuous functions is continuous
- `Complex.continuous_exp.comp` — continuity of complex exponential
- `fun_prop` — closes arithmetic continuity goals (e.g., `2 * π * ↑n * θ * I` continuous in θ)
- `ContinuousOn.integrableOn_compact` — integrable on compact interval from continuity
- `integrableOn_const.mpr (Or.inr ...)` — constant is integrable when finite measure
- `setIntegral_mono_on` — monotone integral bound
- `set_integral_const` — integral of constant = constant * volume
- `Real.volume_Icc` — volume of [a,b] = ENNReal.ofReal (b-a)
- `ENNReal.toReal_ofReal` — converts back to ℝ

## Next Steps

1. `L2_norm`: Prove ∫₀¹ |expSum A θ|² dθ = |A| via Parseval/character orthogonality
   - Key step: `∫₀¹ expTwoPiI (k * θ) dθ = if k = 0 then 1 else 0` for integer k
   - When k≠0: antiderivative is `expTwoPiI (k * θ) / (2πki)`; FTC gives (e^{2πki}-1)/(2πki) = 0
   - Need: `Complex.integral_exp` or `intervalIntegral.integral_comp_mul_right` in Mathlib
   - Then swap integral and double sum using `MeasureTheory.integral_finset_sum`
