# Problem: Lipschitz Bound for Fourier Coefficients via Mathlib LipschitzWith API

**Slug**: fourier-series-oq-02-incomplete-01-oq-01
**Created**: 2026-04-21T22:19:18+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Can `fourier_lipschitz_bound` be proved using Mathlib's `LipschitzWith` API for `toCircle`?

Specifically: given a Hölder-continuous function $f : \mathbb{T} \to \mathbb{C}$ with Lipschitz constant $C$, prove that the Fourier coefficients satisfy the decay bound

$$|\hat{f}(n)| \leq C / |n|^{\alpha}$$

via the `LipschitzWith` typeclass in Mathlib, leveraging the `toCircle` map from `Real` to `Circle`.

### Plain Language

The gallery entry `fourier-series-oq-02-incomplete-01` establishes infrastructure for Fourier coefficient decay under Hölder conditions, but leaves `fourier_lipschitz_bound` as a sorry. This problem asks whether Mathlib's `LipschitzWith` API — which provides a structured interface for Lipschitz maps — can be used to give a clean Lean 4 proof of the bound, closing the sorry.

### Why This Matters

- Provides missing infrastructure for the `fourier-series-oq-02` gallery chain (Hölder regularity → coefficient decay)
- Demonstrates the utility of `LipschitzWith` in harmonic analysis formalization
- The bound is foundational: it implies absolute convergence of Fourier series for smooth enough functions

## Known Results

### What's Already Proven

- Fourier coefficient decay for Hölder-α functions: `|c_n(f)| ≤ C/|n|^α` (stated, sorry in gallery)
- `LipschitzWith K f` in Mathlib provides: `dist (f x) (f y) ≤ K * dist x y`
- `toCircle : ℝ → Circle` is the quotient map, used in Fourier analysis in Mathlib

### What's Still Open

- Whether `fourier_lipschitz_bound` can be filled using existing Mathlib lemmas about `LipschitzWith toCircle`
- The precise API pathway through `ContinuousMap.lipschitz_of_forall_dist_le` or similar

### Our Goal

Fill the sorry in `fourier_lipschitz_bound` using Mathlib's `LipschitzWith` API and `toCircle`, producing a 0-sorry proof of the coefficient decay bound for Hölder-Lipschitz functions on the circle.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| fourier-series-oq-02-incomplete-01 | Direct parent — contains the sorry to fill | Fourier coefficient integrals, Hölder estimates |
| fourier-series-oq-02 | Full Hölder decay result (sorry-based) | summability, holder-continuity |
| fourier-series-oq-02-oq-03 | Sharpness of the bound | extremal functions |

## Initial Thoughts

### Potential Approaches

1. **Direct LipschitzWith integration**: Unfold the Fourier coefficient integral, apply `LipschitzWith.dist_le_mul`, and bound the resulting integral using `norm_integral_le_integral_norm`.
   - Why it might work: The Fourier coefficient is an integral; Lipschitz bounds on the integrand propagate via standard integral estimates.
   - Risk: The `toCircle` map may require additional unfolding to connect with `LipschitzWith`.

2. **Via HolderWith**: Mathlib has `HolderWith` for general Hölder continuity; the `α = 1` case (Lipschitz) may simplify things.
   - Why it might work: Direct instance between `LipschitzWith` and `HolderWith 1`.
   - Risk: The `α`-Hölder coefficient bound needs `α ≠ 1` for the general case.

### Key Difficulties

- Connecting `LipschitzWith K (f ∘ toCircle)` with the Fourier integral bound
- Ensuring the constant works out in the normalized integral (`1/(2π)` convention)
- The `toCircle` periodicity argument needs to handle the summation over `n`

### What Would a Proof Need?

- `LipschitzWith.dist_le_mul` applied to the phase factor `fun x => exp (2πi n x) - exp (2πi n y)`
- `norm_integral_le_integral_norm` for the coefficient bound
- Potentially: `Finset.sum_div_pow_mul_pow_le_pow_mul` or similar for the decay

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The bound is mathematically straightforward; the challenge is API navigation in Mathlib
- `LipschitzWith` is well-developed in Mathlib (Topology.MetricSpace.Lipschitz)
- Similar infrastructure proofs (e.g., `inner_le_nnorm_mul_nnorm`) typically require 20-50 lines

## References

### Mathlib
- `Mathlib.Topology.MetricSpace.Lipschitz` — `LipschitzWith` API
- `Mathlib.Analysis.Fourier.FourierTransform` — Fourier coefficient definitions
- `Mathlib.MeasureTheory.Integral.SetIntegral` — integral bound lemmas

## Metadata

```yaml
tags:
  - analysis
  - harmonic-analysis
  - fourier-series
  - holder-continuity
  - coefficient-decay
  - infrastructure
related_proofs:
  - fourier-series-oq-02-incomplete-01
  - fourier-series-oq-02
difficulty: medium
source: gallery-gap
created: 2026-04-21T22:19:18+02:00
```

**Significance**: 7/10
**Tractability**: 7/10
