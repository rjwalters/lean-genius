# Knowledge Base: fourier-series-oq-02-incomplete-01-oq-01

**Problem**: Lipschitz Bound for Fourier Coefficients via Mathlib LipschitzWith API
**Selected**: 2026-04-22
**Selection Score**: composite 77 (EMPTY tier, tractability 7, significance 7)

---

## Problem Understanding

### The Core Question

Can `fourier_lipschitz_bound` be proved using Mathlib's `LipschitzWith` typeclass?

Specifically, the goal is to prove:
```lean
LipschitzWith (2 * Real.pi * |↑n| / T) (fourier n)
```
— or equivalently, that for each Fourier character `fourier n : AddCircle T → ℂ`, the map
is Lipschitz with explicit constant `2π|n|/T`.

### Current State of the Parent Proof

`FourierSeriesOQ02Incomplete01.lean` — fully proved (0 sorries). The key theorem is:

```lean
theorem fourier_lipschitz_bound (n : ℤ) (x y : AddCircle T) :
    ‖fourier n x - fourier n y‖ ≤ 2 * Real.pi * |↑n| / T * dist x y
```

Proof uses direct computation via:
1. Factoring: exp(A) - exp(B) = exp(B)·(exp(A-B) - 1)
2. Unit norm of exp on circle
3. Periodicity via `round(T⁻¹*(x-y))` for optimal representative
4. Applying `norm_exp_I_mul_ofReal_sub_one_le`: ‖exp(Iθ) - 1‖ ≤ |θ|

**The existing proof does NOT use `LipschitzWith`.** The OQ-01 asks whether a cleaner
proof using Mathlib's `LipschitzWith` typeclass is possible.

### Why LipschitzWith Matters

`LipschitzWith K f` gives composability: if `f` and `g` are Lipschitz, Mathlib can
automatically derive Lipschitz bounds for compositions, sums, etc. A `LipschitzWith`
proof for `fourier n` would integrate better with the broader Mathlib ecosystem for
harmonic analysis.

---

## Insights

### Key Mathlib Entry Points

- `LipschitzWith.of_dist_le_mul`: Given `∀ x y, dist (f x) (f y) ≤ K * dist x y`, constructs `LipschitzWith K f`
- The current direct bound already shows `dist (fourier n x) (fourier n y) ≤ 2π|n|/T * dist x y`
- `Complex.exp_lipschitz`: The exponential map on ℂ is locally Lipschitz; on the unit circle it may have specialized bounds
- `Continuous.lipschitzWith` doesn't exist directly — need `LipschitzWith.mk`

### Likely Direct Approach

Use `LipschitzWith.of_dist_le_mul` with the existing bound:
```lean
lemma fourier_lipschitz (n : ℤ) : LipschitzWith (⟨2 * Real.pi * |↑n| / T, ...⟩) (fourier n)
```
The `LipschitzWith` constant must be an `NNReal`, so need to bundle `2π|n|/T` with a
nonnegativity proof.

### Alternative: Derive from Circle Exponential Lipschitzness

The map `θ ↦ exp(2πiθ/T)` on `ℝ` is Lipschitz with constant `2π/T`, and composing with
`n * id` gives constant `2π|n|/T`. Then quotient by `T` to get AddCircle. Mathlib may
have `AddCircle.lipschitzWith_toCircle` or similar.

---

## Dead Ends

### Avoid Synthesizing from Smoothness

`fourier n` is smooth, but going smooth → Lipschitz in Mathlib requires explicit constant
bounds and is more work than the direct approach. The direct `of_dist_le_mul` route reuses
the existing computation.

### NNReal Constant Requires Care

`LipschitzWith K f` uses `K : NNReal`. Converting `2 * Real.pi * |↑n| / T` to `NNReal`
requires `hT : Fact (0 < T)` (available) and `n : ℤ` (|n| ≥ 0). The cast is:
`⟨2 * Real.pi * |↑n| / T, by positivity⟩ : NNReal`.
