# Current State

**Phase**: RESEARCH
**Since**: 2026-05-12T17:00:00Z
**Iteration**: 4

## Current Focus

S4a ACT complete: n-dimensional parametric complex Gaussian
`∫_{ℂⁿ} exp(-(b·∑‖zᵢ‖²)) = (π/b)ⁿ` proved for arbitrary `n : ℕ` and
`b > 0`. Same Fubini-style skeleton as `AreaOfCircleOQ05OQ02.diagonal_gaussian`
(real-axis n-fold), with each ℂ-factor contributing `π/b` via
`complex_gaussian_integral_scaled_norm` (S3) instead of the real
`scaled_gaussian`.

## Built (Lean)

In `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` (S4a additions on top of
S3, total file 429 lines):

- `complex_gaussian_integral_scaled_pow {n : ℕ} (b > 0) :
    ∫ z : Fin n → ℂ, exp(-(b · ∑ ‖zᵢ‖²)) = (π/b)ⁿ`
  — n-fold Fubini via `integral_fintype_prod_volume_eq_pow`.
- `complex_gaussian_integral_scaled_pow_normSq {n : ℕ} (b > 0) :
    ∫ z : Fin n → ℂ, exp(-(b · ∑ normSq (zᵢ))) = (π/b)ⁿ`
  — `Complex.normSq` form, via `normSq_eq_norm_sq`.
- `complex_gaussian_integral_pow_unit_norm {n : ℕ} :
    ∫ z : Fin n → ℂ, exp(-∑ ‖zᵢ‖²) = πⁿ`
  — `b = 1` corollary.
- `complex_gaussian_integral_pow_normalised {n : ℕ} :
    ∫ z : Fin n → ℂ, (1/π)ⁿ · exp(-∑‖zᵢ‖²) = 1`
  — normalised joint density (multi-mode coherent-state weight).

Added import: `Mathlib.MeasureTheory.Integral.Pi`.

All proofs are sorry-free, axiom-free. The `n = 1` case reduces to S3
(the per-axis factor `π/b` is exactly `complex_gaussian_integral_scaled_norm`).

## Status

- Sorries: 0
- Axioms: 0
- Build: pending Docker verification at commit time.

## Decomposition Plan

| Session | Phase | Deliverable | Lines | Status |
|---|---|---|---|---|
| S1 | OBSERVE | Markdown set + three-statement repair | 0 Lean | merged |
| S2a | ACT-A | `complex_gaussian_integral` (b = π) | ~120 | merged |
| S3 | ACT-B | Parametric in `b > 0` + 3 corollaries | ~120 | merged |
| S4a | ACT | n-dim `∫_{ℂⁿ} exp(-b·∑‖zᵢ‖²) = (π/b)ⁿ` + 3 corollaries | ~96 | **this session** |
| S5 | ? | Either: complex Gaussian Fourier-eigenfunction; or stepwise approach to p-adic | TBD | deferred |

## Next Action

Two viable S5 deliverables (priority unclear, both significant):

- **S5a (complex Fourier-eigenfunction)**: prove that the complex Gaussian
  `f(z) = exp(-π‖z‖²)` is a fixed point of the 2-D real Fourier
  transform (via the ℂ ≃ ℝ² identification). This is the canonical
  archimedean statement of which (C2) is the p-adic analogue and would
  motivate the parallel between the two cases mathematically. Mathlib
  status: `MeasureTheory.fourierIntegral_gaussian_pi` exists for the
  real Gaussian — the complex case is one transport + Fubini reduction.
- **S5b (p-adic Haar wrapper)**: contribute the first of the two
  Mathlib milestones — an explicit `MeasureTheory.Measure ℚ_p` instance
  normalised so `μ(ℤ_p) = 1`. Plausible single-PR Mathlib contribution.
  Builds toward (C2) but does not yet prove it.

The S4a n-dim result also enables a fourth direction:

- **S5c (Schur orthogonality)**: with the n-dim normalised density
  `(1/π)ⁿ · exp(-∑‖zᵢ‖²)` proved as a probability density, the
  complex orthogonality `∫ zᵢ · z̄ⱼ · (1/π)ⁿ · exp(-∑‖zₖ‖²) = δᵢⱼ`
  follows by parametric differentiation. This is a natural next
  expansion of the complex-Gaussian theme.

## Attempt Counts

- Total attempts: 4 sessions (S1 OBSERVE, S2a ACT-A, S3 ACT-B, S4a ACT)
- Current approach attempts: 1 (S4a ACT, fintype-prod Fubini)
- Approaches tried:
  - S1: OBSERVE — three-candidate repair scaffolding.
  - S2a: ACT-A — `b = π` complex Gaussian via Fubini + measurable equivalence.
  - S3: ACT-B — parametric Fubini, identical skeleton, generalised in `b`.
  - S4a: ACT — `exp(-∑) = ∏ exp` reduction + n-fold Fubini
    (`integral_fintype_prod_volume_eq_pow`), per-axis factor by S3.
