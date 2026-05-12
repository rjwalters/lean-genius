# Current State

**Phase**: RESEARCH
**Since**: 2026-05-12T19:30:00Z
**Iteration**: 5

## Current Focus

S5 ACT complete: **translation invariance** of the parametric complex
Gaussian. For any shift `c : ℂ` and `b > 0`,

    ∫_ℂ exp(-(b · ‖z - c‖²)) dz = π / b.

Proof: translate the integrand by `−c`, invoke
`MeasureTheory.integral_add_right_eq_self` (the volume on `ℂ` is an
`IsAddHaarMeasure`, hence `IsAddRightInvariant`), and chain with the
unshifted parametric Gaussian (`complex_gaussian_integral_scaled_norm`
from S3). The mechanism is identical to the real-line idiom in
`ShannonEntropyOQ01.gaussian_variance` and `FourierSeriesOQ02.lean`'s
Fourier-shift lemma.

This unlocks the canonical **two-parameter** complex Gaussian density
(mean `c`, scale `b`):

    ∫_ℂ (b/π) · exp(-(b · ‖z - c‖²)) dz = 1.

## Built (Lean, S5 on top of S4a)

In `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` (S5 additions, total file
~543 lines):

- `complex_gaussian_integral_scaled_shifted_norm (b > 0) (c : ℂ) :
    ∫ z : ℂ, exp(-(b · ‖z - c‖²)) = π / b`
  — main translation-invariance theorem.
- `complex_gaussian_integral_scaled_shifted (b > 0) (c : ℂ) :
    ∫ z : ℂ, exp(-(b · normSq (z - c))) = π / b`
  — `Complex.normSq` form.
- `complex_gaussian_integral_unit_shifted_norm (c : ℂ) :
    ∫ z : ℂ, exp(-‖z - c‖²) = π`
  — `b = 1` corollary.
- `complex_gaussian_density_shifted (b > 0) (c : ℂ) :
    ∫ z : ℂ, (b/π) · exp(-(b · ‖z - c‖²)) = 1`
  — canonical two-parameter complex Gaussian probability density.

No new imports. The proof uses only existing dependencies
(`Mathlib.MeasureTheory.Group.Integral` is transitively pulled in by
`Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`).

All proofs are sorry-free, axiom-free. The `c = 0` case of each S5
theorem reduces to the corresponding S3 result; the new content is the
shift-by-`c` direction.

## Status

- Sorries: 0
- Axioms: 0
- Build: verified locally via `./proofs/scripts/docker-build.sh
  Proofs.AreaOfCircleOQ05OQ04` (2026-05-12 ~20:30 UTC).

## Decomposition Plan

| Session | Phase | Deliverable | Lines | Status |
|---|---|---|---|---|
| S1 | OBSERVE | Markdown set + three-statement repair | 0 Lean | merged |
| S2a | ACT-A | `complex_gaussian_integral` (b = π) | ~120 | merged |
| S3 | ACT-B | Parametric in `b > 0` + 3 corollaries | ~120 | merged |
| S4a | ACT | n-dim `∫_{ℂⁿ} exp(-b·∑‖zᵢ‖²) = (π/b)ⁿ` + 3 corollaries | ~96 | open (#18221) |
| S4b | OBSERVE | p-adic Mathlib gap survey (doc-only) | 0 Lean | open (#18269) |
| S5 | ACT | Translation invariance + `(c, b)`-density | ~110 | **this session** |
| S6 | ? | Either: complex Fourier-eigenfunction; or n-dim shifted; or p-adic Haar wrapper | TBD | deferred |

## Next Action

S5 unlocks three natural follow-on deliverables:

- **S6a (n-dim translation invariance)**: lift the 1-D shifted Gaussian to
  `Fin n → ℂ`, giving `∫_{ℂⁿ} exp(-(b·∑‖zᵢ - cᵢ‖²)) = (π/b)ⁿ` for any
  shift vector `c : Fin n → ℂ`. Direct combination of S4a and S5 idioms;
  needs `IsAddHaarMeasure` on the product measure (Mathlib supplies this
  via `MeasureTheory.Measure.pi.instIsAddHaarMeasure`).
- **S6b (complex Fourier-eigenfunction)**: still the canonical archimedean
  analogue of (C2). Mathlib has `Real.fourierIntegral_gaussian_pi`; the
  complex case is one ℂ ≃ ℝ × ℝ transport + Fubini reduction. Cleanest
  if S6a is in place (lifts to the n-dim Fourier-eigenfunction
  automatically).
- **S6c (Schur orthogonality)**: `∫ zᵢ · z̄ⱼ · (1/π)ⁿ · exp(-∑‖zₖ‖²) = δᵢⱼ`
  via parametric differentiation of the S4a normalised density. Requires
  `hasDerivAt_integral_of_dominated_loc` machinery (heavier).
- **S6d (Mathlib milestone — `Measure ℚ_p`)**: the explicit
  `MeasureTheory.Measure ℚ_p` instance with `μ(ℤ_p) = 1` from the S4b
  survey. Multi-week upstream PR; independent of S6a-c.

## Attempt Counts

- Total attempts: 5 sessions (S1 OBSERVE, S2a ACT-A, S3 ACT-B, S4a ACT,
  S5 ACT). S4b is a concurrent doc-only OBSERVE pass by a parallel
  agent; orthogonal to the S5 Lean work.
- Current approach attempts: 1 (S5 ACT, `integral_add_right_eq_self`)
- Approaches tried:
  - S1: OBSERVE — three-candidate repair scaffolding.
  - S2a: ACT-A — `b = π` complex Gaussian via Fubini + measurable equivalence.
  - S3: ACT-B — parametric Fubini, identical skeleton, generalised in `b`.
  - S4a: ACT — `exp(-∑) = ∏ exp` reduction + n-fold Fubini
    (`integral_fintype_prod_volume_eq_pow`), per-axis factor by S3.
  - S5: ACT — `integral_add_right_eq_self` + `complex_gaussian_integral_scaled_norm`,
    shifting `z - c → z + (-c)` to match the additive-translation form.
    First proof attempt failed at `rw [integral_add_right_eq_self]` (HOU
    can't pattern-match `?f (x + ?g)` through a lambda); fixed by
    chaining via `.trans` with the explicit `f := fun w => exp(-(b·‖w‖²))`.
