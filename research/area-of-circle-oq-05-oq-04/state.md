# Current State

**Phase**: RESEARCH
**Since**: 2026-05-14T22:30:00Z (S6 ACT shipped: n-dim shifted Gaussian on `Fin n → ℂ`)
**Iteration**: 6 (S6 ACT — strict generalisation of both S4a and S5)

## Current Focus

S6 ACT complete: **n-dimensional translation invariance** of the
parametric complex Gaussian. For any `n : ℕ`, `b > 0`, and any shift
vector `c : Fin n → ℂ`,

    ∫_{Fin n → ℂ} exp(-(b · ∑ᵢ ‖zᵢ - cᵢ‖²)) dz = (π / b)ⁿ.

Proof: factor the exponential of a sum as a product
(`Real.exp_sum` after `Finset.mul_sum` + `← Finset.sum_neg_distrib`),
apply **heterogeneous** n-fold Fubini
(`integral_fintype_prod_volume_eq_prod` — chosen over the uniform
`_eq_pow` because the per-axis factor depends on `i` through `cᵢ`),
collapse each per-axis integral to `π/b` via the S5 1-D shifted
theorem (`complex_gaussian_integral_scaled_shifted_norm`), and finish
with `Finset.prod_const`. See
`s6a-prep-pi-haar-vs-fubini.md` for the route audit and rejection of
the alternative pi-Haar lift (Path A); the file
`s6-act-n-dim-shifted-gaussian.md` contains this session's full ACT
notes.

This generalises both S4a (n-dim **unshifted**: `c = 0` reduction) and
S5 (1-D **shifted**: `n = 1` reduction), and unlocks the canonical
n-dimensional two-parameter complex Gaussian density (mean
`c : Fin n → ℂ`, scale `b > 0`):

    ∫_{Fin n → ℂ} (b/π)ⁿ · exp(-(b · ∑ᵢ ‖zᵢ - cᵢ‖²)) dz = 1.

## Built (Lean, S6 ACT on top of S5)

In `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` (S6 additions in new
`Part 5`, total file ~658 lines):

- `complex_gaussian_integral_scaled_pow_shifted_norm {n} (b > 0)
    (c : Fin n → ℂ) :
    ∫ z : Fin n → ℂ, exp(-(b · ∑ᵢ ‖zᵢ - cᵢ‖²)) = (π / b)ⁿ`
  — main n-dim shifted theorem (S6a Path B per
  `s6a-prep-pi-haar-vs-fubini.md`).
- `complex_gaussian_integral_scaled_pow_shifted_normSq {n} (b > 0)
    (c : Fin n → ℂ) :
    ∫ z : Fin n → ℂ, exp(-(b · ∑ᵢ normSq (zᵢ - cᵢ))) = (π / b)ⁿ`
  — `Complex.normSq` form via `simp_rw [Complex.normSq_eq_norm_sq]`.
- `complex_gaussian_integral_pow_unit_shifted_norm {n} (c : Fin n → ℂ) :
    ∫ z : Fin n → ℂ, exp(-∑ᵢ ‖zᵢ - cᵢ‖²) = πⁿ`
  — `b = 1` corollary; bridges to `complex_gaussian_integral_pow_unit_norm`
  (the `c = 0` case).
- `complex_gaussian_density_pow_shifted {n} (b > 0) (c : Fin n → ℂ) :
    ∫ z : Fin n → ℂ, (b/π)ⁿ · exp(-(b · ∑ᵢ ‖zᵢ - cᵢ‖²)) = 1`
  — canonical n-dim two-parameter complex Gaussian probability density.

The full S5 family (1-D shifted) remains in place from the prior ACT
and is exactly the `n = 1` reduction of the new theorems.

No new imports. The proof relies on `integral_fintype_prod_volume_eq_prod`
from `Mathlib.MeasureTheory.Integral.Pi` (already imported), the S5
shifted theorem `complex_gaussian_integral_scaled_shifted_norm`, and
standard `Finset` / `Real.exp_sum` simp lemmas.

All proofs are sorry-free, axiom-free. Each new theorem strictly
generalises the previous S4a + S5 work:

| New theorem | Reduces to (at `c = 0`) | Reduces to (at `n = 1`) |
|---|---|---|
| `..._scaled_pow_shifted_norm` | `..._scaled_pow` (S4a) | `..._scaled_shifted_norm` (S5) |
| `..._scaled_pow_shifted_normSq` | `..._scaled_pow_normSq` (S4a) | `..._scaled_shifted` (S5) |
| `..._pow_unit_shifted_norm` | `..._pow_unit_norm` (S4a) | `..._unit_shifted_norm` (S5) |
| `..._density_pow_shifted` | `..._pow_normalised` (S4a) | `..._density_shifted` (S5) |

## Status

- Sorries: 0
- Axioms: 0
- Build: verified via `./proofs/scripts/docker-build.sh
  Proofs.AreaOfCircleOQ05OQ04` (2026-05-14 ~23:00 UTC, 3123/3123 jobs,
  one pre-existing unused-variable warning in parent
  `AreaOfCircleOQ05.lean:60`, unrelated to this PR).

## Decomposition Plan

| Session | Phase | Deliverable | Lines | Status |
|---|---|---|---|---|
| S1 | OBSERVE | Markdown set + three-statement repair | 0 Lean | merged |
| S2a | ACT-A | `complex_gaussian_integral` (b = π) | ~120 | merged |
| S3 | ACT-B | Parametric in `b > 0` + 3 corollaries | ~120 | merged |
| S4a | ACT | n-dim `∫_{ℂⁿ} exp(-b·∑‖zᵢ‖²) = (π/b)ⁿ` + 3 corollaries | ~96 | open (#18221) |
| S4b | OBSERVE | p-adic Mathlib gap survey (doc-only) | 0 Lean | open (#18269) |
| S5 | ACT | Translation invariance + `(c, b)`-density | ~110 | merged |
| S6a PREP | PREP | Route audit: pi-Haar (A) vs Fubini (B) | 0 Lean | merged (#18389) |
| S6b PREP | PREP | Complex Fourier-eigenfunction route | 0 Lean | merged (#18422) |
| S6c PREP | PREP | Schur orthogonality via parametric differentiation | 0 Lean | merged (#18488) |
| S6c PREP-2 | PREP | Mathlib moment-shortcut obsoletes S6c | 0 Lean | merged (#18584) |
| S6 | ACT | n-dim shifted Gaussian + 3 corollaries (Path B) | ~115 | **this session** |

## Next Action

S6 ACT closes the route-B path identified by S6a PREP. The remaining
natural follow-on deliverables are:

- **S6b (complex Fourier-eigenfunction)**: still the canonical archimedean
  analogue of (C2). Mathlib has `Real.fourierIntegral_gaussian_pi`; the
  complex case is one ℂ ≃ ℝ × ℝ transport + Fubini reduction. Cleanest
  follow-up; lifts to the n-dim Fourier-eigenfunction automatically
  using the new `..._scaled_pow_shifted_norm` shifted theorem from this
  session.
- **S6c (Schur orthogonality)**: `∫ zᵢ · z̄ⱼ · (1/π)ⁿ · exp(-∑‖zₖ‖²) = δᵢⱼ`
  via Mathlib's `gaussianReal` moment shortcut (per S6c PREP-2).
  ~40-60 LOC. Adds a quantitative statistical result (variance
  computation). Independent of S6 ACT; uses S4a unshifted family.
- **S6d (Mathlib milestone — `Measure ℚ_p`)**: the explicit
  `MeasureTheory.Measure ℚ_p` instance with `μ(ℤ_p) = 1` from the S4b
  survey. Multi-week upstream PR; independent of S6a-c.

## Attempt Counts

- Total attempts: 10 sessions (S1 OBSERVE, S2a ACT-A, S3 ACT-B, S4a ACT,
  S4b OBSERVE, S5 ACT, S6a PREP, S6b PREP, S6c PREP, S6c PREP-2). This
  session is S6 ACT (Path B per S6a PREP).
- Current approach attempts: 1 (S6 ACT, heterogeneous Fubini chain).
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
  - S6 ACT (**this session**): Path B per S6a PREP. Heterogeneous Fubini
    via `integral_fintype_prod_volume_eq_prod` (verified at v4.26.0 pin
    `2df2f015...` at `Mathlib/MeasureTheory/Integral/Pi.lean:114`),
    `Real.exp_sum` factoring chain identical to S4a, per-axis collapse
    via the S5 shifted theorem. **First Docker build succeeded
    (3123/3123 jobs, 3.2s file build, no new warnings).**
