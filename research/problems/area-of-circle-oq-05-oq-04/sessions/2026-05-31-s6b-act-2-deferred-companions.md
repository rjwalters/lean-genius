# S6b ACT-2 — Deferred Companions: shifted Fourier-Gaussian + density-eigenfunction

**Researcher**: researcher-1
**Date**: 2026-05-31
**Phase**: RESEARCH (S6b ACT-2, follow-up to 2026-05-31 S6b ACT)
**Outcome**: COMPLETE — 2 theorems shipped, Docker-verified 3129/3129 jobs

## Context

The prior session (`2026-05-31-s6b-act-complex-fourier-gaussian.md`) shipped 3
theorems in Part 6 of `proofs/Proofs/AreaOfCircleOQ05OQ04.lean`:

- `complex_fourier_gaussian` — parametric Fourier-Gaussian at `V := ℂ`
- `complex_fourier_gaussian_pi` — load-bearing archimedean (C2) self-Fourier at `b = π`
- `complex_fourier_gaussian_normSq` — `Complex.normSq` companion

It explicitly deferred two companions for the next research claim
(per the prior `nextAction` field):

1. `complex_fourier_gaussian_shifted` — direct
   `_root_.fourier_gaussian_innerProductSpace'` specialization at `V := ℂ`
   (modulation companion, ~25 LOC target).
2. `complex_fourier_gaussian_density_eigen` — Fourier eigenfunction of the
   normalised density `(1/π) · exp(-π · ‖z‖²)` via constant-pull
   (~15-20 LOC target).

This session ships both as **Part 7** of the same file.

## Theorems shipped

### `complex_fourier_gaussian_shifted` (modulation companion)

Statement (sketch):
```
𝓕 (z ↦ exp(-b · ‖z‖² + 2π i · ⟪x, z⟫)) w
  = (π / b) · exp(-π² · ‖x - w‖² / b)
```

Proof: direct specialization of `_root_.fourier_gaussian_innerProductSpace'`
at `V := ℂ`. Collapse the dimensional exponent
`(Module.finrank ℝ ℂ / 2 : ℂ)` to `1` via `Complex.finrank_real_complex`,
then `Complex.cpow_one` reduces `(π/b) ^ (1 : ℂ)` to `π/b`. Direct
`exact h` discharges the remainder.

Strategic note: the modulation `2π i · ⟪x, z⟫` (a multiplicative phase
shift in the input) maps to an additive shift `w ↦ w - x` in the
Fourier-domain Gaussian peak. This is the Fourier-pair dual of S5's
*input* translation `complex_gaussian_integral_scaled_shifted_norm`,
where translation in the input integrates trivially via additive Haar
invariance; here translation appears in the Fourier domain as a
phase-modulation/peak-shift duality.

### `complex_fourier_gaussian_density_eigen` (normalised-density eigenfunction)

Statement:
```
𝓕 (z ↦ (1/π) · exp(-π · ‖z‖²)) w = (1/π) · exp(-π · ‖w‖²)
```

Proof: pull `(1/π)` out of the Fourier integral via
`integral_const_mul` (linearity of the Lebesgue integral), then apply
`complex_fourier_gaussian_pi`.

Key tactic gotcha discovered: `Circle.smul_def` rewrites
`(c : Circle) • a` to `(↑c : ℂ) • a` (still an `SMul`, not `*`).
To reach multiplicative form for `ring`, must follow with `smul_eq_mul`:

```lean
simp only [Circle.smul_def, smul_eq_mul]
ring
```

Naive `rw [Circle.smul_def, Circle.smul_def]; ring` leaves a residual
`↑(𝐞 _) • exp(...)` that `ring` cannot handle (it's still `SMul` on the
RHS after Circle.smul_def alone).

This is the **density-form companion** of `complex_fourier_gaussian_pi`:
the normalised density `(1/π) · exp(-π · ‖z‖²)` on ℂ — which integrates
to 1 by `complex_gaussian_integral_normalised` (S3) — is a fixed point
of `𝓕` with eigenvalue **1**. Together with
`complex_fourier_gaussian_pi`, this exhibits the archimedean Fourier
fixed-point structure as a `(1, 1)`-eigenpair (normalisation × constant).

## Build verification

```
./proofs/scripts/docker-build.sh Proofs.AreaOfCircleOQ05OQ04
=== Build succeeded ===
✔ [3129/3129] Built Proofs.AreaOfCircleOQ05OQ04 (39s)
```

Mathlib v4.26.0 (lake-manifest SHA `2df2f0150c…`).

## File state delta

- LOC: **771 → 854** (+83 LOC, vs. ~40 LOC target — overshoot due to
  full docstrings and a parser-quirk workaround for `⟪x, z⟫`
  coercion-to-ℂ form)
- Theorems: **24 → 26** (+2 in Part 7), plus 1 doc-only inline header
- Imports: **no changes** (Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
  was already pulled in by Part 6)
- Scopes: **added** `open scoped RealInnerProductSpace` (needed for `⟪x, z⟫`
  notation in the shifted statement). Previously only
  `open scoped FourierTransform`.
- Sorries: **0** (unchanged)
- Axioms: **0** (unchanged)

## Tactic-engineering notes

1. **`⟪x, z⟫_ℝ` parsing**: the subscripted form requires
   `open scoped InnerProductSpace` (not `RealInnerProductSpace`).
   The notation `⟪x, z⟫_ℝ` at the parser level is
   `⟪x, z⟫_` followed by `ℝ` and needs the `:max` notation declared
   in `InnerProductSpace.Defs`. We use the un-subscripted form
   `⟪x, z⟫` (which `RealInnerProductSpace` provides as `inner ℝ x z`)
   and an explicit `(_ : ℝ)` ascription where needed.

2. **`Circle.smul_def` is NOT `smul → mul`**: it rewrites
   `(c : Circle) • a` to `(↑c : ℂ) • a`. To reach `*`, follow with
   `smul_eq_mul`. This is the key tactic-level surprise of S6b ACT-2.

3. **`simp_rw` under binders**: `simp_rw [ptw]` correctly rewrites
   inside `∫ z, ...` even when `ptw` is `∀ z, ...`. Worked first try.

## Status post-ACT-2

| Theorem | Sorries | Axioms |
|---|---|---|
| `complex_fourier_gaussian` | 0 | 0 |
| `complex_fourier_gaussian_pi` | 0 | 0 |
| `complex_fourier_gaussian_normSq` | 0 | 0 |
| **`complex_fourier_gaussian_shifted` (NEW)** | 0 | 0 |
| **`complex_fourier_gaussian_density_eigen` (NEW)** | 0 | 0 |

The Fourier-Gaussian Part 6+7 package is now feature-complete for
the 1-dim complex case. Remaining S6 follow-ups (S6c/S6d) are
independent of this package.

## Next steps

- **S6c**: Schur orthogonality `∫ zᵢ z̄ⱼ · (1/π)ⁿ · exp(-∑‖zₖ‖²) = δᵢⱼ`
  via parametric differentiation. The 2026-05-13 PREP-2 #18584
  noted Mathlib's `gaussianReal`/`IsGaussian` moment shortcut now
  obsoletes the `hasDerivAt_integral_of_dominated_loc` route.
  ~40–60 LOC. Independent of S6a/S6b.
- **n-dim Fourier-Gaussian**: lift the Part 6+7 package to
  `EuclideanSpace ℂ (Fin n)` via the same
  `fourier_gaussian_innerProductSpace` at `V := EuclideanSpace ℂ ι`.
  Auto-generalizes — strategic add-on, ~30 LOC.
- **S6d**: Mathlib upstream PR for explicit
  `MeasureTheory.Measure ℚ_p` with `μ(ℤ_p) = 1` (multi-week,
  unchanged from S4b survey).
- **Housekeeping (Mechanic scope)**:
  flat-dir → canonical consolidation (7 files);
  `src/data/proofs/area-of-circle-oq-05-oq-04/` gallery entry
  creation; `leanFiles[].lineCount/theoremCount` in JSON still
  records 204/3 vs. actual 854/26.
