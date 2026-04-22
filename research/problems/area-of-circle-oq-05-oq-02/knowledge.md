# Knowledge: area-of-circle-oq-05-oq-02

## Problem Summary

**Goal**: Prove the multivariate Gaussian integral
```
∫ x : Fin n → ℝ, exp(-xᵀAx) = √(πⁿ / det A)
```
for positive-definite real symmetric A, via spectral decomposition.

**File**: `proofs/Proofs/AreaOfCircleOQ05OQ02.lean`

## Status: COMPLETE (0 sorries)

All three theorems proved:
- `prod_sqrt_eq_sqrt_prod` — induction on n
- `diagonal_gaussian` — Fubini + scalar Gaussian
- `multivariate_gaussian_integral` — spectral decomp + orthogonal change of variables

## Proof Architecture

### diagonal_gaussian
```
exp(-∑ bᵢxᵢ²) = ∏ exp(-bᵢxᵢ²)    [Real.exp_sum via Finset.sum_neg_distrib]
∫ ∏ = ∏ ∫                          [integral_fintype_prod_volume_eq_prod]
∫ exp(-bᵢxᵢ²) = √(π/bᵢ)           [GaussianIntegralCircle.scaled_gaussian]
∏ √(π/bᵢ) = √(πⁿ/∏bᵢ)             [prod_sqrt_eq_sqrt_prod + Finset.prod_div_distrib]
```

### multivariate_gaussian_integral
Key steps:
1. `det A = ∏ eigenvalues` via `IsHermitian.det_eq_prod_eigenvalues` + `RCLike.ofReal_real_eq_id`
2. `A = U * diag(λ) * Uᵀ` via `spectral_theorem` + `conjTranspose_eq_transpose_of_trivial`
3. Quadratic form: `xᵀAx = ∑ λᵢ (Uᵀx)ᵢ²` via `dotProduct_mulVec` + `vecMul_transpose` + `mulVec_diagonal`
4. `|det Uᵀ| = 1`: unitary property → `det²=1` via `sq_eq_one_iff` → `|det|=1`
5. `Measure.map L volume = volume` via `map_linearMap_volume_pi_eq_smul_volume_pi`
6. Change of variables via `← integral_map + hmap`
7. Apply `diagonal_gaussian`

## Key Mathlib APIs Used

| API | Purpose |
|-----|---------|
| `Real.map_linearMap_volume_pi_eq_smul_volume_pi` | map L volume = |det L|⁻¹ • volume |
| `MeasureTheory.integral_map` | ∫ g ∂(map L μ) = ∫ g∘L ∂μ |
| `Matrix.det_of_mem_unitary` | det U ∈ unitary ℝ (gives det·star det = 1) |
| `RCLike.ofReal_real_eq_id` | ofReal ∘ λ = λ over ℝ |
| `Matrix.toLin'_apply'` | mulVecLin M = toLin' M (connects to det_toLin') |
| `Matrix.vecMul_transpose` | x ᵥ* M = Mᵀ.mulVec x |
| `sq_eq_one_iff` | a²=1 → a=1 or a=-1 |

## Session 2026-04-22 (Session 1)

**Outcome**: COMPLETE  
**Sorries closed**: 1 (multivariate_gaussian_integral)  
**Key insight**: The change-of-variables step doesn't need a MeasurableEquiv — just
`map_linearMap_volume_pi_eq_smul_volume_pi` (which gives the scalar factor) combined with
`integral_map` (which does the substitution). The measure-preserving proof follows from
|det Uᵀ| = 1 via the unitary group property.

**Pitfalls resolved**:
- `mulVecLin` vs `toLin'`: need `Matrix.toLin'_apply'` to connect them for `det_toLin'`
- `star U` over ℝ: `star_trivial` gives `star r = r`, then `sq_eq_one_iff` for |det|=1
- `RCLike.ofReal ∘ eigenvalues` over ℝ: use `RCLike.ofReal_real_eq_id` (not `simp`)
- Spectral theorem form: `conjStarAlgAut_apply u x = u * x * star u`

## Session 2026-04-22 (Session 2)

**Outcome**: VERIFIED BUILD (0 sorries, clean ✔)
**Key fixes**:
- `Matrix.dotProduct` does NOT exist — `dotProduct` is in root namespace (not `Matrix`). Use `simp only [dotProduct, ...]`
- `fun_prop` cannot prove `AEStronglyMeasurable` for pi-types `Fin n → ℝ`. Fix: use `Continuous.aestronglyMeasurable` + `fun_prop` for continuity
- Docker build script mounts MAIN repo, not worktree. Must run docker-build.sh FROM the worktree directory

**Build output**: `✔ [3154/3154] Built Proofs.AreaOfCircleOQ05OQ02 (3.8s)` — no sorry warnings
