# Knowledge: area-of-circle-oq-05-oq-02

## Key Facts

### Mathematical Setup
- Positive-definite real symmetric A: all eigenvalues λᵢ > 0
- ∫_{ℝⁿ} e^{-xᵀAx} dx = √(πⁿ/det A)
- Proof chain: spectral decomposition → change of variables → Fubini → scalar integral

### Scalar Case (from parent AreaOfCircleOQ05.lean)
- `scaled_gaussian (a : ℝ) (ha : 0 < a) : ∫ x : ℝ, rexp (-(a * x ^ 2)) = √(π / a)`
- This is the building block for the multivariate case via Fubini

### Mathlib APIs Confirmed (Session 2026-04-21)

**Spectral theorem:**
- `Matrix.IsHermitian.spectral_theorem`:
  `A = conjStarAlgAut 𝕜 _ eigenvectorUnitary (diagonal (RCLike.ofReal ∘ eigenvalues))`
- `Matrix.IsHermitian.eigenvectorUnitary : Matrix n n 𝕜` (unitary matrix, star = transpose for ℝ)
- `Matrix.IsHermitian.eigenvalues : n → ℝ`
- `Matrix.PosDef.eigenvalues_pos : A.PosDef → ∀ i, 0 < hA.1.eigenvalues i`
- `Matrix.IsHermitian.det_eq_prod_eigenvalues : det A = ∏ i, (eigenvalues i : 𝕜)`

**Fubini for products:**
- `integral_fintype_prod_volume_eq_prod (f : (i : ι) → E i → 𝕜) :
    ∫ x : (i : ι) → E i, ∏ i, f i (x i) = ∏ i, ∫ x, f i x`
- In `Mathlib.MeasureTheory.Integral.Pi`

**exp factoring:**
- `Real.exp_sum (s : Finset α) (f : α → ℝ) :
    Real.exp (∑ x ∈ s, f x) = ∏ x ∈ s, Real.exp (f x)`
- `← Finset.sum_neg_distrib` rewrites `-(∑ f) → ∑ (-f)` under simp_rw

**Change of variables (to complete):**
- `map_linearMap_volume_pi_eq_smul_volume_pi (hf : LinearMap.det f ≠ 0) :
    Measure.map f volume = ENNReal.ofReal (abs (LinearMap.det f)⁻¹) • volume`
- For orthogonal map (|det| = 1): `Measure.map f volume = volume`
- `MeasurePreserving.integral_comp' (h : MeasurePreserving f μ ν) (g : β → G) :
    ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν`

---

## Session 2026-04-21 (Session 1) - Diagonal Case Proved

**Mode**: FRESH
**Outcome**: progress — diagonal_gaussian proved (0 sorries), main theorem 1 sorry

### What I Did

1. Surveyed Mathlib APIs: spectral theorem, Fubini for ℝⁿ, exp_sum, measure change-of-variables
2. Confirmed `integral_fintype_prod_volume_eq_prod` in `Mathlib.MeasureTheory.Integral.Pi`
3. Confirmed `Fin.prod_univ_castSucc` in `Mathlib.Algebra.BigOperators.Fin`
4. Wrote `proofs/Proofs/AreaOfCircleOQ05OQ02.lean` (139 lines)
5. Proved `prod_sqrt_eq_sqrt_prod` by induction (0 sorries)
6. Proved `diagonal_gaussian` completely via exp_sum + Fubini + scaled_gaussian (0 sorries)
7. Stated `multivariate_gaussian_integral` with 1 sorry (spectral change-of-variables)
8. Created gallery entry `src/data/proofs/area-of-circle-oq-05-oq-02/`

### Key Findings

**diagonal_gaussian proof is clean**: Uses `← Finset.sum_neg_distrib` (from GaussianFourierTransform usage) + `Real.exp_sum` to factor exp(-∑) = ∏ exp(-), then Fubini via `integral_fintype_prod_volume_eq_prod`, then `scaled_gaussian` from parent, then `prod_sqrt_eq_sqrt_prod` + `prod_div_distrib` + `prod_const`.

**Main sorry analysis**: The spectral decomposition step requires:
- Rewriting `dotProduct x (A.mulVec x)` using spectral_theorem
- Showing the change of variables y = (eigenvectorUnitary)ᵀ *ᵥ x is measure-preserving
- This needs `map_linearMap_volume_pi_eq_smul_volume_pi` with |det (eigenvectorUnitary)ᵀ| = 1
- The det = ±1 for unitary matrices; for real symmetric PosDef, det(eigenvectorUnitary) ∈ {±1}

**Key challenge**: Constructing a `MeasurableEquiv` from the linear map `(eigenvectorUnitary)ᵀ *ᵥ·` to use `MeasurePreserving.integral_comp'`. The linear map IS measurable and is a bijection, so this should be possible via `LinearEquiv.measurePreserving` or `ContinuousLinearEquiv.measurePreserving`.

### Files Modified
- `proofs/Proofs/AreaOfCircleOQ05OQ02.lean` (created, 139 lines, 1 sorry)
- `src/data/proofs/area-of-circle-oq-05-oq-02/` (gallery entry created)
- `src/data/proofs/listings.json` (entry added)
- `src/data/research/problems/area-of-circle-oq-05-oq-02.json` (updated knowledge)

### Next Steps
1. Find `ContinuousLinearEquiv.measurePreserving` or `LinearEquiv.measurePreserving` to build the MeasurableEquiv
2. Show `Matrix.IsHermitian.eigenvectorUnitary` is a ContinuousLinearEquiv when restricted to ℝ
3. Prove det = ±1 for eigenvectorUnitary — use `Matrix.unitaryGroup.det_apply` or similar
4. Complete the quadratic form rewriting: xᵀAx = ∑ λᵢ (Uᵀx)ᵢ² via spectral_theorem
