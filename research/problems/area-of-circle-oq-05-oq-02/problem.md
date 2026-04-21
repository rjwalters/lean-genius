# Problem: Multivariate Gaussian Integral via Matrix Diagonalization

**Slug**: area-of-circle-oq-05-oq-02
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-extension

## Problem Statement

### Plain Language

The gallery proof `AreaOfCircleOQ05.lean` establishes the scalar Gaussian integral
∫_{ℝ} e^{-x²} dx = √π. This open question asks:

**Can the multivariate Gaussian integral be formalized in Lean 4?**

Specifically: for a positive-definite real symmetric matrix A of size n×n,

    ∫_{ℝⁿ} exp(-xᵀAx) dx = √(πⁿ / det(A))

### Formal Statement

```lean
theorem multivariate_gaussian_integral (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) :
    ∫ x : Fin n → ℝ, Real.exp (-(Matrix.dotProduct x (A.mulVec x))) =
      Real.sqrt (Real.pi ^ n / A.det) := by
  -- Diagonalize A = QᵀDQ via spectral theorem
  -- Apply change of variables y = Q x
  -- Use Fubini: ∫ e^{-λ₁y₁²} ... e^{-λₙyₙ²} = ∏ √(π/λᵢ)
  -- Combine: ∏ √(π/λᵢ) = √(πⁿ/∏λᵢ) = √(πⁿ/det A)
  sorry
```

### Why This Matters

- Natural generalization of the scalar Gaussian in `AreaOfCircleOQ05.lean`
- Used in probability theory (multivariate normal distribution), statistics, quantum mechanics
- Requires spectral theorem + Fubini + measure theory on ℝⁿ — substantial Mathlib coverage
- Tractability 7/10: all the ingredients likely exist in Mathlib

## Known Results

### From Parent Proof (`AreaOfCircleOQ05.lean`)
- `gaussian_integral_eq_sqrt_pi`: ∫_{ℝ} e^{-x²} dx = √π (proved)
- Scalar case: ∫ e^{-ax²} dx = √(π/a) for a > 0 (derivable from scaling)

### Mathematical Facts

1. **Spectral theorem**: Symmetric positive-definite A = QᵀDQ where Q orthogonal,
   D = diag(λ₁, ..., λₙ) with all λᵢ > 0
2. **Change of variables**: y = Qx, Jacobian = |det Q| = 1 (Q orthogonal)
3. **Fubini**: ∫_{ℝⁿ} e^{-yᵀDy} dy = ∫_{ℝⁿ} ∏ᵢ e^{-λᵢyᵢ²} dy = ∏ᵢ ∫_{ℝ} e^{-λᵢyᵢ²} dyᵢ
4. **Scalar integral**: ∫ e^{-λy²} dy = √(π/λ)
5. **Product**: ∏ᵢ √(π/λᵢ) = √(πⁿ / ∏λᵢ) = √(πⁿ / det A)

### Lean 4 / Mathlib Status
- `Matrix.PosDef`: positive-definite matrices — in Mathlib
- `Matrix.IsSymm`: symmetric matrices — in Mathlib
- Spectral theorem for real symmetric matrices: `Matrix.IsSymm.eigenvectorMatrix` — verify in Mathlib
- `MeasureTheory.integral_comp_mul_right`: change of variables in integrals — check
- `MeasureTheory.Fubini`: product integrals — in Mathlib
- `Matrix.det_diagonal`: determinant of diagonal matrix — in Mathlib

## Suggested Approach

### Phase 1: OBSERVE
1. Read `AreaOfCircleOQ05.lean` to understand the scalar integral formalization
2. Check `Mathlib.LinearAlgebra.Matrix.PosDef` for spectral theorem access
3. Search for `Matrix.IsHermitian.eigenvectorMatrix` or similar
4. Check `MeasureTheory.volume_comp_linearMap` for orthogonal change of variables

### Phase 2: ORIENT
1. Can the spectral theorem in Mathlib give us Q and D explicitly?
2. Is there an `OrthogonalGroup` action on measures?
3. Does `MeasureTheory.Fubini` work cleanly for ℝⁿ as `Fin n → ℝ`?

### Phase 3: DECIDE
1. If spectral theorem path works: full proof via Q, D, Fubini
2. Simpler: prove only for diagonal A first, then generalize
3. Alternative: induction on n using Fubini to peel off one variable at a time

### Phase 4: ACT

```lean
-- Step 1: Diagonal case
theorem multivariate_gaussian_diagonal (n : ℕ) (λ : Fin n → ℝ) (hλ : ∀ i, 0 < λ i) :
    ∫ x : Fin n → ℝ, Real.exp (-∑ i, λ i * x i ^ 2) =
      Real.sqrt (Real.pi ^ n / ∏ i, λ i) := by
  rw [show (-∑ i, λ i * x i ^ 2) = ...]
  rw [Real.exp_sum]
  rw [integral_fintype_prod]
  simp [gaussian_integral_eq_sqrt_pi]

-- Step 2: General case via spectral theorem
```

## Related Gallery Proofs

- `area-of-circle-oq-05`: Parent — scalar Gaussian integral
- `erdos-1151-oq-04`: Related — uses similar analysis/measure theory infrastructure
- `central-limit-theorem`: Uses multivariate Gaussian in its statement

## Quality Assessment

- **Tractability**: 7/10 — clear mathematical path, good Mathlib coverage
- **Significance**: 7/10 — fundamental result in probability theory
- **Domain**: Analysis / probability / linear algebra
- **Risk**: Low-medium — spectral theorem availability is the main uncertainty
