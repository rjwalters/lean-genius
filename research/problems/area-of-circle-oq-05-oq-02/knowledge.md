# Knowledge: area-of-circle-oq-05-oq-02

## Key Facts

### Mathematical Setup
- Positive-definite real symmetric A: all eigenvalues λᵢ > 0
- ∫_{ℝⁿ} e^{-xᵀAx} dx = √(πⁿ/det A)
- Proof chain: spectral decomposition → change of variables → Fubini → scalar integral

### Scalar Case (from parent)
- ∫_{ℝ} e^{-ax²} dx = √(π/a) for a > 0
- This is the building block for the multivariate case via Fubini

### Spectral Theorem (to verify in Mathlib)
- `Matrix.IsHermitian`: real symmetric matrices have real eigenvalues
- `Matrix.IsHermitian.eigenvectorMatrix`: Q such that Q^T A Q = D (diagonal)
- `Matrix.IsHermitian.spectral_theorem`: A = Q D Q^T (spectral decomposition)
- Need: Q is orthogonal (Q^T Q = I)

### Change of Variables
- y = Qx, |det Q| = 1 (orthogonal matrix)
- `MeasureTheory.MeasurePreserving` for orthogonal transformations?
- `MeasureTheory.integral_comp_mul_right`: f(Ax) substitution

### Fubini
- `MeasureTheory.integral_prod`: for product measures
- For `Fin n → ℝ`, the product measure decomposes as ∏ᵢ (Lebesgue on ℝ)
- `MeasureTheory.Measure.pi`: product measure on `Fin n → ℝ`

### Determinant
- `Matrix.det_diagonal`: det(diag(λ₁,...,λₙ)) = ∏ λᵢ
- `Matrix.PosDef.det_pos`: det A > 0 for positive-definite A
- `Real.sqrt_mul`: √(πⁿ/det A) = ∏ᵢ √(π/λᵢ) via eigenvalues

## Open Questions
- Does Mathlib have spectral theorem in a form usable for change-of-variables?
- Is there a `MeasurePreserving` lemma for orthogonal linear maps?
- How is `Fin n → ℝ` measure handled — `EuclideanSpace` or `Fin n → ℝ`?

## References
- Parent proof: `proofs/Proofs/AreaOfCircleOQ05.lean`
- `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Mathlib.MeasureTheory.Integral.Bochner`
- `Mathlib.MeasureTheory.Measure.Haar.Basic`
