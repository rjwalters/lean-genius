/-
  Aristotle targets for Multivariate Gaussian Integral (AreaOfCircleOQ05OQ02)
  Routine supporting lemmas for automated proof search.
  See AreaOfCircleOQ05OQ02.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main theorem (multivariate_gaussian_integral is fully proved modulo hquad)
  - hquad is a HARD known result (quadratic form rewrite via spectral theorem)
  - Known proof exists: A = U diag(λ) U*, then xᵀAx = (U*x)ᵀ diag(λ) (U*x) = ∑ λᵢ (U*x)ᵢ²
  - No axioms or definition sorries
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Determinant

namespace MultivariateGaussian.Aristotle

open MeasureTheory Real Matrix Finset

/-!
## hquad: Quadratic form rewrite via spectral theorem

For a positive-definite real symmetric matrix A with spectral decomposition A = U diag(λ) U*,
prove that xᵀAx = ∑ᵢ λᵢ · (Uᵀx)ᵢ².

Key tools needed:
- `IsHermitian.spectral_theorem`: A = conjStarAlgAut 𝕜 _ hH.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ λ))
- `dotProduct_mulVec`: x ⬝ᵥ (A *ᵥ x) = (Aᵀ *ᵥ x) ⬝ᵥ x
- `mulVec_diagonal`: (diagonal v) *ᵥ w = fun i => v i * w i
-/

/-- For a positive-definite real symmetric matrix A, with
    UT = star (eigenvectorUnitary A) (the conjugate transpose of the eigenvector unitary),
    the quadratic form satisfies xᵀAx = ∑ᵢ λᵢ · (UT *ᵥ x)ᵢ²

    where λᵢ = eigenvalues of A (all positive by PosDef). -/
theorem hquad_of_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    let hH := hA.isHermitian
    let UT : Matrix (Fin n) (Fin n) ℝ :=
      star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    ∀ x : Fin n → ℝ,
      dotProduct x (A.mulVec x) = ∑ i : Fin n, hH.eigenvalues i * (UT *ᵥ x) i ^ 2 := by
  classical
  intro hH UT x
  sorry

end MultivariateGaussian.Aristotle
