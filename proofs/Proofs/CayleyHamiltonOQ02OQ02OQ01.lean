import Mathlib
import Proofs.CayleyHamiltonOQ02OQ02

/-
# Spectral Consequences of Sylvester's Interpolation Formula
# (cayley-hamilton-oq-02-oq-02-oq-01)

Follow-up to `CayleyHamiltonOQ02OQ02` (Sylvester interpolation via Frobenius covariants).

The parent file establishes **Sylvester's formula** for a diagonalizable matrix
`A = U · diagonal d · V` (with `U V = V U = 1`):

  `aeval A p = ∑_μ p.eval μ · Z_μ`,   `Z_μ = frobeniusCovariant U V d μ`,

together with the projection algebra of the Frobenius covariants `Z_μ`
(`Z_μ² = Z_μ`, `Z_μ Z_ν = 0`, `∑ Z_μ = 1`, `A Z_μ = μ Z_μ`). It does not, however,
record what the formula *says* about `A` itself. This entry draws those spectral
consequences out:

1. `spectral_decomposition` — **`A = ∑_μ μ · Z_μ`**: the matrix is the
   eigenvalue-weighted sum of its own spectral projections (Sylvester at `p = X`).

2. `pow_eq_sum_frobenius` — **spectral mapping for powers** `Aᵏ = ∑_μ μᵏ · Z_μ`
   (Sylvester at `p = Xᵏ`): raising `A` to a power re-weights the *same* fixed
   projections by `μᵏ`.

3. `aeval_eq_of_eval_eq` — **interpolation uniqueness**: the functional calculus
   `aeval A p` depends on `p` only through its values `p.eval μ` on the eigenvalues;
   two polynomials agreeing on the spectrum give the same matrix.

4. `frobenius_eigen_right` / `frobenius_commute` — the covariants are *two-sided*
   eigen-projections: `Z_μ A = μ Z_μ` as well as `A Z_μ = μ Z_μ`, so each `Z_μ`
   commutes with `A`.

## Summary: 0 sorries, 0 axioms, no `native_decide`. Builds on the verified parent.
-/

set_option linter.unusedSectionVars false

namespace CayleyHamiltonOQ02OQ02OQ01

open Matrix Polynomial Finset
open CayleyHamiltonOQ02OQ02

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [CommRing 𝕜] [DecidableEq 𝕜]

-- ============================================================
-- PART 1: A and its powers as eigenvalue-weighted sums of projections
-- ============================================================

/-- **Spectral decomposition of a diagonalizable matrix.** `A = ∑_μ μ · Z_μ`: the
matrix `A = U · diagonal d · V` is the eigenvalue-weighted sum of its Frobenius
covariants. This is Sylvester's formula applied to `p = X`. -/
theorem spectral_decomposition (U V : Matrix n n 𝕜) (hUV : U * V = 1) (hVU : V * U = 1)
    (d : n → 𝕜) :
    U * diagonal d * V
      = ∑ μ ∈ Finset.univ.image d, μ • frobeniusCovariant U V d μ := by
  have h := sylvester U V hUV hVU d X
  simpa using h

/-- **Spectral mapping for powers.** `Aᵏ = ∑_μ μᵏ · Z_μ`: powers of `A` re-weight
the *same* fixed spectral projections by `μᵏ`. This is Sylvester's formula applied
to `p = Xᵏ`. -/
theorem pow_eq_sum_frobenius (U V : Matrix n n 𝕜) (hUV : U * V = 1) (hVU : V * U = 1)
    (d : n → 𝕜) (k : ℕ) :
    (U * diagonal d * V) ^ k
      = ∑ μ ∈ Finset.univ.image d, μ ^ k • frobeniusCovariant U V d μ := by
  have h := sylvester U V hUV hVU d (X ^ k)
  simpa [map_pow] using h

-- ============================================================
-- PART 2: Interpolation uniqueness — f(A) depends only on f on the spectrum
-- ============================================================

/-- **Interpolation uniqueness.** The functional calculus `aeval A p` depends on `p`
only through its values `p.eval μ` on the eigenvalues: if `p` and `q` agree on every
eigenvalue of `A`, then `aeval A p = aeval A q`. -/
theorem aeval_eq_of_eval_eq (U V : Matrix n n 𝕜) (hUV : U * V = 1) (hVU : V * U = 1)
    (d : n → 𝕜) (p q : 𝕜[X])
    (h : ∀ μ ∈ Finset.univ.image d, p.eval μ = q.eval μ) :
    aeval (U * diagonal d * V) p = aeval (U * diagonal d * V) q := by
  rw [sylvester U V hUV hVU d p, sylvester U V hUV hVU d q]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [h μ hμ]

-- ============================================================
-- PART 3: The covariants are two-sided eigen-projections
-- ============================================================

/-- Multiplying a coordinate projection by the diagonal matrix on the *right* scales
it by the eigenvalue: `E_μ · diagonal d = μ • E_μ` (diagonal matrices commute). -/
theorem coordProj_mul_diag (d : n → 𝕜) (μ : 𝕜) :
    coordProj d μ * diagonal d = μ • coordProj d μ := by
  unfold coordProj
  rw [diagonal_mul_diagonal, ← diagonal_smul]
  congr 1
  funext i
  by_cases h : d i = μ <;> simp [h, Pi.smul_apply, smul_eq_mul]

/-- **The covariants are right eigen-projections too.** `Z_μ · A = μ · Z_μ`, the
right-hand companion to the parent's `A · Z_μ = μ · Z_μ`. -/
theorem frobenius_eigen_right (U V : Matrix n n 𝕜) (hVU : V * U = 1) (d : n → 𝕜) (μ : 𝕜) :
    frobeniusCovariant U V d μ * (U * diagonal d * V) = μ • frobeniusCovariant U V d μ := by
  unfold frobeniusCovariant
  calc U * coordProj d μ * V * (U * diagonal d * V)
      = U * coordProj d μ * (V * U) * diagonal d * V := by noncomm_ring
    _ = U * coordProj d μ * 1 * diagonal d * V := by rw [hVU]
    _ = U * (coordProj d μ * diagonal d) * V := by noncomm_ring
    _ = U * (μ • coordProj d μ) * V := by rw [coordProj_mul_diag]
    _ = μ • (U * coordProj d μ * V) := by rw [mul_smul_comm, smul_mul_assoc]

/-- **Each Frobenius covariant commutes with `A`.** `A · Z_μ = Z_μ · A`, both equal to
`μ · Z_μ`: the spectral projections are intrinsic and commute with the matrix. -/
theorem frobenius_commute (U V : Matrix n n 𝕜) (hVU : V * U = 1) (d : n → 𝕜) (μ : 𝕜) :
    (U * diagonal d * V) * frobeniusCovariant U V d μ
      = frobeniusCovariant U V d μ * (U * diagonal d * V) := by
  rw [frobenius_eigen U V hVU d μ, frobenius_eigen_right U V hVU d μ]

/-
## Significance

Sylvester's interpolation formula `f(A) = ∑_λ f(λ) Z_λ` packages the entire
functional calculus of a diagonalizable matrix into a fixed family of spectral
projections, the Frobenius covariants `Z_λ`. The parent entry proves the formula
and the projection algebra; this entry reads off what it means for `A`.

Taking `f = X` recovers the **spectral decomposition** `A = ∑_λ λ Z_λ`
(`spectral_decomposition`), and `f = Xᵏ` gives the **spectral mapping theorem for
powers** `Aᵏ = ∑_λ λᵏ Z_λ` (`pow_eq_sum_frobenius`) — powers act by re-weighting the
*same* projections. The formula's dependence on `f` only through the eigenvalue
samples `f(λ)` is the **interpolation-uniqueness** principle `aeval_eq_of_eval_eq`,
the algebraic shadow of Lagrange interpolation. Finally the covariants are genuine
two-sided eigen-projections (`frobenius_eigen_right`, `frobenius_commute`): they
commute with `A`, confirming they are intrinsic spectral data. Everything is
verified from the parent's results, with no axioms.
-/

end CayleyHamiltonOQ02OQ02OQ01
