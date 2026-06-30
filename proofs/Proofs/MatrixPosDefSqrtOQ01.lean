/-
  The positive semidefinite square root of a matrix: existence, structure,
  and uniqueness.

  Every positive semidefinite matrix `A` over `𝕜 = ℝ` or `ℂ` (`RCLike 𝕜`) has a
  positive semidefinite square root.  Modern Mathlib supplies it through the
  continuous functional calculus as `CFC.sqrt A` (the matrix-specific
  `Matrix.PosSemidef.sqrt` was deprecated in favour of this C⋆-algebra version),
  and the relevant Loewner-order instances on `Matrix n n 𝕜` are the scoped
  `MatrixOrder` instances, under which `0 ≤ A ↔ A.PosSemidef`.

  The gallery had no entry on the operator square root (it is a different object
  from the Gram/positive-definite material and from the determinant identities).
  The substantive content packaged here is the full characterization:

    * **Defining property.**  `√A · √A = A` (equivalently `(√A)^2 = A`).

    * **Structure.**  `√A` is again positive semidefinite, and in particular
      Hermitian — the square root stays inside the cone.

    * **Uniqueness.**  `√A` is the *only* positive semidefinite `B` with
      `B · B = A`.  This is the non-trivial half: it is what makes "the" square
      root well defined and powers the corollaries below.

    * **Corollaries from uniqueness.**  `√0 = 0`, `√1 = 1`, and `√(A^2) = A`
      for PSD `A` — each is the uniqueness statement applied to an obvious
      candidate.

    * **Determinant shadow.**  `det(√A)^2 = det A`: the square root halves the
      determinant in the multiplicative sense (so `det A ≥ 0` is visible as a
      square).

    * **Concrete instance.**  `√ diag(4, 9) = diag(2, 3)`, computed from
      uniqueness, cross-checking the abstract functional-calculus definition
      against an elementary entrywise square root.

  The PSD square root underlies the polar decomposition `A = (PSD)·(unitary)`,
  the operator absolute value `|A| = √(Aᴴ A)`, and the whitening transform in
  statistics.

  Verified: 0 sorries, 0 axioms beyond the foundational `propext` /
  `Classical.choice` / `Quot.sound`; no `native_decide`, no `Lean.ofReduceBool`.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

open Matrix
open scoped MatrixOrder ComplexOrder

namespace MatrixPosDefSqrtOQ01

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Defining property: `√A` is a square root of `A` -/

/-- The defining property of the square root: `√A · √A = A` for PSD `A`. -/
theorem sqrt_mul_self (A : Matrix n n 𝕜) (hA : A.PosSemidef) :
    CFC.sqrt A * CFC.sqrt A = A :=
  CFC.sqrt_mul_sqrt_self A hA.nonneg

/-- Equivalent statement of the defining property as a power: `(√A)^2 = A`. -/
theorem sq_sqrt (A : Matrix n n 𝕜) (hA : A.PosSemidef) :
    CFC.sqrt A ^ 2 = A :=
  CFC.sq_sqrt A hA.nonneg

/-! ### Structure: the square root stays in the PSD cone -/

/-- The square root of any matrix is positive semidefinite.  (No hypothesis on
`A` is needed: `CFC.sqrt` is defined via the `ℝ≥0` functional calculus, so its
output is unconditionally nonnegative.) -/
theorem sqrt_posSemidef (A : Matrix n n 𝕜) :
    (CFC.sqrt A).PosSemidef :=
  (CFC.sqrt_nonneg A).posSemidef

/-- The square root is Hermitian (a special case of being positive
semidefinite). -/
theorem sqrt_isHermitian (A : Matrix n n 𝕜) :
    (CFC.sqrt A).IsHermitian :=
  (sqrt_posSemidef A).isHermitian

/-! ### Uniqueness: `√A` is the unique PSD square root -/

/-- **Uniqueness of the positive semidefinite square root.**  If `B` is positive
semidefinite and `B · B = A`, then `B` *is* the square root `√A`.  Combined with
`sqrt_mul_self` and `sqrt_posSemidef`, this says the PSD square root exists and
is unique. -/
theorem sqrt_unique (A B : Matrix n n 𝕜) (hB : B.PosSemidef) (h : B * B = A) :
    CFC.sqrt A = B :=
  CFC.sqrt_unique h hB.nonneg

/-! ### Corollaries from uniqueness -/

/-- `√0 = 0`: apply uniqueness to the candidate `B = 0`. -/
theorem sqrt_zero : CFC.sqrt (0 : Matrix n n 𝕜) = 0 :=
  sqrt_unique 0 0 .zero (by simp)

/-- `√1 = 1`: apply uniqueness to the candidate `B = 1`. -/
theorem sqrt_one : CFC.sqrt (1 : Matrix n n 𝕜) = 1 :=
  sqrt_unique 1 1 .one (by simp)

/-- `√(A^2) = A` for positive semidefinite `A`: the square root inverts squaring
on the PSD cone.  This is uniqueness applied to the candidate `B = A`. -/
theorem sqrt_sq (A : Matrix n n 𝕜) (hA : A.PosSemidef) :
    CFC.sqrt (A ^ 2) = A :=
  sqrt_unique (A ^ 2) A hA (by rw [pow_two])

/-! ### Determinant shadow -/

/-- The determinant of the square root squares back to the determinant of `A`:
`det(√A)^2 = det A`.  In particular `det A` is a square of `det √A`, exhibiting
`det A ≥ 0` for real PSD matrices. -/
theorem det_sqrt_sq (A : Matrix n n 𝕜) (hA : A.PosSemidef) :
    (CFC.sqrt A).det ^ 2 = A.det := by
  rw [← Matrix.det_pow, sq_sqrt A hA]

/-! ### Concrete instance -/

/-- The candidate square root `diag(2, 3)` is positive semidefinite. -/
theorem diag_two_three_posSemidef :
    (diagonal ![(2 : ℝ), 3]).PosSemidef :=
  Matrix.PosSemidef.diagonal (by
    rw [Pi.le_def]
    intro i
    fin_cases i <;> norm_num [cons_val_zero, cons_val_one, head_cons])

/-- **Concrete computation.**  The square root of the diagonal matrix
`diag(4, 9)` is `diag(2, 3)`, obtained from uniqueness: `diag(2,3)` is PSD and
squares to `diag(4,9)`.  This cross-checks the abstract `CFC.sqrt` against the
elementary entrywise square root `√4 = 2`, `√9 = 3`. -/
theorem sqrt_diag_four_nine :
    CFC.sqrt (diagonal ![(4 : ℝ), 9]) = diagonal ![(2 : ℝ), 3] :=
  sqrt_unique _ _ diag_two_three_posSemidef (by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> norm_num [Pi.mul_apply, cons_val_zero, cons_val_one, head_cons])

end MatrixPosDefSqrtOQ01
