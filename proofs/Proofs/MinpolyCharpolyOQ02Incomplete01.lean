/-
# Diagonalizable Matrices — OQ-02 / closure properties of `Matrix.IsDiagonalizable`

The parent `MinpolyCharpolyOQ02` introduces the predicate

    `Matrix.IsDiagonalizable M := ∃ P, IsUnit P ∧ IsDiag (P⁻¹ * M * P)`

(`M` is similar to a diagonal matrix), proves the forward direction of the
diagonalizability characterisation, and records the trivial instances
(`zero`, `one`, `diagonal`, `of_isDiag`).  The substantive *reverse* direction
(squarefree minpoly ⇒ diagonalizable) is the parent's sole open obligation and is
not touched here.

This file fills in the **closure properties** of `IsDiagonalizable` — the
elementary algebraic stability laws that every textbook states immediately after
the definition but which the parent omits:

  * `IsDiagonalizable.conj`      — **similarity invariance**: if `M` is
    diagonalizable and `U` is invertible, so is the conjugate `U⁻¹ M U`.  This is
    the defining feature of diagonalizability as a property of the *operator*,
    not the matrix representative.
  * `IsDiagonalizable.smul`      — scalar multiples `c • M` stay diagonalizable
    (same diagonalizing `P`; the conjugate scales).
  * `IsDiagonalizable.neg`       — `-M` stays diagonalizable.
  * `IsDiagonalizable.transpose` — the transpose `Mᵀ` is diagonalizable, with
    diagonalizer `(Pᵀ)⁻¹` (eigenvalues are preserved under transpose).
  * `IsDiagonalizable.inv`       — the inverse `M⁻¹` is diagonalizable (same `P`),
    because `P⁻¹ M⁻¹ P = (P⁻¹ M P)⁻¹` and the inverse of a diagonal matrix is
    diagonal (`isDiag_inv`).
  * `IsDiagonalizable.pow`       — every power `Mᵏ` is diagonalizable (same `P`),
    because `P⁻¹ Mᵏ P = (P⁻¹ M P)ᵏ` (`conj_pow`) and powers of a diagonal matrix
    are diagonal (`isDiag_pow`, built on `isDiag_mul`).

All are fully machine-checked (0 axioms, 0 sorries) and reuse only the
parent's *definition* (not its open reverse-direction obligation).

Reference: Axler, *Linear Algebra Done Right* §5–8; Dummit–Foote §12.
-/

import Mathlib
import Proofs.MinpolyCharpoly
import Proofs.MinpolyCharpolyOQ02

namespace MinpolyCharpolyOQ02Incomplete01

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- **Similarity invariance.**  If `M` is diagonalizable and `U` is invertible,
    then the conjugate `U⁻¹ * M * U` is diagonalizable.  Diagonalizing `M` with
    `P` (so `P⁻¹ M P` is diagonal), the matrix `U⁻¹ P` diagonalizes `U⁻¹ M U`. -/
theorem IsDiagonalizable.conj {M : Matrix n n K} (hM : M.IsDiagonalizable)
    {U : Matrix n n K} (hU : IsUnit U) :
    (U⁻¹ * M * U).IsDiagonalizable := by
  obtain ⟨P, hP, hD⟩ := hM
  have hUdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hU
  have hUinv : IsUnit U⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hU
  refine ⟨U⁻¹ * P, hUinv.mul hP, ?_⟩
  have hQinv : (U⁻¹ * P)⁻¹ = P⁻¹ * U := by
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv U hUdet]
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hUdet
  have hsimp : (U⁻¹ * P)⁻¹ * (U⁻¹ * M * U) * (U⁻¹ * P) = P⁻¹ * M * P := by
    rw [hQinv]
    calc P⁻¹ * U * (U⁻¹ * M * U) * (U⁻¹ * P)
        = P⁻¹ * (U * U⁻¹) * M * (U * U⁻¹) * P := by simp only [mul_assoc]
      _ = P⁻¹ * M * P := by rw [hUU]; simp only [mul_one]
  rw [hsimp]
  exact hD

/-- **Scalar multiples stay diagonalizable.**  The same `P` diagonalizes `c • M`,
    since `P⁻¹ (c • M) P = c • (P⁻¹ M P)` is again diagonal. -/
theorem IsDiagonalizable.smul {M : Matrix n n K} (hM : M.IsDiagonalizable) (c : K) :
    (c • M).IsDiagonalizable := by
  obtain ⟨P, hP, hD⟩ := hM
  refine ⟨P, hP, ?_⟩
  have h : P⁻¹ * (c • M) * P = c • (P⁻¹ * M * P) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [h]
  exact IsDiag.smul c hD

/-- **Negation stays diagonalizable.** -/
theorem IsDiagonalizable.neg {M : Matrix n n K} (hM : M.IsDiagonalizable) :
    (-M).IsDiagonalizable := by
  obtain ⟨P, hP, hD⟩ := hM
  refine ⟨P, hP, ?_⟩
  have h : P⁻¹ * (-M) * P = -(P⁻¹ * M * P) := by
    rw [Matrix.mul_neg, Matrix.neg_mul]
  rw [h]
  exact hD.neg

/-- **The transpose is diagonalizable.**  If `P⁻¹ M P` is diagonal then
    `((Pᵀ)⁻¹)⁻¹ Mᵀ (Pᵀ)⁻¹ = (P⁻¹ M P)ᵀ` is diagonal, so `(Pᵀ)⁻¹` diagonalizes
    `Mᵀ`. -/
theorem IsDiagonalizable.transpose {M : Matrix n n K} (hM : M.IsDiagonalizable) :
    (Mᵀ).IsDiagonalizable := by
  obtain ⟨P, hP, hD⟩ := hM
  have hPt : IsUnit (Pᵀ) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPtdet : IsUnit (Pᵀ).det := (Matrix.isUnit_iff_isUnit_det _).mp hPt
  refine ⟨(Pᵀ)⁻¹, Matrix.isUnit_nonsing_inv_iff.mpr hPt, ?_⟩
  have heq : (Pᵀ)⁻¹⁻¹ * Mᵀ * (Pᵀ)⁻¹ = (P⁻¹ * M * P)ᵀ := by
    rw [Matrix.nonsing_inv_nonsing_inv _ hPtdet, ← Matrix.transpose_nonsing_inv]
    simp only [Matrix.transpose_mul, mul_assoc]
  rw [heq]
  exact hD.transpose

/-- **The inverse of a diagonal matrix is diagonal.**  Writing `A = diagonal (diag A)`
    (valid because `A` is diagonal), `Matrix.inv_diagonal` gives
    `A⁻¹ = diagonal (Ring.inverse (diag A))`, which is again diagonal. -/
theorem isDiag_inv {A : Matrix n n K} (h : A.IsDiag) : A⁻¹.IsDiag := by
  rw [show A⁻¹ = (diagonal (diag A))⁻¹ by rw [h.diagonal_diag], Matrix.inv_diagonal]
  exact Matrix.isDiag_diagonal _

/-- **The inverse of a diagonalizable matrix is diagonalizable.**  The *same* `P`
    diagonalizes `M⁻¹`: since `P⁻¹ M⁻¹ P = (P⁻¹ M P)⁻¹` and the inverse of a diagonal
    matrix is diagonal (`isDiag_inv`), `P⁻¹ M⁻¹ P` is diagonal.  (No invertibility
    hypothesis on `M` is needed: if `M` is singular then `M⁻¹` is the junk value `0`,
    which is trivially diagonalizable, and the identity `P⁻¹ M⁻¹ P = (P⁻¹ M P)⁻¹`
    still holds for Mathlib's `nonsing_inv`.) -/
theorem IsDiagonalizable.inv {M : Matrix n n K} (hM : M.IsDiagonalizable) :
    M⁻¹.IsDiagonalizable := by
  obtain ⟨P, hP, hD⟩ := hM
  refine ⟨P, hP, ?_⟩
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have key : (P⁻¹ * M * P)⁻¹ = P⁻¹ * M⁻¹ * P := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv P hPdet,
      ← mul_assoc]
  rw [← key]
  exact isDiag_inv hD

/-- **The product of two diagonal matrices is diagonal.**  Off the diagonal
    (`i ≠ j`), every term `A i k * B k j` of `(A * B) i j = ∑ₖ A i k * B k j`
    vanishes: if `k ≠ i` then `A i k = 0`, and if `k = i` then `B k j = B i j = 0`
    (since `i ≠ j`). -/
theorem isDiag_mul {A B : Matrix n n K} (hA : A.IsDiag) (hB : B.IsDiag) :
    (A * B).IsDiag := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rcases eq_or_ne i k with rfl | hik
  · rw [hB hij, mul_zero]
  · rw [hA hik, zero_mul]

/-- **Powers of a diagonal matrix are diagonal.**  Immediate induction on the
    exponent: `A⁰ = 1` is diagonal and `Aᵏ⁺¹ = Aᵏ * A` is a product of diagonals. -/
theorem isDiag_pow {A : Matrix n n K} (h : A.IsDiag) (k : ℕ) : (A ^ k).IsDiag := by
  induction k with
  | zero => rw [pow_zero]; exact Matrix.isDiag_one
  | succ k ih => rw [pow_succ]; exact isDiag_mul ih h

/-- **Conjugation commutes with taking powers.**  For invertible `P`,
    `P⁻¹ Mᵏ P = (P⁻¹ M P)ᵏ`.  Proof by induction, cancelling the interior
    `P * P⁻¹ = 1` at each step. -/
theorem conj_pow {M P : Matrix n n K} (hP : IsUnit P.det) (k : ℕ) :
    P⁻¹ * M ^ k * P = (P⁻¹ * M * P) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, mul_one, Matrix.nonsing_inv_mul P hP]
  | succ k ih =>
      have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
      rw [pow_succ, pow_succ, ← ih]
      have hcollapse : P⁻¹ * M ^ k * P * (P⁻¹ * M * P)
          = P⁻¹ * M ^ k * (P * P⁻¹) * (M * P) := by simp only [mul_assoc]
      rw [hcollapse, hPP]
      simp only [mul_one, mul_assoc]

/-- **Powers stay diagonalizable.**  The *same* `P` diagonalizes `Mᵏ`: since
    `P⁻¹ Mᵏ P = (P⁻¹ M P)ᵏ` (`conj_pow`) and powers of the diagonal matrix
    `P⁻¹ M P` are diagonal (`isDiag_pow`), `P⁻¹ Mᵏ P` is diagonal.  Completes the
    documented `nextSteps` item on powers of a diagonalizable matrix. -/
theorem IsDiagonalizable.pow {M : Matrix n n K} (hM : M.IsDiagonalizable) (k : ℕ) :
    (M ^ k).IsDiagonalizable := by
  obtain ⟨P, hP, hD⟩ := hM
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  refine ⟨P, hP, ?_⟩
  rw [conj_pow hPdet]
  exact isDiag_pow hD k

end MinpolyCharpolyOQ02Incomplete01
