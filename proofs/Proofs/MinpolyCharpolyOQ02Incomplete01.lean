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

All four are fully machine-checked (0 axioms, 0 sorries) and reuse only the
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
      _ = P⁻¹ * M * P := by rw [hUU]; simp only [mul_one, one_mul]
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

end MinpolyCharpolyOQ02Incomplete01
