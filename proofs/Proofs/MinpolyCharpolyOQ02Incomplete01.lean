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

/-- **A finite sum of diagonal matrices is diagonal.**  Pointwise off the
    diagonal every summand vanishes, so does their sum. -/
theorem isDiag_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix n n K)
    (h : ∀ i ∈ s, (A i).IsDiag) : (∑ i ∈ s, A i).IsDiag := by
  intro r c hrc
  rw [Matrix.sum_apply]
  exact Finset.sum_eq_zero fun i hi => h i hi hrc

/-- **Polynomial closure — the capstone law.**  For *any* polynomial `q : K[X]`,
    the matrix `q(M) = aeval M q` is diagonalizable whenever `M` is, with the
    *same* diagonalizer `P`.  Indeed
    `P⁻¹ · q(M) · P = ∑ᵢ qᵢ · (P⁻¹ M P)ⁱ` (distributing the conjugation through
    the polynomial and applying `conj_pow` term-by-term), and each summand
    `qᵢ · (P⁻¹ M P)ⁱ` is diagonal (`isDiag_pow` + scaling), hence so is the sum.

    This subsumes the earlier `IsDiagonalizable.pow` (`q = Xᵏ`),
    `IsDiagonalizable.smul` (`q = C c · X`), `IsDiagonalizable.neg` (`q = -X`),
    and the spectral shift `M + c·1` (`q = X + C c`) in one statement. -/
theorem IsDiagonalizable.aeval {M : Matrix n n K} (hM : M.IsDiagonalizable)
    (q : Polynomial K) : ((Polynomial.aeval M) q).IsDiagonalizable := by
  obtain ⟨P, hP, hD⟩ := hM
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  refine ⟨P, hP, ?_⟩
  have hconj : P⁻¹ * ((Polynomial.aeval M) q) * P
      = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • (P⁻¹ * M * P) ^ i := by
    rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, conj_pow hPdet]
  rw [hconj]
  exact isDiag_sum _ _ fun i _ => IsDiag.smul (q.coeff i) (isDiag_pow hD i)

/-!
## Simultaneous diagonalization — the common-diagonalizer closure laws

The `aeval` capstone above closes `IsDiagonalizable` under polynomials of a
*single* matrix `M` (all sharing `M`'s diagonalizer `P`).  The remaining
documented `nextSteps` item — sums and products of *distinct* diagonalizable
matrices — is genuinely harder: in general `M + N` and `M * N` need NOT be
diagonalizable, and the classical sufficient condition (commuting matrices are
*simultaneously* diagonalizable) requires an eigenspace-decomposition argument.

The two laws below isolate the reusable, elementary half of that story: **once a
single invertible `P` is known to diagonalize both `M` and `N`, it diagonalizes
`M + N` and `M * N` as well.**  A future proof that commuting diagonalizable
matrices admit a common `P` would combine with these to conclude the commuting
sum/product is diagonalizable; here the hard eigenspace step is deliberately left
out and the algebraic consequence is recorded in full.
-/

/-- **Common diagonalizer ⟹ the sum is diagonalizable.**  If a single invertible
    `P` diagonalizes both `M` and `N` (so `P⁻¹ M P` and `P⁻¹ N P` are diagonal),
    then the same `P` diagonalizes `M + N`, since
    `P⁻¹ (M + N) P = P⁻¹ M P + P⁻¹ N P` is a sum of two diagonal matrices. -/
theorem IsDiagonalizable.add_of_commonDiagonalizer {M N P : Matrix n n K}
    (hP : IsUnit P) (hM : (P⁻¹ * M * P).IsDiag) (hN : (P⁻¹ * N * P).IsDiag) :
    (M + N).IsDiagonalizable := by
  refine ⟨P, hP, ?_⟩
  have h : P⁻¹ * (M + N) * P = (P⁻¹ * M * P) + (P⁻¹ * N * P) := by
    rw [Matrix.mul_add, Matrix.add_mul]
  rw [h]
  exact hM.add hN

/-- **Common diagonalizer ⟹ the product is diagonalizable.**  If a single
    invertible `P` diagonalizes both `M` and `N`, then the same `P` diagonalizes
    `M * N`, since `P⁻¹ (M * N) P = (P⁻¹ M P) (P⁻¹ N P)` (cancelling the interior
    `P * P⁻¹ = 1`) is a product of two diagonal matrices (`isDiag_mul`).  Unlike
    the general product of diagonalizable matrices, sharing a diagonalizer makes
    the product diagonalizable unconditionally. -/
theorem IsDiagonalizable.mul_of_commonDiagonalizer {M N P : Matrix n n K}
    (hP : IsUnit P) (hM : (P⁻¹ * M * P).IsDiag) (hN : (P⁻¹ * N * P).IsDiag) :
    (M * N).IsDiagonalizable := by
  refine ⟨P, hP, ?_⟩
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPdet
  have h : P⁻¹ * (M * N) * P = (P⁻¹ * M * P) * (P⁻¹ * N * P) := by
    calc P⁻¹ * (M * N) * P
        = P⁻¹ * M * (P * P⁻¹) * N * P := by rw [hPP]; simp only [mul_one, mul_assoc]
      _ = (P⁻¹ * M * P) * (P⁻¹ * N * P) := by simp only [mul_assoc]
  rw [h]
  exact isDiag_mul hM hN

end MinpolyCharpolyOQ02Incomplete01
