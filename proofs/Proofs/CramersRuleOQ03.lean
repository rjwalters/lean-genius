import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-
# Non-Commutative Cramer's Rule via Quasideterminants

Extends Cramer's Rule from commutative rings to division rings
using the Gelfand-Retakh quasideterminant (Schur complement).

For a 2×2 system Ax = b over a division ring D, the solution is:
  x₀ = |A|₀₀⁻¹ · (b₀ - a₀₁ · a₁₁⁻¹ · b₁)
  x₁ = a₁₁⁻¹ · (b₁ - a₁₀ · x₀)
where |A|₀₀ = a₀₀ - a₀₁ · a₁₁⁻¹ · a₁₀ is the quasideterminant.

References:
- Gelfand, Retakh: "Determinants of matrices over noncommutative rings" (1991)
- Gelfand, Retakh: "Quasideterminants, I" (1997)
-/

noncomputable section

namespace CramersRuleOQ03

open Matrix Finset

variable {D : Type*} [DivisionRing D]

/-
## Section I: Quasideterminants

For a 2×2 matrix A over a division ring, the (i,j)-quasideterminant
is the Schur complement of the complementary entry.
-/

/-- The (0,0)-quasideterminant: |A|₀₀ = a₀₀ - a₀₁ · a₁₁⁻¹ · a₁₀.
    This is the Schur complement of the (1,1)-entry. -/
def quasidet₀₀ (A : Matrix (Fin 2) (Fin 2) D) : D :=
  A 0 0 - A 0 1 * (A 1 1)⁻¹ * A 1 0

/-- The (1,1)-quasideterminant: |A|₁₁ = a₁₁ - a₁₀ · a₀₀⁻¹ · a₀₁. -/
def quasidet₁₁ (A : Matrix (Fin 2) (Fin 2) D) : D :=
  A 1 1 - A 1 0 * (A 0 0)⁻¹ * A 0 1

/-
## Section II: Solution Formula
-/

/-- The non-commutative Cramer solution for a 2×2 system Ax = b.
    x₀ = |A|₀₀⁻¹ · (b₀ - a₀₁ · a₁₁⁻¹ · b₁)
    x₁ = a₁₁⁻¹ · (b₁ - a₁₀ · x₀) -/
def ncSolve (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D) : Fin 2 → D := fun i =>
  let x₀ := (quasidet₀₀ A)⁻¹ * (b 0 - A 0 1 * (A 1 1)⁻¹ * b 1)
  if i = 0 then x₀
  else (A 1 1)⁻¹ * (b 1 - A 1 0 * x₀)

/-- The first component of the solution. -/
@[simp]
theorem ncSolve_zero (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D) :
    ncSolve A b 0 = (quasidet₀₀ A)⁻¹ * (b 0 - A 0 1 * (A 1 1)⁻¹ * b 1) := by
  simp [ncSolve]

/-- The second component of the solution. -/
@[simp]
theorem ncSolve_one (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D) :
    ncSolve A b 1 = (A 1 1)⁻¹ * (b 1 - A 1 0 * ncSolve A b 0) := by
  simp [ncSolve]

/-
## Section III: Correctness
-/

/-- Row 1 of the system is satisfied: a₁₀·x₀ + a₁₁·x₁ = b₁.
    Key step: a₁₁ · (a₁₁⁻¹ · z) = z by left cancellation. -/
theorem ncSolve_row1 (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D)
    (h22 : A 1 1 ≠ 0) :
    A 1 0 * ncSolve A b 0 + A 1 1 * ncSolve A b 1 = b 1 := by
  rw [ncSolve_one, ← mul_assoc, mul_inv_cancel₀ h22, one_mul]
  abel

/-- Row 0 of the system is satisfied: a₀₀·x₀ + a₀₁·x₁ = b₀.
    Key steps: (1) distribute a₀₁·a₁₁⁻¹ over subtraction,
    (2) factor out quasideterminant, (3) cancel q·q⁻¹. -/
theorem ncSolve_row0 (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D)
    (_h22 : A 1 1 ≠ 0) (hq : quasidet₀₀ A ≠ 0) :
    A 0 0 * ncSolve A b 0 + A 0 1 * ncSolve A b 1 = b 0 := by
  rw [ncSolve_one, ← mul_assoc (A 0 1), mul_sub, ← mul_assoc (A 0 1 * (A 1 1)⁻¹) (A 1 0)]
  -- Factor: a₀₀·x₀ + c·b₁ - c·a₁₀·x₀ = q·x₀ + c·b₁
  have factored : A 0 0 * ncSolve A b 0 +
      (A 0 1 * (A 1 1)⁻¹ * b 1 - A 0 1 * (A 1 1)⁻¹ * A 1 0 * ncSolve A b 0) =
      quasidet₀₀ A * ncSolve A b 0 + A 0 1 * (A 1 1)⁻¹ * b 1 := by
    unfold quasidet₀₀; rw [sub_mul]; abel
  rw [factored, ncSolve_zero, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]
  abel

/-
## Section IV: Main Theorem
-/

/-- **Non-Commutative Cramer's Rule (2×2)**:
    The quasideterminant solution satisfies Ax = b over any division ring.

    This answers OQ-03 affirmatively: Cramer's Rule extends to
    non-commutative settings via the Gelfand-Retakh quasideterminant. -/
theorem nc_cramers_rule (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D)
    (h22 : A 1 1 ≠ 0) (hq : quasidet₀₀ A ≠ 0) :
    A.mulVec (ncSolve A b) = b := by
  ext i
  simp only [mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases i
  · exact ncSolve_row0 A b h22 hq
  · exact ncSolve_row1 A b h22

/-
## Section V: Uniqueness
-/

/-- If A·x = 0 and the quasideterminant is invertible, then x = 0.
    The 2×2 system with invertible quasideterminant has trivial kernel. -/
theorem nc_kernel_trivial (A : Matrix (Fin 2) (Fin 2) D) (x : Fin 2 → D)
    (h22 : A 1 1 ≠ 0) (hq : quasidet₀₀ A ≠ 0)
    (hx : A.mulVec x = 0) : x = 0 := by
  have hrow0 : A 0 0 * x 0 + A 0 1 * x 1 = 0 := by
    have := congr_fun hx 0; simp [mulVec, dotProduct, Fin.sum_univ_two] at this; exact this
  have hrow1 : A 1 0 * x 0 + A 1 1 * x 1 = 0 := by
    have := congr_fun hx 1; simp [mulVec, dotProduct, Fin.sum_univ_two] at this; exact this
  -- From row 1: x₁ = -(a₁₁⁻¹ · a₁₀ · x₀)
  have hx1 : x 1 = -((A 1 1)⁻¹ * (A 1 0 * x 0)) := by
    have h := eq_neg_of_add_eq_zero_right hrow1
    calc x 1 = (A 1 1)⁻¹ * (A 1 1 * x 1) := by
            rw [← mul_assoc, inv_mul_cancel₀ h22, one_mul]
      _ = -((A 1 1)⁻¹ * (A 1 0 * x 0)) := by rw [h, mul_neg]
  -- Substitute into row 0: quasidet₀₀(A) · x₀ = 0
  have hqx : quasidet₀₀ A * x 0 = 0 := by
    have h0 : A 0 0 * x 0 + A 0 1 * (-((A 1 1)⁻¹ * (A 1 0 * x 0))) = 0 := by rwa [← hx1]
    rw [mul_neg, ← sub_eq_add_neg] at h0
    rw [← mul_assoc (A 0 1), ← mul_assoc (A 0 1 * (A 1 1)⁻¹)] at h0
    rwa [← sub_mul, show A 0 0 - A 0 1 * (A 1 1)⁻¹ * A 1 0 = quasidet₀₀ A from rfl] at h0
  -- q ≠ 0, so x₀ = 0; then x₁ = 0
  have hx0 : x 0 = 0 := (mul_eq_zero.mp hqx).resolve_left hq
  have hx1z : x 1 = 0 := by rw [hx1, hx0, mul_zero, mul_zero, neg_zero]
  ext i; fin_cases i <;> assumption

/-- The non-commutative Cramer solution is unique. -/
theorem nc_cramers_unique (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D)
    (h22 : A 1 1 ≠ 0) (hq : quasidet₀₀ A ≠ 0)
    (x : Fin 2 → D) (hx : A.mulVec x = b) :
    x = ncSolve A b := by
  have hsolve := nc_cramers_rule A b h22 hq
  have hdiff : A.mulVec (x - ncSolve A b) = 0 := by
    have heq := hx.trans hsolve.symm
    ext i
    have hi := congr_fun heq i
    simp only [mulVec, dotProduct, Fin.sum_univ_two, Pi.sub_apply, Pi.zero_apply] at hi ⊢
    rw [mul_sub, mul_sub]
    have rearr : A i 0 * x 0 - A i 0 * ncSolve A b 0 + (A i 1 * x 1 - A i 1 * ncSolve A b 1) =
        (A i 0 * x 0 + A i 1 * x 1) - (A i 0 * ncSolve A b 0 + A i 1 * ncSolve A b 1) := by abel
    rw [rearr, sub_eq_zero.mpr hi]
  have hzero := nc_kernel_trivial A _ h22 hq hdiff
  ext i; exact sub_eq_zero.mp (congr_fun hzero i)

/-
## Section VI: Commutative Reduction
-/

/-- In the commutative case, quasidet₀₀(A) · a₁₁ = det(A).
    This shows the quasideterminant generalizes the classical determinant. -/
theorem quasidet_mul_eq_det {F : Type*} [Field F]
    (A : Matrix (Fin 2) (Fin 2) F) (h : A 1 1 ≠ 0) :
    quasidet₀₀ A * A 1 1 = A.det := by
  simp only [quasidet₀₀, det_fin_two]
  field_simp

end CramersRuleOQ03

end
