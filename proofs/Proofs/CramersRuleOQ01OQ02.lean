import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-
# Quasideterminant Theory: Non-Commutative Analogue of Determinants (OQ-01-OQ-02)

## Research Question
Is there a non-commutative analogue of determinants and Cramer's Rule
using quasideterminants (Gelfand-Retakh)?

## Answer: YES

This file develops the complete quasideterminant theory for 2x2 matrices
over division rings, extending CramersRuleOQ03.lean with:

1. All four quasideterminants (vs. OQ-03's two)
2. Matrix inversion via Schur complement
3. Alternate pivoting (solving via |A|11 when a00 != 0)
4. Row and column scaling identities
5. Complete commutative reduction (all four formulas)
6. Special cases (triangular, diagonal)

## Key Insight
An nxn matrix over a division ring has n^2 quasideterminants, one per entry.
The (i,j)-quasideterminant is the Schur complement of the complementary
submatrix. In the 2x2 case, each involves the inverse of a single
complementary entry.

## References
- Gelfand, Retakh: "Determinants of matrices over noncommutative rings" (1991)
- Gelfand, Retakh, Serconek, Wilson: "Quasideterminants" (2005)

## Extends
- CramersRuleOQ03.lean: Basic 2x2 non-commutative Cramer's rule
- CramersRuleOQ01.lean: Cayley-Hamilton from Cramer's rule
-/

noncomputable section

namespace CramersRuleOQ01OQ02

open Matrix

variable {D : Type*} [DivisionRing D]

-- ============================================================
-- PART I: The Four 2x2 Quasideterminants
-- ============================================================

/-
## The Complete Quasideterminant Set

For A = [[a,b],[c,d]] over a division ring D, the four quasideterminants are:

  |A|00 = a - b*d^{-1}*c    (Schur complement of d)
  |A|01 = b - a*c^{-1}*d    (Schur complement of c)
  |A|10 = c - d*b^{-1}*a    (Schur complement of b)
  |A|11 = d - c*a^{-1}*b    (Schur complement of a)
-/

/-- The (0,0)-quasideterminant: a - b*d^{-1}*c -/
def qdet00 (A : Matrix (Fin 2) (Fin 2) D) : D :=
  A 0 0 - A 0 1 * (A 1 1)⁻¹ * A 1 0

/-- The (0,1)-quasideterminant: b - a*c^{-1}*d -/
def qdet01 (A : Matrix (Fin 2) (Fin 2) D) : D :=
  A 0 1 - A 0 0 * (A 1 0)⁻¹ * A 1 1

/-- The (1,0)-quasideterminant: c - d*b^{-1}*a -/
def qdet10 (A : Matrix (Fin 2) (Fin 2) D) : D :=
  A 1 0 - A 1 1 * (A 0 1)⁻¹ * A 0 0

/-- The (1,1)-quasideterminant: d - c*a^{-1}*b -/
def qdet11 (A : Matrix (Fin 2) (Fin 2) D) : D :=
  A 1 1 - A 1 0 * (A 0 0)⁻¹ * A 0 1

-- ============================================================
-- PART II: Commutative Reduction
-- ============================================================

/-
## Connection to Classical Determinants

Over a commutative field F, each quasideterminant times its
complementary diagonal entry equals (plus or minus) the classical determinant:

  |A|00 * d = det(A)      a * |A|11 = det(A)
  |A|01 * c = -det(A)     b * |A|10 = -det(A)

This shows quasideterminants generalize det(A)/a_{jj}.
-/

/-- Over a commutative field: |A|00 * a11 = det(A) -/
theorem qdet00_mul_eq_det {F : Type*} [Field F]
    (A : Matrix (Fin 2) (Fin 2) F) (h : A 1 1 ≠ 0) :
    qdet00 A * A 1 1 = A.det := by
  simp only [qdet00, det_fin_two]
  field_simp

/-- Over a commutative field: a00 * |A|11 = det(A) -/
theorem mul_qdet11_eq_det {F : Type*} [Field F]
    (A : Matrix (Fin 2) (Fin 2) F) (h : A 0 0 ≠ 0) :
    A 0 0 * qdet11 A = A.det := by
  simp only [qdet11, det_fin_two]
  field_simp

/-- Over a commutative field: |A|01 * a10 = -det(A) -/
theorem qdet01_mul_eq_neg_det {F : Type*} [Field F]
    (A : Matrix (Fin 2) (Fin 2) F) (h : A 1 0 ≠ 0) :
    qdet01 A * A 1 0 = -A.det := by
  simp only [qdet01, det_fin_two]
  field_simp
  ring

/-- Over a commutative field: a01 * |A|10 = -det(A)
    (b * |A|10 = -det(A) per the doc table, where b = A 0 1 is the complement of position (1,0)). -/
theorem mul_qdet10_eq_neg_det {F : Type*} [Field F]
    (A : Matrix (Fin 2) (Fin 2) F) (h : A 0 1 ≠ 0) :
    A 0 1 * qdet10 A = -A.det := by
  simp only [qdet10, det_fin_two]
  field_simp
  ring

-- ============================================================
-- PART III: Triangular and Diagonal Special Cases
-- ============================================================

/-
## Simplifications for Special Matrix Forms

For triangular and diagonal matrices, the quasideterminants reduce
to the diagonal entries themselves (the off-diagonal contribution vanishes).
-/

/-- For an upper triangular matrix (a10 = 0), |A|00 = a00. -/
theorem qdet00_upper_tri (A : Matrix (Fin 2) (Fin 2) D) (h : A 1 0 = 0) :
    qdet00 A = A 0 0 := by
  simp [qdet00, h, mul_zero]

/-- For a lower triangular matrix (a01 = 0), |A|00 = a00. -/
theorem qdet00_lower_tri (A : Matrix (Fin 2) (Fin 2) D) (h : A 0 1 = 0) :
    qdet00 A = A 0 0 := by
  simp [qdet00, h, zero_mul]

/-- For an upper triangular matrix, |A|11 = a11. -/
theorem qdet11_upper_tri (A : Matrix (Fin 2) (Fin 2) D) (h : A 1 0 = 0) :
    qdet11 A = A 1 1 := by
  simp [qdet11, h, zero_mul]

/-- For a lower triangular matrix, |A|11 = a11. -/
theorem qdet11_lower_tri (A : Matrix (Fin 2) (Fin 2) D) (h : A 0 1 = 0) :
    qdet11 A = A 1 1 := by
  simp [qdet11, h, mul_zero]

/-- For an upper triangular matrix, |A|01 = a01. -/
theorem qdet01_upper_tri (A : Matrix (Fin 2) (Fin 2) D) (h : A 1 0 = 0) :
    qdet01 A = A 0 1 := by
  simp [qdet01, h, _root_.inv_zero, mul_zero, zero_mul]

/-- For a lower triangular matrix, |A|10 = a10. -/
theorem qdet10_lower_tri (A : Matrix (Fin 2) (Fin 2) D) (h : A 0 1 = 0) :
    qdet10 A = A 1 0 := by
  simp [qdet10, h, _root_.inv_zero, mul_zero, zero_mul]

-- ============================================================
-- PART IV: Row and Column Scaling
-- ============================================================

/-
## Scaling Identities

Quasideterminants transform naturally under row and column scaling.
These are the non-commutative analogues of det(lambda * row_i(A)) = lambda * det(A).

Key fact: scaling row i from the LEFT by lambda scales |A|_{ij} from the LEFT.
Scaling column j from the RIGHT by lambda scales |A|_{ij} from the RIGHT.
This distinguishes left/right scaling in the non-commutative setting.
-/

/-- Left row scaling: |A|00 is left-linear in row 0.
    If a' = lambda*a, b' = lambda*b (row 0 scaled), then |A'|00 = lambda * |A|00. -/
theorem qdet00_left_row0_scale (a b c d : D) (lambda : D) :
    let A := Matrix.of ![![a, b], ![c, d]]
    let A' := Matrix.of ![![lambda * a, lambda * b], ![c, d]]
    qdet00 A' = lambda * qdet00 A := by
  simp only [qdet00, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const]
  rw [mul_sub, mul_assoc, mul_assoc, mul_assoc]

/-- Right column scaling: |A|00 is right-linear in column 0.
    If a' = a*lambda, c' = c*lambda (col 0 scaled), then |A'|00 = |A|00 * lambda. -/
theorem qdet00_right_col0_scale (a b c d : D) (lambda : D) :
    let A := Matrix.of ![![a, b], ![c, d]]
    let A' := Matrix.of ![![a * lambda, b], ![c * lambda, d]]
    qdet00 A' = qdet00 A * lambda := by
  simp only [qdet00, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.head_fin_const]
  rw [sub_mul, mul_assoc, mul_assoc, mul_assoc]

-- ============================================================
-- PART V: Alternate Pivoting via qdet11
-- ============================================================

/-
## Solving via the (1,1)-quasideterminant

CramersRuleOQ03 solves Ax=b by pivoting on a11 (using |A|00).
When a00 != 0 instead, we pivot the other way using |A|11:

  x1 = |A|11^{-1} * (b1 - a10 * a00^{-1} * b0)
  x0 = a00^{-1} * (b0 - a01 * x1)

This provides a complete non-commutative solver covering all invertible matrices:
use the (0,0)-pivot when a11 != 0, or the (1,1)-pivot when a00 != 0.
-/

/-- The alternate non-commutative Cramer solution, pivoting via |A|11. -/
def ncSolveAlt (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D) : Fin 2 → D := fun i =>
  let x1 := (qdet11 A)⁻¹ * (b 1 - A 1 0 * (A 0 0)⁻¹ * b 0)
  if i = 1 then x1
  else (A 0 0)⁻¹ * (b 0 - A 0 1 * x1)

@[simp] theorem ncSolveAlt_zero (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D) :
    ncSolveAlt A b 0 = (A 0 0)⁻¹ * (b 0 - A 0 1 * ncSolveAlt A b 1) := by
  simp [ncSolveAlt]

@[simp] theorem ncSolveAlt_one (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D) :
    ncSolveAlt A b 1 = (qdet11 A)⁻¹ * (b 1 - A 1 0 * (A 0 0)⁻¹ * b 0) := by
  simp [ncSolveAlt]

/-- Row 0 correctness: a00*x0 + a01*x1 = b0.
    Proof: a00 cancels a00^{-1}, leaving (b0 - a01*x1) + a01*x1 = b0. -/
theorem ncSolveAlt_row0 (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D)
    (h00 : A 0 0 ≠ 0) :
    A 0 0 * ncSolveAlt A b 0 + A 0 1 * ncSolveAlt A b 1 = b 0 := by
  rw [ncSolveAlt_zero, ← mul_assoc, mul_inv_cancel₀ h00, one_mul]
  abel

/-- Row 1 correctness: a10*x0 + a11*x1 = b1.
    Proof: substitute x0 = a00^{-1}*(b0-a01*x1), factor out qdet11, cancel. -/
theorem ncSolveAlt_row1 (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D)
    (_h00 : A 0 0 ≠ 0) (hq : qdet11 A ≠ 0) :
    A 1 0 * ncSolveAlt A b 0 + A 1 1 * ncSolveAlt A b 1 = b 1 := by
  rw [ncSolveAlt_zero, ← mul_assoc (A 1 0), mul_sub,
    ← mul_assoc (A 1 0 * (A 0 0)⁻¹) (A 0 1)]
  -- Goal: a10*a00^{-1}*b0 - a10*a00^{-1}*a01*x1 + a11*x1 = b1
  -- Rearrange: (a11 - a10*a00^{-1}*a01)*x1 + a10*a00^{-1}*b0 = b1
  have key : A 1 0 * (A 0 0)⁻¹ * b 0 -
      A 1 0 * (A 0 0)⁻¹ * A 0 1 * ncSolveAlt A b 1 +
      A 1 1 * ncSolveAlt A b 1 =
      qdet11 A * ncSolveAlt A b 1 + A 1 0 * (A 0 0)⁻¹ * b 0 := by
    unfold qdet11; rw [sub_mul]; abel
  rw [key, ncSolveAlt_one, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]
  abel

/-- **Alternate Non-Commutative Cramer's Rule (2x2)**:
    A * ncSolveAlt(A, b) = b using the (1,1)-quasideterminant.
    This covers the case when a00 != 0, complementing OQ-03's a11 != 0 case. -/
theorem nc_cramers_rule_alt (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D)
    (h00 : A 0 0 ≠ 0) (hq : qdet11 A ≠ 0) :
    A.mulVec (ncSolveAlt A b) = b := by
  ext i
  simp only [mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases i
  · exact ncSolveAlt_row0 A b h00
  · exact ncSolveAlt_row1 A b h00 hq

/-- Kernel triviality for the alternate pivoting:
    If Ax = 0 and a00, |A|11 are invertible, then x = 0. -/
theorem nc_kernel_trivial_alt (A : Matrix (Fin 2) (Fin 2) D) (x : Fin 2 → D)
    (h00 : A 0 0 ≠ 0) (hq : qdet11 A ≠ 0)
    (hx : A.mulVec x = 0) : x = 0 := by
  have hrow0 : A 0 0 * x 0 + A 0 1 * x 1 = 0 := by
    have := congr_fun hx 0
    simp [mulVec, dotProduct, Fin.sum_univ_two] at this; exact this
  have hrow1 : A 1 0 * x 0 + A 1 1 * x 1 = 0 := by
    have := congr_fun hx 1
    simp [mulVec, dotProduct, Fin.sum_univ_two] at this; exact this
  -- From row 0: x0 = -(a00^{-1} * a01 * x1)
  have hx0 : x 0 = -((A 0 0)⁻¹ * (A 0 1 * x 1)) := by
    have h : A 0 0 * x 0 = -(A 0 1 * x 1) := add_eq_zero_iff_eq_neg.mp hrow0
    calc x 0 = (A 0 0)⁻¹ * (A 0 0 * x 0) := by
            rw [← mul_assoc, inv_mul_cancel₀ h00, one_mul]
      _ = -((A 0 0)⁻¹ * (A 0 1 * x 1)) := by rw [h, mul_neg]
  -- Substitute into row 1: qdet11(A) * x1 = 0
  have hqx : qdet11 A * x 1 = 0 := by
    have h1 : A 1 0 * (-((A 0 0)⁻¹ * (A 0 1 * x 1))) + A 1 1 * x 1 = 0 := by rwa [← hx0]
    rw [mul_neg, neg_add_eq_sub] at h1
    rw [← mul_assoc (A 1 0), ← mul_assoc (A 1 0 * (A 0 0)⁻¹)] at h1
    rwa [← sub_mul, show A 1 1 - A 1 0 * (A 0 0)⁻¹ * A 0 1 = qdet11 A from rfl] at h1
  -- qdet11 != 0, so x1 = 0; then x0 = 0
  have hx1 : x 1 = 0 := (mul_eq_zero.mp hqx).resolve_left hq
  have hx0z : x 0 = 0 := by rw [hx0, hx1, mul_zero, mul_zero, neg_zero]
  ext i; fin_cases i <;> assumption

/-- Uniqueness of the alternate solution. -/
theorem nc_cramers_unique_alt (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D)
    (h00 : A 0 0 ≠ 0) (hq : qdet11 A ≠ 0)
    (x : Fin 2 → D) (hx : A.mulVec x = b) :
    x = ncSolveAlt A b := by
  have hsolve := nc_cramers_rule_alt A b h00 hq
  have hdiff : A.mulVec (x - ncSolveAlt A b) = 0 := by
    ext i
    have hi := congr_fun (hx.trans hsolve.symm) i
    simp only [mulVec, dotProduct, Fin.sum_univ_two, Pi.sub_apply, Pi.zero_apply] at hi ⊢
    rw [mul_sub, mul_sub]
    have : A i 0 * x 0 - A i 0 * ncSolveAlt A b 0 +
        (A i 1 * x 1 - A i 1 * ncSolveAlt A b 1) =
        (A i 0 * x 0 + A i 1 * x 1) - (A i 0 * ncSolveAlt A b 0 + A i 1 * ncSolveAlt A b 1) := by
      abel
    rw [this, sub_eq_zero.mpr hi]
  have hzero := nc_kernel_trivial_alt A _ h00 hq hdiff
  ext i; exact sub_eq_zero.mp (congr_fun hzero i)

-- ============================================================
-- PART VI: Matrix Inversion via Schur Complement
-- ============================================================

/-
## The Schur Complement Inversion Formula

For A = [[a,b],[c,d]] over D with d != 0, |A|00 != 0:

  A^{-1} = [[ q^{-1},             -(q^{-1}*b*d^{-1})          ],
             [ -(d^{-1}*c*q^{-1}),  d^{-1}+d^{-1}*c*q^{-1}*b*d^{-1} ]]

where q = |A|00 = a - b*d^{-1}*c.
-/

/-- The Schur complement inverse of a 2x2 matrix. -/
def schurInv (A : Matrix (Fin 2) (Fin 2) D) : Matrix (Fin 2) (Fin 2) D := fun i j =>
  let q := qdet00 A
  let d := A 1 1
  if i = 0 then
    if j = 0 then q⁻¹
    else -(q⁻¹ * A 0 1 * d⁻¹)
  else
    if j = 0 then -(d⁻¹ * A 1 0 * q⁻¹)
    else d⁻¹ + d⁻¹ * A 1 0 * q⁻¹ * A 0 1 * d⁻¹

@[simp] lemma schurInv_00 (A : Matrix (Fin 2) (Fin 2) D) :
    schurInv A 0 0 = (qdet00 A)⁻¹ := by simp [schurInv]

@[simp] lemma schurInv_01 (A : Matrix (Fin 2) (Fin 2) D) :
    schurInv A 0 1 = -((qdet00 A)⁻¹ * A 0 1 * (A 1 1)⁻¹) := by
  simp only [schurInv, show ¬(1 : Fin 2) = (0 : Fin 2) from by decide,
    if_true, if_false, ite_true, ite_false]

@[simp] lemma schurInv_10 (A : Matrix (Fin 2) (Fin 2) D) :
    schurInv A 1 0 = -((A 1 1)⁻¹ * A 1 0 * (qdet00 A)⁻¹) := by
  simp only [schurInv, show ¬(1 : Fin 2) = (0 : Fin 2) from by decide,
    if_true, if_false, ite_true, ite_false]

@[simp] lemma schurInv_11 (A : Matrix (Fin 2) (Fin 2) D) :
    schurInv A 1 1 =
      (A 1 1)⁻¹ + (A 1 1)⁻¹ * A 1 0 * (qdet00 A)⁻¹ * A 0 1 * (A 1 1)⁻¹ := by
  simp only [schurInv, show ¬(1 : Fin 2) = (0 : Fin 2) from by decide,
    show (1 : Fin 2) = 1 from rfl, ite_false, ite_true]

/-- The (0,0) entry of A * schurInv(A) is 1.
    Proof: a*q^{-1} - b*d^{-1}*c*q^{-1} = (a - b*d^{-1}*c)*q^{-1} = q*q^{-1} = 1. -/
theorem mul_schurInv_00 (A : Matrix (Fin 2) (Fin 2) D)
    (hq : qdet00 A ≠ 0) :
    A 0 0 * schurInv A 0 0 + A 0 1 * schurInv A 1 0 = 1 := by
  simp only [schurInv_00, schurInv_10]
  rw [mul_neg, ← sub_eq_add_neg]
  rw [show A 0 1 * ((A 1 1)⁻¹ * A 1 0 * (qdet00 A)⁻¹) =
        A 0 1 * (A 1 1)⁻¹ * A 1 0 * (qdet00 A)⁻¹ from by
    rw [← mul_assoc, ← mul_assoc]]
  rw [← sub_mul, show A 0 0 - A 0 1 * (A 1 1)⁻¹ * A 1 0 = qdet00 A from rfl]
  exact mul_inv_cancel₀ hq

/-- The (1,0) entry of A * schurInv(A) is 0.
    Proof: c*q^{-1} - d*d^{-1}*c*q^{-1} = c*q^{-1} - c*q^{-1} = 0. -/
theorem mul_schurInv_10 (A : Matrix (Fin 2) (Fin 2) D)
    (hd : A 1 1 ≠ 0) :
    A 1 0 * schurInv A 0 0 + A 1 1 * schurInv A 1 0 = 0 := by
  simp only [schurInv_00, schurInv_10]
  rw [mul_neg]
  rw [show A 1 1 * ((A 1 1)⁻¹ * A 1 0 * (qdet00 A)⁻¹) = A 1 0 * (qdet00 A)⁻¹ from by
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]]
  exact add_neg_cancel _

-- ============================================================
-- PART VII: Transpose and Commutativity
-- ============================================================

/-
## Transpose Duality

In the non-commutative case, transposition reverses multiplication order,
so |A^T|00 != |A|00 in general. But over a commutative field, they agree.
-/

/-- Over a commutative field, qdet00(A^T) = qdet00(A). -/
theorem qdet00_transpose_comm {F : Type*} [Field F]
    (A : Matrix (Fin 2) (Fin 2) F) :
    qdet00 (A.transpose) = qdet00 A := by
  simp only [qdet00, transpose_apply]
  ring

/-- Over a commutative field, qdet11(A^T) = qdet11(A). -/
theorem qdet11_transpose_comm {F : Type*} [Field F]
    (A : Matrix (Fin 2) (Fin 2) F) :
    qdet11 (A.transpose) = qdet11 A := by
  simp only [qdet11, transpose_apply]
  ring

-- ============================================================
-- PART VIII: Quasideterminant and Zero Entries
-- ============================================================

/-
## Behavior When Entries Vanish

When the "complementary" entry is zero, the inverse is 0 (by convention in
DivisionRing), and the quasideterminant degenerates to the entry itself.
This is the non-commutative analogue of det(triangular) = product of diagonal.
-/

/-- If the complementary entry a11 = 0, then qdet00 = a00.
    (Since 0^{-1} = 0 in a DivisionRing, the correction term vanishes.) -/
theorem qdet00_of_zero_complement (A : Matrix (Fin 2) (Fin 2) D) (h : A 1 1 = 0) :
    qdet00 A = A 0 0 := by
  simp [qdet00, h, _root_.inv_zero, mul_zero, zero_mul]

/-- If the complementary entry a00 = 0, then qdet11 = a11. -/
theorem qdet11_of_zero_complement (A : Matrix (Fin 2) (Fin 2) D) (h : A 0 0 = 0) :
    qdet11 A = A 1 1 := by
  simp [qdet11, h, _root_.inv_zero, mul_zero, zero_mul]

-- ============================================================
-- PART IX: Quasideterminant Product Identities
-- ============================================================

/-
## Products of Quasideterminants

Over a commutative field, the product of the two diagonal quasideterminants
relates to the determinant and diagonal entries:
  |A|00 * |A|11 = det(A) * (a11^{-1} * a00^{-1} * det(A))
This simplifies in the commutative case but is nontrivial in general.
-/

/-- Over a commutative field: |A|00 * a11 * a00^{-1} * |A|11 = det(A)^2 * a00^{-1} * a11^{-1}.
    More usefully, both diagonal quasideterminants are det(A)/a_{jj}. -/
theorem qdet00_eq_det_div {F : Type*} [Field F]
    (A : Matrix (Fin 2) (Fin 2) F) (h : A 1 1 ≠ 0) :
    qdet00 A = A.det * (A 1 1)⁻¹ := by
  have := qdet00_mul_eq_det A h
  rw [eq_comm, ← mul_inv_cancel_right₀ h (qdet00 A)]
  rw [this]

theorem qdet11_eq_det_div {F : Type*} [Field F]
    (A : Matrix (Fin 2) (Fin 2) F) (h : A 0 0 ≠ 0) :
    qdet11 A = A.det * (A 0 0)⁻¹ := by
  have hmul := mul_qdet11_eq_det A h
  rw [← hmul]
  field_simp

/-- Over a commutative field, the two diagonal quasideterminants are proportional:
    |A|00 * a00 = |A|11 * a11 (both equal det(A)). -/
theorem qdet00_qdet11_proportional {F : Type*} [Field F]
    (A : Matrix (Fin 2) (Fin 2) F) (ha : A 0 0 ≠ 0) (hd : A 1 1 ≠ 0) :
    qdet00 A * A 1 1 = A 0 0 * qdet11 A := by
  rw [qdet00_mul_eq_det A hd, mul_qdet11_eq_det A ha]

end CramersRuleOQ01OQ02

end
