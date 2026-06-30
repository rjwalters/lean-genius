import Mathlib

/-
# The Cayley–Menger polynomials are *literally* determinants

The parent entry (`CayleyMengerHeronOQ05`) introduces the Cayley–Menger
*polynomials* `cmDet3` (triangle) and `cmDet4` (tetrahedron) in the squared edge
lengths and proves they reproduce `−16·Area²` and `288·V²`.  Their docstrings
*assert* that these polynomials are the determinants of the bordered
squared-distance matrices

      ⎡ 0  1   1   1  ⎤                  ⎡ 0  1   1   1   1  ⎤
      ⎢ 1  0  d₀₁ d₀₂ ⎥                  ⎢ 1  0  d₀₁ d₀₂ d₀₃ ⎥
      ⎢ 1 d₀₁  0  d₁₂ ⎥   and           ⎢ 1 d₀₁  0  d₁₂ d₁₃ ⎥
      ⎣ 1 d₀₂ d₁₂  0  ⎦                  ⎢ 1 d₀₂ d₁₂  0  d₂₃ ⎥
                                         ⎣ 1 d₀₃ d₁₃ d₂₃  0  ⎦

but never *certify* that claim: `cmDet3`/`cmDet4` are entered as hand-expanded
polynomials.  This entry closes that gap (parent open question oq-03): it builds
the bordered matrices as honest `Matrix (Fin 4) (Fin 4) ℝ` / `Matrix (Fin 5)
(Fin 5) ℝ` objects and proves, by Laplace cofactor expansion, that
`Matrix.det` of each **equals** the parent polynomial.  Combined with the parent
identities this gives the textbook determinant forms of Heron's formula and the
tetrahedron-volume formula:

* `det (bordered 4×4) = −16·Area²`,
* `det (bordered 5×5) =  288·V²`.

Mathlib has `Matrix.det_fin_three` but no `det_fin_four`/`det_fin_five`; the 4×4
and 5×5 determinants are obtained from the general Laplace expansion
`Matrix.det_succ_row_zero` down to the 3×3 base case.

The polynomial definitions `cmDet3`, `cmDet4` and the geometric scalars
`sqDist2`, `area2`, `sqDist3`, `vol6` are reproduced verbatim from the parent so
this file is self-contained and machine-checks standalone.

No axioms, no sorries.
-/

namespace CayleyMengerHeronOQ0503

open Matrix

/-! ## A 4×4 determinant expansion

Mathlib provides `Matrix.det_fin_three` but stops there.  We record the Laplace
cofactor expansion of a general 4×4 matrix along its first row; this is the
engine for evaluating the 5×5 Cayley–Menger determinant below. -/

set_option maxHeartbeats 1000000 in
/-- Cofactor (Laplace) expansion of a 4×4 determinant along the first row. -/
theorem det_fin_four {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) :
    M.det =
      M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2)
             - M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1)
             + M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1))
    - M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2)
             - M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
             + M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0))
    + M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1)
             - M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
             + M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0))
    - M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1)
             - M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)
             + M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) := by
  simp only [Matrix.det_succ_row_zero, Matrix.submatrix_apply, Fin.succ_zero_eq_one,
    Matrix.submatrix_submatrix, Matrix.det_unique, Fin.default_eq_zero, Function.comp_apply,
    Fin.succ_one_eq_two, Fin.sum_univ_succ, Fin.val_zero, Fin.zero_succAbove, Finset.univ_unique,
    Fin.val_succ, Fin.val_eq_zero, Fin.succ_succAbove_zero, Finset.sum_singleton,
    Fin.succ_succAbove_one, Fin.succ_succAbove_succ,
    show Fin.succ (2 : Fin 3) = (3 : Fin 4) from rfl,
    show Fin.succAbove (1 : Fin 4) (2 : Fin 3) = (3 : Fin 4) from rfl,
    show Fin.succAbove (2 : Fin 4) (2 : Fin 3) = (3 : Fin 4) from rfl,
    show Fin.succAbove (3 : Fin 4) (2 : Fin 3) = (2 : Fin 4) from rfl]
  ring

/-! ## Triangle (n = 2): the 4×4 Cayley–Menger determinant -/

abbrev Point2 := ℝ × ℝ

/-- Squared Euclidean distance between two points of the plane. -/
def sqDist2 (p q : Point2) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Twice the signed area of triangle `P₀P₁P₂`. -/
def area2 (P₀ P₁ P₂ : Point2) : ℝ :=
  (P₁.1 - P₀.1) * (P₂.2 - P₀.2) - (P₂.1 - P₀.1) * (P₁.2 - P₀.2)

/-- The Cayley–Menger polynomial of a triangle (parent `cmDet3`). -/
def cmDet3 (d01 d02 d12 : ℝ) : ℝ :=
  d01 ^ 2 - 2 * d01 * d02 - 2 * d01 * d12 + d02 ^ 2 - 2 * d02 * d12 + d12 ^ 2

/-- The bordered squared-distance matrix of a triangle. -/
def cmMatrix3 (d01 d02 d12 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 1, 1;
     1, 0, d01, d02;
     1, d01, 0, d12;
     1, d02, d12, 0]

/-- **The triangle Cayley–Menger polynomial is literally a determinant.** -/
theorem cmDet3_eq_det (d01 d02 d12 : ℝ) :
    (cmMatrix3 d01 d02 d12).det = cmDet3 d01 d02 d12 := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [cmMatrix3, Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_succ,
    Matrix.cons_val, Fin.isValue, Fin.succAbove, Fin.succ, Fin.castSucc, Fin.castAdd,
    Fin.castLE, Fin.lt_def]
  norm_num [cmDet3]
  ring

/-- **Heron's formula, determinant form.** The determinant of the bordered
squared-distance matrix of three planar points equals `-16·Area²`, where
`Area = |area2|/2` is the triangle's area. This is `cmDet3_eq_det` combined with
the parent Cayley–Menger identity `cmDet3 = -4·(2·Area)²`. -/
theorem det_cmMatrix3_eq_area (P₀ P₁ P₂ : Point2) :
    (cmMatrix3 (sqDist2 P₀ P₁) (sqDist2 P₀ P₂) (sqDist2 P₁ P₂)).det
      = -16 * (|area2 P₀ P₁ P₂| / 2) ^ 2 := by
  rw [cmDet3_eq_det, cmDet3, sqDist2, sqDist2, sqDist2, area2, div_pow, sq_abs]
  ring

/-! ## Tetrahedron (n = 3): the 5×5 Cayley–Menger determinant -/

abbrev Point3 := ℝ × ℝ × ℝ

/-- Squared Euclidean distance between two points of space. -/
def sqDist3 (p q : Point3) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 + (p.2.2 - q.2.2) ^ 2

/-- Six times the signed volume of tetrahedron `P₀P₁P₂P₃` (the `3!·V` scalar). -/
def vol6 (P₀ P₁ P₂ P₃ : Point3) : ℝ :=
  (P₁.1 - P₀.1) *
      ((P₂.2.1 - P₀.2.1) * (P₃.2.2 - P₀.2.2) - (P₂.2.2 - P₀.2.2) * (P₃.2.1 - P₀.2.1))
  - (P₁.2.1 - P₀.2.1) *
      ((P₂.1 - P₀.1) * (P₃.2.2 - P₀.2.2) - (P₂.2.2 - P₀.2.2) * (P₃.1 - P₀.1))
  + (P₁.2.2 - P₀.2.2) *
      ((P₂.1 - P₀.1) * (P₃.2.1 - P₀.2.1) - (P₂.2.1 - P₀.2.1) * (P₃.1 - P₀.1))

/-- The Cayley–Menger polynomial of a tetrahedron (parent `cmDet4`). -/
def cmDet4 (d01 d02 d03 d12 d13 d23 : ℝ) : ℝ :=
  -2 * d01 ^ 2 * d23 - 2 * d01 * d02 * d12 + 2 * d01 * d02 * d13
  + 2 * d01 * d02 * d23 + 2 * d01 * d03 * d12 - 2 * d01 * d03 * d13
  + 2 * d01 * d03 * d23 + 2 * d01 * d12 * d23 + 2 * d01 * d13 * d23
  - 2 * d01 * d23 ^ 2 - 2 * d02 ^ 2 * d13 + 2 * d02 * d03 * d12
  + 2 * d02 * d03 * d13 - 2 * d02 * d03 * d23 + 2 * d02 * d12 * d13
  - 2 * d02 * d13 ^ 2 + 2 * d02 * d13 * d23 - 2 * d03 ^ 2 * d12
  - 2 * d03 * d12 ^ 2 + 2 * d03 * d12 * d13 + 2 * d03 * d12 * d23
  - 2 * d12 * d13 * d23

/-- The bordered squared-distance matrix of a tetrahedron. -/
def cmMatrix4 (d01 d02 d03 d12 d13 d23 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 1, 1, 1, 1;
     1, 0, d01, d02, d03;
     1, d01, 0, d12, d13;
     1, d02, d12, 0, d23;
     1, d03, d13, d23, 0]

set_option maxHeartbeats 1000000 in
/-- **The tetrahedron Cayley–Menger polynomial is literally a determinant.** -/
theorem cmDet4_eq_det (d01 d02 d03 d12 d13 d23 : ℝ) :
    (cmMatrix4 d01 d02 d03 d12 d13 d23).det = cmDet4 d01 d02 d03 d12 d13 d23 := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_five]
  simp only [cmMatrix4, det_fin_four, Matrix.submatrix_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_succ,
    Matrix.cons_val, Fin.isValue, Fin.succAbove, Fin.succ, Fin.castSucc, Fin.castAdd,
    Fin.castLE, Fin.lt_def]
  norm_num [cmDet4]
  ring

/-- **Tetrahedron volume, determinant form.** The determinant of the bordered
squared-distance matrix of four points in space equals `288·V²`, where
`V = |vol6|/6` is the tetrahedron's volume. -/
theorem det_cmMatrix4_eq_vol (P₀ P₁ P₂ P₃ : Point3) :
    (cmMatrix4 (sqDist3 P₀ P₁) (sqDist3 P₀ P₂) (sqDist3 P₀ P₃)
               (sqDist3 P₁ P₂) (sqDist3 P₁ P₃) (sqDist3 P₂ P₃)).det
      = 288 * (|vol6 P₀ P₁ P₂ P₃| / 6) ^ 2 := by
  rw [cmDet4_eq_det, cmDet4]
  simp only [sqDist3, vol6, div_pow, sq_abs]
  ring

/-- The Cayley–Menger determinant of four points in space is always nonnegative
(equivalently `288·V² ≥ 0`), recovered directly from the matrix determinant. -/
theorem det_cmMatrix4_nonneg (P₀ P₁ P₂ P₃ : Point3) :
    0 ≤ (cmMatrix4 (sqDist3 P₀ P₁) (sqDist3 P₀ P₂) (sqDist3 P₀ P₃)
               (sqDist3 P₁ P₂) (sqDist3 P₁ P₃) (sqDist3 P₂ P₃)).det := by
  rw [det_cmMatrix4_eq_vol]; positivity

end CayleyMengerHeronOQ0503
