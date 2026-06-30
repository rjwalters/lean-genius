/-
# Heron's Formula OQ-05-03: Cayley–Menger Polynomials Are Literally Determinants

The parent file `CayleyMengerHeronOQ05` introduces the Cayley–Menger *polynomials*
`cmDet3` / `cmDet4` (the expanded forms of the 4×4 / 5×5 bordered squared-distance
determinants) and proves they recover triangle area / tetrahedron volume. It does
not, however, certify that those polynomials are *literally* the determinants of
the bordered matrices

      ⎡ 0  1   1   1  ⎤              ⎡ 0  1   1   1   1  ⎤
      ⎢ 1  0  d₀₁ d₀₂ ⎥              ⎢ 1  0  d₀₁ d₀₂ d₀₃ ⎥
      ⎢ 1 d₀₁  0  d₁₂ ⎥              ⎢ 1 d₀₁  0  d₁₂ d₁₃ ⎥
      ⎣ 1 d₀₂ d₁₂  0  ⎦              ⎢ 1 d₀₂ d₁₂  0  d₂₃ ⎥
                                     ⎣ 1 d₀₃ d₁₃ d₂₃  0  ⎦

This file closes parent OQ-05 openQuestion[2]: it builds the bordered matrices
`cmMatrix3` / `cmMatrix4` as honest `Matrix (Fin 4) (Fin 4) ℝ` /
`Matrix (Fin 5) (Fin 5) ℝ` objects and proves, by cofactor expansion
(`Matrix.det_succ_row_zero` reduced through `Matrix.det_fin_three`), that

    (cmMatrix3 d₀₁ d₀₂ d₁₂).det = cmDet3 d₀₁ d₀₂ d₁₂
    (cmMatrix4 d₀₁ d₀₂ d₀₃ d₁₂ d₁₃ d₂₃).det = cmDet4 d₀₁ d₀₂ d₀₃ d₁₂ d₁₃ d₂₃

Composing with the parent identities then expresses the geometric content directly
as `Matrix.det`:

    (cmMatrix3 ‖·‖²).det = -4 · (2·Area)²        (triangle)
    (cmMatrix4 ‖·‖²).det =  8 · (6·V)²            (tetrahedron)

certifying the Cayley–Menger polynomials are exactly the bordered determinants.

## Status: Verified (0 axioms, 0 sorries)
-/

import Mathlib.Tactic
import Proofs.CayleyMengerHeronOQ05

namespace CayleyMengerHeron

open Matrix

/-! ## The bordered Cayley–Menger matrix of a triangle (4×4) -/

/-- The 4×4 bordered Cayley–Menger matrix of a triangle with squared edge lengths
`d₀₁, d₀₂, d₁₂`:

      ⎡ 0  1   1   1  ⎤
      ⎢ 1  0  d₀₁ d₀₂ ⎥
      ⎢ 1 d₀₁  0  d₁₂ ⎥
      ⎣ 1 d₀₂ d₁₂  0  ⎦ -/
def cmMatrix3 (d01 d02 d12 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![ 0,   1,   1,   1;
      1,   0,   d01, d02;
      1,   d01, 0,   d12;
      1,   d02, d12, 0]

/-- **The triangle Cayley–Menger polynomial is literally a determinant.**
The expanded polynomial `cmDet3` equals the determinant of the bordered 4×4
squared-distance matrix `cmMatrix3`. -/
theorem det_cmMatrix3 (d01 d02 d12 : ℝ) :
    (cmMatrix3 d01 d02 d12).det = cmDet3 d01 d02 d12 := by
  unfold cmMatrix3 cmDet3
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- **Cayley–Menger identity as a determinant (triangle).** The determinant of the
bordered squared-distance matrix of three planar points equals `-4` times the
square of twice their signed area. -/
theorem det_cmMatrix3_eq (P₀ P₁ P₂ : Point2) :
    (cmMatrix3 (sqDist2 P₀ P₁) (sqDist2 P₀ P₂) (sqDist2 P₁ P₂)).det
      = -4 * (area2 P₀ P₁ P₂) ^ 2 := by
  rw [det_cmMatrix3, cmDet3_eq]

/-- **Heron's formula as a determinant.** With `Area = |area2| / 2`,
`16·Area² = -det (cmMatrix3 ‖·‖²)`. -/
theorem heron_det_form (P₀ P₁ P₂ : Point2) :
    16 * (|area2 P₀ P₁ P₂| / 2) ^ 2
      = -(cmMatrix3 (sqDist2 P₀ P₁) (sqDist2 P₀ P₂) (sqDist2 P₁ P₂)).det := by
  rw [det_cmMatrix3]; exact heron_sixteen_area_sq P₀ P₁ P₂

/-! ## The bordered Cayley–Menger matrix of a tetrahedron (5×5) -/

/-- The 5×5 bordered Cayley–Menger matrix of a tetrahedron with squared edge
lengths `d₀₁, d₀₂, d₀₃, d₁₂, d₁₃, d₂₃`:

      ⎡ 0  1   1   1   1  ⎤
      ⎢ 1  0  d₀₁ d₀₂ d₀₃ ⎥
      ⎢ 1 d₀₁  0  d₁₂ d₁₃ ⎥
      ⎢ 1 d₀₂ d₁₂  0  d₂₃ ⎥
      ⎣ 1 d₀₃ d₁₃ d₂₃  0  ⎦ -/
def cmMatrix4 (d01 d02 d03 d12 d13 d23 : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![ 0,   1,   1,   1,   1;
      1,   0,   d01, d02, d03;
      1,   d01, 0,   d12, d13;
      1,   d02, d12, 0,   d23;
      1,   d03, d13, d23, 0]

/-- **The tetrahedron Cayley–Menger polynomial is literally a determinant.**
The expanded polynomial `cmDet4` equals the determinant of the bordered 5×5
squared-distance matrix `cmMatrix4`, established by two cofactor steps
(`Matrix.det_succ_row_zero`) reducing to 3×3 determinants. -/
theorem det_cmMatrix4 (d01 d02 d03 d12 d13 d23 : ℝ) :
    (cmMatrix4 d01 d02 d03 d12 d13 d23).det = cmDet4 d01 d02 d03 d12 d13 d23 := by
  unfold cmMatrix4 cmDet4
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- **Cayley–Menger identity as a determinant (tetrahedron).** The determinant of
the bordered squared-distance matrix of four points in space equals `8` times the
square of six times their signed volume. -/
theorem det_cmMatrix4_eq (P₀ P₁ P₂ P₃ : Point3) :
    (cmMatrix4 (sqDist3 P₀ P₁) (sqDist3 P₀ P₂) (sqDist3 P₀ P₃)
               (sqDist3 P₁ P₂) (sqDist3 P₁ P₃) (sqDist3 P₂ P₃)).det
      = 8 * (vol6 P₀ P₁ P₂ P₃) ^ 2 := by
  rw [det_cmMatrix4, cmDet4_eq]

/-- **Tetrahedron volume as a determinant.** With `V = |vol6| / 6`,
`288·V² = det (cmMatrix4 ‖·‖²)`. -/
theorem cayley_menger_tetrahedron_det_form (P₀ P₁ P₂ P₃ : Point3) :
    288 * (|vol6 P₀ P₁ P₂ P₃| / 6) ^ 2
      = (cmMatrix4 (sqDist3 P₀ P₁) (sqDist3 P₀ P₂) (sqDist3 P₀ P₃)
                   (sqDist3 P₁ P₂) (sqDist3 P₁ P₃) (sqDist3 P₂ P₃)).det := by
  rw [det_cmMatrix4]; exact cayley_menger_tetrahedron P₀ P₁ P₂ P₃

/-- **Degeneracy as a vanishing determinant.** Four points are coplanar (zero
volume) iff their bordered Cayley–Menger determinant vanishes. -/
theorem det_cmMatrix4_eq_zero_iff_coplanar (P₀ P₁ P₂ P₃ : Point3) :
    (cmMatrix4 (sqDist3 P₀ P₁) (sqDist3 P₀ P₂) (sqDist3 P₀ P₃)
               (sqDist3 P₁ P₂) (sqDist3 P₁ P₃) (sqDist3 P₂ P₃)).det = 0
      ↔ vol6 P₀ P₁ P₂ P₃ = 0 := by
  rw [det_cmMatrix4]; exact cmDet4_eq_zero_iff_coplanar P₀ P₁ P₂ P₃

end CayleyMengerHeron
