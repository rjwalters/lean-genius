/-
  The Parallelogram Defect Identity (sharp generalization of the British Flag Theorem)
  Open Question: british-flag-theorem-oq-01-oq-01

  For a parallelogram A, B = A+u, C = A+u+v, D = A+v in any real inner product
  space, and any point P, the "British-flag defect"
    |PA|² + |PC|² − |PB|² − |PD|²
  equals 2⟪u, v⟫ — independent of the observer P and of the base point A. When
  the parallelogram is a rectangle (u ⊥ v) the defect vanishes, recovering the
  British Flag Theorem in arbitrary dimension.

  ## Main Result

  `parallelogram_defect` (PROVED): in a real inner product space,
    ‖P − A‖² + ‖P − (A+u+v)‖² − ‖P − (A+u)‖² − ‖P − (A+v)‖² = 2⟪u, v⟫.

  ## Corollaries

  `british_flag_of_orthogonal` : u ⊥ v ⟹ the two diagonal sums are equal.
  `british_flag`               : vertex form with C = B + D − A and AB ⊥ AD,
                                 the British Flag Theorem in any dimension.

  ## Proof Strategy

  Translate so the base point is A: with x = P − A, the four points become
  x, x − u, x − u − v, x − v. Expanding each squared norm with
  `norm_sub_sq_real` / `norm_add_sq_real` (all inner products appear with the
  same orientation, so no symmetry juggling is needed) and cancelling, the
  P- and A-dependent terms drop out, leaving exactly 2⟪u, v⟫.
-/

import Mathlib

open scoped InnerProductSpace

namespace BritishFlagTheoremOQ01OQ01

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Parallelogram defect identity.** For a parallelogram with vertex `A` and
    edge vectors `u`, `v` (so the vertices are `A`, `A+u`, `A+u+v`, `A+v`), and
    for any point `P`, the British-flag defect equals `2⟪u, v⟫`, independent of
    `P` and `A`. -/
theorem parallelogram_defect (P A u v : V) :
    ‖P - A‖ ^ 2 + ‖P - (A + u + v)‖ ^ 2 - ‖P - (A + u)‖ ^ 2 - ‖P - (A + v)‖ ^ 2
      = 2 * ⟪u, v⟫_ℝ := by
  have e1 : P - (A + u + v) = (P - A) - (u + v) := by abel
  have e2 : P - (A + u) = (P - A) - u := by abel
  have e3 : P - (A + v) = (P - A) - v := by abel
  rw [e1, e2, e3, norm_sub_sq_real (P - A) (u + v), norm_sub_sq_real (P - A) u,
    norm_sub_sq_real (P - A) v, norm_add_sq_real u v, inner_add_right]
  ring

/-- If the parallelogram is a rectangle (`u ⊥ v`), the defect vanishes: the sum
    of squared distances to one diagonal's endpoints equals the sum to the
    other's. This is the British Flag Theorem, here in an arbitrary real inner
    product space. -/
theorem british_flag_of_orthogonal (P A u v : V) (h : ⟪u, v⟫_ℝ = 0) :
    ‖P - A‖ ^ 2 + ‖P - (A + u + v)‖ ^ 2 = ‖P - (A + u)‖ ^ 2 + ‖P - (A + v)‖ ^ 2 := by
  have hd := parallelogram_defect P A u v
  rw [h, mul_zero] at hd
  linarith

/-- **British Flag Theorem (vertex form, any dimension).** If `ABCD` is a
    rectangle — `C = B + D − A` closes the parallelogram and `AB ⊥ AD` — then for
    every point `P`,
      ‖P − A‖² + ‖P − C‖² = ‖P − B‖² + ‖P − D‖². -/
theorem british_flag (P A B C D : V) (hC : C = B + D - A)
    (hperp : ⟪B - A, D - A⟫_ℝ = 0) :
    ‖P - A‖ ^ 2 + ‖P - C‖ ^ 2 = ‖P - B‖ ^ 2 + ‖P - D‖ ^ 2 := by
  have hd := parallelogram_defect P A (B - A) (D - A)
  rw [hperp, mul_zero] at hd
  have hB : A + (B - A) = B := by abel
  have hD : A + (D - A) = D := by abel
  have hBC : B + (D - A) = C := by rw [hC]; abel
  rw [hB, hD, hBC] at hd
  linarith

end BritishFlagTheoremOQ01OQ01
