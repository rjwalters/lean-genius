/-
Erdős Problem #100, OQ-05, follow-up chain OQ-01 → OQ-01:
An integer-coordinate 4-simplex in ℝ⁴ whose ten edge lengths are ten DISTINCT
positive integers.

Parent problem (Erdős #100): a point set `A` is required to have all pairwise
distances POSITIVE INTEGERS and, in the "restricted-distance" form, all distances
DISTINCT (any two distinct distances differ by ≥ 1).  The parent open question
OQ-05 asks whether the phenomenon changes qualitatively in higher dimensions
ℝ^d for d ≥ 3.

The first follow-up (`Erdos100OQ05OQ01.lean`) answered the d = 3 case: an explicit
integer-coordinate *tetrahedron* (4 points, 6 edges) whose six edge lengths are the
six consecutive integers 6,…,11 — all distinct.  This file pushes the theme one
dimension further, to d = 4.

We exhibit the explicit five-point set

    P₀ = (0,0,0,0), P₁ = (0,2,4,4), P₂ = (4,1,0,8),
    P₃ = (8,4,0,8), P₄ = (12,9,8,0)                         ⊂ ℤ⁴

whose ten pairwise distances are

    |P₀P₁| = 6,  |P₀P₂| = 9,  |P₀P₃| = 12, |P₀P₄| = 17,
    |P₁P₂| = 7,  |P₁P₃| = 10, |P₁P₄| = 15,
    |P₂P₃| = 5,  |P₂P₄| = 16, |P₃P₄| = 13,

i.e. the ten DISTINCT integers {5, 6, 7, 9, 10, 12, 13, 15, 16, 17}.  In particular:

* all ten distances are positive integers (an integer-distance / "perfect"
  4-simplex with integer coordinates);
* all ten distances are pairwise DISTINCT, so the configuration meets the genuine
  restricted-distance hypothesis of Erdős #100 in four dimensions;
* the simplex is non-degenerate: the four edge vectors out of `P₀` have
  determinant `-768 ≠ 0`, so the five points are genuinely 4-dimensional and
  affinely independent (they do not lie in any hyperplane).

Together with the d = 3 example, this shows the distinct-integer-distance
construction persists into ℝ⁴, and the same recipe (place a new vertex off the
current hyperplane at integer distance from all existing vertices) evidently
continues into higher dimensions — the parent's "does the problem change
qualitatively in d ≥ 3" is answered on the *existence* side by an unbroken family
of full-dimensional distinct-integer-distance simplices.

Reference: https://erdosproblems.com/100

**Status**: fully verified (0 sorries, 0 axioms, no `native_decide`).  The parent
diameter conjecture itself remains OPEN.
-/

import Mathlib

open scoped BigOperators

namespace Erdos100OQ05OQ01OQ01

/-! ## The five vertices -/

/-- The five vertices of the 4-simplex, in `EuclideanSpace ℝ (Fin 4)`. -/
def P0 : EuclideanSpace ℝ (Fin 4) := !₂[0, 0, 0, 0]
def P1 : EuclideanSpace ℝ (Fin 4) := !₂[0, 2, 4, 4]
def P2 : EuclideanSpace ℝ (Fin 4) := !₂[4, 1, 0, 8]
def P3 : EuclideanSpace ℝ (Fin 4) := !₂[8, 4, 0, 8]
def P4 : EuclideanSpace ℝ (Fin 4) := !₂[12, 9, 8, 0]

/-! ## Part 1: the ten pairwise distances are ten distinct positive integers -/

theorem dist_P0_P1 : dist P0 P1 = 6 := by
  rw [P0, P1, EuclideanSpace.dist_eq, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Real.dist_eq]
  rw [show |(0:ℝ) - 0| ^ 2 + |(0:ℝ) - 2| ^ 2 + |(0:ℝ) - 4| ^ 2 + |(0:ℝ) - 4| ^ 2 = 6 ^ 2 by
    norm_num, Real.sqrt_sq (by norm_num)]

theorem dist_P0_P2 : dist P0 P2 = 9 := by
  rw [P0, P2, EuclideanSpace.dist_eq, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Real.dist_eq]
  rw [show |(0:ℝ) - 4| ^ 2 + |(0:ℝ) - 1| ^ 2 + |(0:ℝ) - 0| ^ 2 + |(0:ℝ) - 8| ^ 2 = 9 ^ 2 by
    norm_num, Real.sqrt_sq (by norm_num)]

theorem dist_P0_P3 : dist P0 P3 = 12 := by
  rw [P0, P3, EuclideanSpace.dist_eq, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Real.dist_eq]
  rw [show |(0:ℝ) - 8| ^ 2 + |(0:ℝ) - 4| ^ 2 + |(0:ℝ) - 0| ^ 2 + |(0:ℝ) - 8| ^ 2 = 12 ^ 2 by
    norm_num, Real.sqrt_sq (by norm_num)]

theorem dist_P0_P4 : dist P0 P4 = 17 := by
  rw [P0, P4, EuclideanSpace.dist_eq, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Real.dist_eq]
  rw [show |(0:ℝ) - 12| ^ 2 + |(0:ℝ) - 9| ^ 2 + |(0:ℝ) - 8| ^ 2 + |(0:ℝ) - 0| ^ 2 = 17 ^ 2 by
    norm_num, Real.sqrt_sq (by norm_num)]

theorem dist_P1_P2 : dist P1 P2 = 7 := by
  rw [P1, P2, EuclideanSpace.dist_eq, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Real.dist_eq]
  rw [show |(0:ℝ) - 4| ^ 2 + |(2:ℝ) - 1| ^ 2 + |(4:ℝ) - 0| ^ 2 + |(4:ℝ) - 8| ^ 2 = 7 ^ 2 by
    norm_num, Real.sqrt_sq (by norm_num)]

theorem dist_P1_P3 : dist P1 P3 = 10 := by
  rw [P1, P3, EuclideanSpace.dist_eq, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Real.dist_eq]
  rw [show |(0:ℝ) - 8| ^ 2 + |(2:ℝ) - 4| ^ 2 + |(4:ℝ) - 0| ^ 2 + |(4:ℝ) - 8| ^ 2 = 10 ^ 2 by
    norm_num, Real.sqrt_sq (by norm_num)]

theorem dist_P1_P4 : dist P1 P4 = 15 := by
  rw [P1, P4, EuclideanSpace.dist_eq, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Real.dist_eq]
  rw [show |(0:ℝ) - 12| ^ 2 + |(2:ℝ) - 9| ^ 2 + |(4:ℝ) - 8| ^ 2 + |(4:ℝ) - 0| ^ 2 = 15 ^ 2 by
    norm_num, Real.sqrt_sq (by norm_num)]

theorem dist_P2_P3 : dist P2 P3 = 5 := by
  rw [P2, P3, EuclideanSpace.dist_eq, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Real.dist_eq]
  rw [show |(4:ℝ) - 8| ^ 2 + |(1:ℝ) - 4| ^ 2 + |(0:ℝ) - 0| ^ 2 + |(8:ℝ) - 8| ^ 2 = 5 ^ 2 by
    norm_num, Real.sqrt_sq (by norm_num)]

theorem dist_P2_P4 : dist P2 P4 = 16 := by
  rw [P2, P4, EuclideanSpace.dist_eq, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Real.dist_eq]
  rw [show |(4:ℝ) - 12| ^ 2 + |(1:ℝ) - 9| ^ 2 + |(0:ℝ) - 8| ^ 2 + |(8:ℝ) - 0| ^ 2 = 16 ^ 2 by
    norm_num, Real.sqrt_sq (by norm_num)]

theorem dist_P3_P4 : dist P3 P4 = 13 := by
  rw [P3, P4, EuclideanSpace.dist_eq, Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Real.dist_eq]
  rw [show |(8:ℝ) - 12| ^ 2 + |(4:ℝ) - 9| ^ 2 + |(0:ℝ) - 8| ^ 2 + |(8:ℝ) - 0| ^ 2 = 13 ^ 2 by
    norm_num, Real.sqrt_sq (by norm_num)]

/-- **All ten pairwise distances are positive integers.** -/
theorem all_distances_integer :
    dist P0 P1 = 6 ∧ dist P0 P2 = 9 ∧ dist P0 P3 = 12 ∧ dist P0 P4 = 17 ∧
    dist P1 P2 = 7 ∧ dist P1 P3 = 10 ∧ dist P1 P4 = 15 ∧
    dist P2 P3 = 5 ∧ dist P2 P4 = 16 ∧ dist P3 P4 = 13 :=
  ⟨dist_P0_P1, dist_P0_P2, dist_P0_P3, dist_P0_P4, dist_P1_P2, dist_P1_P3,
    dist_P1_P4, dist_P2_P3, dist_P2_P4, dist_P3_P4⟩

/-! ## Part 2: the ten distances are pairwise DISTINCT

We record this in three equivalent ways: as the underlying set of ten distinct
numerals, as a `card = 10` count, and as a `List.Nodup` fact. -/

/-- The ten pairwise distances, as a `Finset ℝ`, are exactly the ten distinct
integers `{5, 6, 7, 9, 10, 12, 13, 15, 16, 17}`. -/
theorem distance_set_eq :
    ({dist P0 P1, dist P0 P2, dist P0 P3, dist P0 P4, dist P1 P2, dist P1 P3,
        dist P1 P4, dist P2 P3, dist P2 P4, dist P3 P4} : Finset ℝ) =
      {6, 9, 12, 17, 7, 10, 15, 5, 16, 13} := by
  rw [dist_P0_P1, dist_P0_P2, dist_P0_P3, dist_P0_P4, dist_P1_P2, dist_P1_P3,
    dist_P1_P4, dist_P2_P3, dist_P2_P4, dist_P3_P4]

/-- **All ten pairwise distances are distinct**, phrased as a cardinality: the
`Finset` of the ten distances has exactly ten elements, so no two edges of the
simplex have equal length. -/
theorem distances_card_ten :
    ({dist P0 P1, dist P0 P2, dist P0 P3, dist P0 P4, dist P1 P2, dist P1 P3,
        dist P1 P4, dist P2 P3, dist P2 P4, dist P3 P4} : Finset ℝ).card = 10 := by
  rw [distance_set_eq]
  norm_num

/-- The ten pairwise distances, listed, have no repeats. -/
theorem distances_nodup :
    ([dist P0 P1, dist P0 P2, dist P0 P3, dist P0 P4, dist P1 P2, dist P1 P3,
        dist P1 P4, dist P2 P3, dist P2 P4, dist P3 P4] : List ℝ).Nodup := by
  rw [dist_P0_P1, dist_P0_P2, dist_P0_P3, dist_P0_P4, dist_P1_P2, dist_P1_P3,
    dist_P1_P4, dist_P2_P3, dist_P2_P4, dist_P3_P4]
  norm_num [List.nodup_cons]

/-- The five vertices are pairwise distinct (immediate from the positive
distances). -/
theorem vertices_distinct :
    P0 ≠ P1 ∧ P0 ≠ P2 ∧ P0 ≠ P3 ∧ P0 ≠ P4 ∧ P1 ≠ P2 ∧ P1 ≠ P3 ∧ P1 ≠ P4 ∧
    P2 ≠ P3 ∧ P2 ≠ P4 ∧ P3 ≠ P4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro h <;>
    first
      | (have := dist_P0_P1; rw [h, dist_self] at this; norm_num at this)
      | (have := dist_P0_P2; rw [h, dist_self] at this; norm_num at this)
      | (have := dist_P0_P3; rw [h, dist_self] at this; norm_num at this)
      | (have := dist_P0_P4; rw [h, dist_self] at this; norm_num at this)
      | (have := dist_P1_P2; rw [h, dist_self] at this; norm_num at this)
      | (have := dist_P1_P3; rw [h, dist_self] at this; norm_num at this)
      | (have := dist_P1_P4; rw [h, dist_self] at this; norm_num at this)
      | (have := dist_P2_P3; rw [h, dist_self] at this; norm_num at this)
      | (have := dist_P2_P4; rw [h, dist_self] at this; norm_num at this)
      | (have := dist_P3_P4; rw [h, dist_self] at this; norm_num at this)

/-! ## Part 3: non-degeneracy — the simplex is genuinely 4-dimensional

The four edge vectors out of `P₀` are
  `v₁ = P₁ - P₀ = (0,2,4,4)`, `v₂ = P₂ - P₀ = (4,1,0,8)`,
  `v₃ = P₃ - P₀ = (8,4,0,8)`, `v₄ = P₄ - P₀ = (12,9,8,0)`.
Their `4 × 4` coordinate matrix has determinant `-768 ≠ 0`, so the vectors are
linearly independent and the five points are affinely independent (not contained
in any hyperplane of ℝ⁴). -/

/-- The matrix whose rows are the four edge vectors of the simplex. -/
def edgeMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 2, 4, 4;
     4, 1, 0, 8;
     8, 4, 0, 8;
     12, 9, 8, 0]

/-- The edge matrix has determinant `-768`, in particular nonzero.  (Since Mathlib
provides an explicit closed form only up to `3 × 3`, we expand the top row via
`Matrix.det_succ_row_zero` and evaluate the four `3 × 3` minors with
`Matrix.det_fin_three`.) -/
theorem edgeMatrix_det : edgeMatrix.det = -768 := by
  rw [edgeMatrix, Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Fin.succAbove, Fin.castSucc, Fin.castAdd,
    Fin.castLE, Fin.lt_def, Fin.succ]
  norm_num

/-- **Non-degeneracy.**  The four edge vectors of the simplex are linearly
independent; equivalently, the five points span a 4-dimensional affine subspace and
are therefore not contained in any hyperplane.  Together with `distances_card_ten`
this gives a full-dimensional integer-coordinate point set in ℝ⁴ all of whose
pairwise distances are *distinct* integers — the restricted-distance regime of
Erdős #100, now realized in four dimensions. -/
theorem edges_linearIndependent : LinearIndependent ℝ (fun i ↦ edgeMatrix i) :=
  Matrix.linearIndependent_rows_of_det_ne_zero (by rw [edgeMatrix_det]; norm_num)

end Erdos100OQ05OQ01OQ01
