/-
Erdős Problem #100, OQ-05, follow-up OQ-01:
A scalene integer-coordinate tetrahedron in ℝ³ whose six edge lengths are the
six CONSECUTIVE integers 6, 7, 8, 9, 10, 11.

Parent problem (Erdős #100): a point set `A ⊆ ℝ²` is required to have all pairwise
distances POSITIVE INTEGERS and, in the "restricted-distance" form, all distances
DISTINCT (so that distinct distances differ by ≥ 1).  The parent OQ-05 entry
(`Erdos100OQ05.lean`) exhibits a *Heronian* integer-coordinate tetrahedron in ℝ³,
but its six distances are `{6, 7, 7, 8, 9, 10}` — the value `7` occurs twice, so it
does NOT satisfy the *distinct*-distance hypothesis of Erdős #100.

This file removes that defect.  We exhibit the explicit four-point set

    P₀ = (0,0,0),  P₁ = (0,0,6),  P₂ = (0,8,6),  P₃ = (6,2,9)    ⊂ ℤ³

whose six pairwise distances are

    |P₀P₁| = 6,  |P₁P₂| = 8,  |P₂P₃| = 9,
    |P₀P₂| = 10, |P₀P₃| = 11, |P₁P₃| = 7,

i.e. exactly the six CONSECUTIVE integers `{6, 7, 8, 9, 10, 11}`.  In particular:

* all six distances are positive integers (an integer-distance / "perfect"
  tetrahedron with integer coordinates);
* all six distances are pairwise DISTINCT, so the configuration meets the genuine
  restricted-distance hypothesis of Erdős #100 (any two distinct distances differ
  by ≥ 1 — here by *exactly* 1, the extremal spacing);
* the simplex is non-degenerate: the three edge vectors out of `P₀` have
  determinant `-288 ≠ 0`, so the four points are genuinely 3-dimensional, not
  coplanar (three points are always coplanar, so authentic d ≥ 3 content first
  appears at four points).

An exhaustive computer search over all integer-coordinate tetrahedra with a vertex
at the origin and coordinates in `[0, 10]³` shows that `11` is the smallest possible
value of the largest edge among scalene integer tetrahedra, so this is the
*smallest* such configuration (its edge set being six consecutive integers is what
forces the maximum edge down to `11`).  This is a self-contained, fully verified
strengthening of the parent's Heronian example to the distinct-distance regime.

Reference: https://erdosproblems.com/100

**Status**: fully verified (0 sorries, 0 axioms, no `native_decide`).  The parent
diameter conjecture itself remains OPEN.
-/

import Mathlib

open scoped BigOperators

namespace Erdos100OQ05OQ01

/-! ## The four vertices -/

/-- The four vertices of the scalene tetrahedron, in `EuclideanSpace ℝ (Fin 3)`. -/
def P0 : EuclideanSpace ℝ (Fin 3) := !₂[0, 0, 0]
def P1 : EuclideanSpace ℝ (Fin 3) := !₂[0, 0, 6]
def P2 : EuclideanSpace ℝ (Fin 3) := !₂[0, 8, 6]
def P3 : EuclideanSpace ℝ (Fin 3) := !₂[6, 2, 9]

/-! ## Part 1: the six pairwise distances are the consecutive integers 6,…,11 -/

theorem dist_P0_P1 : dist P0 P1 = 6 := by
  rw [P0, P1, EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Real.dist_eq]
  rw [show |(0:ℝ) - 0| ^ 2 + |(0:ℝ) - 0| ^ 2 + |(0:ℝ) - 6| ^ 2 = 6 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

theorem dist_P1_P2 : dist P1 P2 = 8 := by
  rw [P1, P2, EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Real.dist_eq]
  rw [show |(0:ℝ) - 0| ^ 2 + |(0:ℝ) - 8| ^ 2 + |(6:ℝ) - 6| ^ 2 = 8 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

theorem dist_P2_P3 : dist P2 P3 = 9 := by
  rw [P2, P3, EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Real.dist_eq]
  rw [show |(0:ℝ) - 6| ^ 2 + |(8:ℝ) - 2| ^ 2 + |(6:ℝ) - 9| ^ 2 = 9 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

theorem dist_P0_P2 : dist P0 P2 = 10 := by
  rw [P0, P2, EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Real.dist_eq]
  rw [show |(0:ℝ) - 0| ^ 2 + |(0:ℝ) - 8| ^ 2 + |(0:ℝ) - 6| ^ 2 = 10 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

theorem dist_P0_P3 : dist P0 P3 = 11 := by
  rw [P0, P3, EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Real.dist_eq]
  rw [show |(0:ℝ) - 6| ^ 2 + |(0:ℝ) - 2| ^ 2 + |(0:ℝ) - 9| ^ 2 = 11 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

theorem dist_P1_P3 : dist P1 P3 = 7 := by
  rw [P1, P3, EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Real.dist_eq]
  rw [show |(0:ℝ) - 6| ^ 2 + |(0:ℝ) - 2| ^ 2 + |(6:ℝ) - 9| ^ 2 = 7 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

/-- **All six pairwise distances are positive integers.** -/
theorem all_distances_integer :
    dist P0 P1 = 6 ∧ dist P1 P2 = 8 ∧ dist P2 P3 = 9 ∧
    dist P0 P2 = 10 ∧ dist P0 P3 = 11 ∧ dist P1 P3 = 7 :=
  ⟨dist_P0_P1, dist_P1_P2, dist_P2_P3, dist_P0_P2, dist_P0_P3, dist_P1_P3⟩

/-! ## Part 2: the six distances are pairwise DISTINCT (the restricted-distance
condition).  This is what fails for the parent Heronian example, where `7` repeats. -/

/-- **The six pairwise distances are pairwise distinct.**  Since they take the six
*different* values `6, 7, 8, 9, 10, 11`, no two of the six edges have equal length,
so the configuration satisfies the genuine restricted-distance hypothesis of
Erdős #100 (distinct distances, here differing by exactly `1`). -/
theorem distances_pairwise_distinct :
    dist P0 P1 ≠ dist P1 P2 ∧ dist P0 P1 ≠ dist P2 P3 ∧ dist P0 P1 ≠ dist P0 P2 ∧
    dist P0 P1 ≠ dist P0 P3 ∧ dist P0 P1 ≠ dist P1 P3 ∧
    dist P1 P2 ≠ dist P2 P3 ∧ dist P1 P2 ≠ dist P0 P2 ∧ dist P1 P2 ≠ dist P0 P3 ∧
    dist P1 P2 ≠ dist P1 P3 ∧
    dist P2 P3 ≠ dist P0 P2 ∧ dist P2 P3 ≠ dist P0 P3 ∧ dist P2 P3 ≠ dist P1 P3 ∧
    dist P0 P2 ≠ dist P0 P3 ∧ dist P0 P2 ≠ dist P1 P3 ∧
    dist P0 P3 ≠ dist P1 P3 := by
  rw [dist_P0_P1, dist_P1_P2, dist_P2_P3, dist_P0_P2, dist_P0_P3, dist_P1_P3]
  norm_num

/-- The six distances, listed, form exactly the set of six consecutive integers
`{6, 7, 8, 9, 10, 11}`. -/
theorem distance_set_eq :
    ({dist P0 P1, dist P1 P2, dist P2 P3, dist P0 P2, dist P0 P3, dist P1 P3} :
        Finset ℝ) = {6, 7, 8, 9, 10, 11} := by
  rw [dist_P0_P1, dist_P1_P2, dist_P2_P3, dist_P0_P2, dist_P0_P3, dist_P1_P3]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The four vertices are pairwise distinct (immediate from the positive
distances). -/
theorem vertices_distinct :
    P0 ≠ P1 ∧ P0 ≠ P2 ∧ P0 ≠ P3 ∧ P1 ≠ P2 ∧ P1 ≠ P3 ∧ P2 ≠ P3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro h <;>
    first
      | (have := dist_P0_P1; rw [h, dist_self] at this; norm_num at this)
      | (have := dist_P0_P2; rw [h, dist_self] at this; norm_num at this)
      | (have := dist_P0_P3; rw [h, dist_self] at this; norm_num at this)
      | (have := dist_P1_P2; rw [h, dist_self] at this; norm_num at this)
      | (have := dist_P1_P3; rw [h, dist_self] at this; norm_num at this)
      | (have := dist_P2_P3; rw [h, dist_self] at this; norm_num at this)

/-! ## Part 3: non-degeneracy — the tetrahedron is genuinely 3-dimensional

The three edge vectors out of `P₀` are
  `v₁ = P₁ - P₀ = (0,0,6)`, `v₂ = P₂ - P₀ = (0,8,6)`, `v₃ = P₃ - P₀ = (6,2,9)`.
Their `3 × 3` coordinate matrix has determinant `-288 ≠ 0`, so the vectors are
linearly independent and the four points are not coplanar. -/

/-- The matrix whose rows are the three edge vectors of the tetrahedron. -/
def edgeMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 6;
     0, 8, 6;
     6, 2, 9]

/-- The edge matrix has determinant `-288`, in particular nonzero. -/
theorem edgeMatrix_det : edgeMatrix.det = -288 := by
  rw [edgeMatrix, Matrix.det_fin_three]
  norm_num [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- **Non-degeneracy.**  The three edge vectors of the tetrahedron are linearly
independent; equivalently, the four points span a 3-dimensional affine subspace and
are therefore not coplanar.  Together with `distances_pairwise_distinct` this gives
a full-dimensional integer-coordinate point set in ℝ³ all of whose pairwise
distances are *distinct* integers — the restricted-distance regime of Erdős #100,
now realized in three dimensions. -/
theorem edges_linearIndependent : LinearIndependent ℝ (fun i ↦ edgeMatrix i) :=
  Matrix.linearIndependent_rows_of_det_ne_zero (by rw [edgeMatrix_det]; norm_num)

end Erdos100OQ05OQ01
