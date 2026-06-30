/-
Erdős Problem #100, Open Question 05: Integer-Distance Point Sets in
Higher Dimensions ℝ^d (d ≥ 3)

Parent problem (Erdős #100): if A ⊆ ℝ² has n points with all pairwise distances
positive integers, must its diameter grow like ≫ n?  This file studies the
*qualitative* question for higher dimensions: does the picture change in ℝ^d,
d ≥ 3?

This file contributes two fully verified, self-contained facts.

1. **Full-dimensional integral simplex in ℝ³ exists.**  We exhibit an explicit
   four-point set with INTEGER COORDINATES whose six pairwise distances are all
   positive integers, and whose three edge vectors are linearly independent
   (the simplex is non-degenerate, i.e. genuinely 3-dimensional, *not* a planar
   configuration in disguise).  The points are

       P₀ = (0,0,0),  P₁ = (0,0,6),  P₂ = (0,8,0),  P₃ = (6,2,3),

   with distances

       |P₀P₁| = 6,  |P₀P₂| = 8,  |P₀P₃| = 7,
       |P₁P₂| = 10, |P₁P₃| = 7,  |P₂P₃| = 9.

   This is a *Heronian tetrahedron with integer coordinates*; it shows the
   integer-distance problem is non-vacuous and admits genuinely d-dimensional
   configurations once d ≥ 3 (every triangle is planar, so 3-D content first
   appears at 4 points).

2. **Dimension-uniform collinear family.**  For every dimension d ≥ 1 and every
   n, the n collinear lattice points 0,1,…,n−1 along a coordinate axis of ℝ^d
   have all pairwise distances integers and diameter exactly n−1.  Hence the
   *existence / small-diameter* side of the problem (diameter = O(n) achievable)
   is completely dimension-independent.

**Qualitative answer to OQ-05.**  The problem does *not* trivialize in higher
dimensions:
  * Full-dimensional integral point sets exist in every dimension (fact 1 for
    d = 3; products give all d ≥ 3).
  * The collinear extremal family (fact 2) shows diameter O(n) is achievable in
    every dimension, exactly as in the plane.
  * The naive packing lower bound, however, *weakens* with dimension: n points
    with pairwise distance ≥ 1 inside a ball of diameter D satisfy n ≲ D^d, so
    D ≳ n^{1/d}, an exponent that → 0.  Thus packing alone gives essentially
    nothing in high dimension and the genuine content rests on
    distinct-distance (Guth–Katz-type) machinery, which is itself
    dimension-sensitive.  (This last bound is documented, not formalized here.)

Reference: https://erdosproblems.com/100

**Status**: the two formalized facts are fully verified (0 sorries, 0 axioms).
The parent diameter conjecture itself remains OPEN.
-/

import Mathlib

open scoped BigOperators

namespace Erdos100OQ05

/-! ## Part 1: An explicit full-dimensional integral tetrahedron in ℝ³ -/

/-- The four vertices of the tetrahedron, as elements of `EuclideanSpace ℝ (Fin 3)`. -/
def P0 : EuclideanSpace ℝ (Fin 3) := !₂[0, 0, 0]
def P1 : EuclideanSpace ℝ (Fin 3) := !₂[0, 0, 6]
def P2 : EuclideanSpace ℝ (Fin 3) := !₂[0, 8, 0]
def P3 : EuclideanSpace ℝ (Fin 3) := !₂[6, 2, 3]

/-- A uniform helper: the distance between two explicit points of `ℝ³` whose
coordinates are given numerically equals `√(Σ (differences)²)`, which we then
evaluate to a concrete integer via `Real.sqrt_eq_iff` style reasoning. -/
theorem dist_P0_P1 : dist P0 P1 = 6 := by
  rw [P0, P1, EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Real.dist_eq]
  rw [show |(0:ℝ) - 0| ^ 2 + |(0:ℝ) - 0| ^ 2 + |(0:ℝ) - 6| ^ 2 = 6 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

theorem dist_P0_P2 : dist P0 P2 = 8 := by
  rw [P0, P2, EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Real.dist_eq]
  rw [show |(0:ℝ) - 0| ^ 2 + |(0:ℝ) - 8| ^ 2 + |(0:ℝ) - 0| ^ 2 = 8 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

theorem dist_P0_P3 : dist P0 P3 = 7 := by
  rw [P0, P3, EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Real.dist_eq]
  rw [show |(0:ℝ) - 6| ^ 2 + |(0:ℝ) - 2| ^ 2 + |(0:ℝ) - 3| ^ 2 = 7 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

theorem dist_P1_P2 : dist P1 P2 = 10 := by
  rw [P1, P2, EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Real.dist_eq]
  rw [show |(0:ℝ) - 0| ^ 2 + |(0:ℝ) - 8| ^ 2 + |(6:ℝ) - 0| ^ 2 = 10 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

theorem dist_P1_P3 : dist P1 P3 = 7 := by
  rw [P1, P3, EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Real.dist_eq]
  rw [show |(0:ℝ) - 6| ^ 2 + |(0:ℝ) - 2| ^ 2 + |(6:ℝ) - 3| ^ 2 = 7 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

theorem dist_P2_P3 : dist P2 P3 = 9 := by
  rw [P2, P3, EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Real.dist_eq]
  rw [show |(0:ℝ) - 6| ^ 2 + |(8:ℝ) - 2| ^ 2 + |(0:ℝ) - 3| ^ 2 = 9 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

/-- **All six pairwise distances are positive integers.** -/
theorem all_distances_integer :
    dist P0 P1 = 6 ∧ dist P0 P2 = 8 ∧ dist P0 P3 = 7 ∧
    dist P1 P2 = 10 ∧ dist P1 P3 = 7 ∧ dist P2 P3 = 9 :=
  ⟨dist_P0_P1, dist_P0_P2, dist_P0_P3, dist_P1_P2, dist_P1_P3, dist_P2_P3⟩

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

/-! ### Non-degeneracy: the simplex spans 3 dimensions

The three edge vectors out of `P₀` are
  `v₁ = P₁ - P₀ = (0,0,6)`, `v₂ = P₂ - P₀ = (0,8,0)`, `v₃ = P₃ - P₀ = (6,2,3)`.
Their `3 × 3` coordinate matrix has determinant `-288 ≠ 0`, so the vectors are
linearly independent and the tetrahedron is non-degenerate (it is genuinely
3-dimensional, i.e. the four points are *not* coplanar). -/

/-- The matrix whose rows are the three edge vectors of the tetrahedron. -/
def edgeMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 0, 6;
     0, 8, 0;
     6, 2, 3]

/-- The edge matrix has determinant `-288`, in particular nonzero. -/
theorem edgeMatrix_det : edgeMatrix.det = -288 := by
  rw [edgeMatrix, Matrix.det_fin_three]
  norm_num [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

/-- **Non-degeneracy.**  The three edge vectors of the tetrahedron are linearly
independent; equivalently, the four points span a 3-dimensional affine subspace
and are therefore not coplanar. -/
theorem edges_linearIndependent : LinearIndependent ℝ (fun i ↦ edgeMatrix i) :=
  Matrix.linearIndependent_rows_of_det_ne_zero (by rw [edgeMatrix_det]; norm_num)

/-! ## Part 2: The dimension-uniform collinear family

For any dimension `d ≥ 1` (we use `Fin (d+1)` to keep the index type nonempty)
the points `Q j = j • e₀` for `j = 0,…,n-1` along the first coordinate axis have
all pairwise distances integers and diameter `n − 1`.  This holds verbatim in
every dimension, so the small-diameter side of the problem is
dimension-independent. -/

/-- The `j`-th collinear lattice point along the first coordinate axis of `ℝ^{d+1}`. -/
noncomputable def Q (d : ℕ) (j : ℕ) : EuclideanSpace ℝ (Fin (d + 1)) :=
  (j : ℝ) • EuclideanSpace.single (0 : Fin (d + 1)) (1 : ℝ)

/-- **Integer (indeed integer-valued absolute difference) distances in every
dimension.**  The distance between the `i`-th and `j`-th collinear points is
`|i − j|`, independent of the dimension `d`. -/
theorem Q_dist (d i j : ℕ) : dist (Q d i) (Q d j) = |(i : ℝ) - (j : ℝ)| := by
  rw [Q, Q, dist_eq_norm, ← sub_smul, norm_smul, EuclideanSpace.norm_single]
  simp [Real.norm_eq_abs]

/-- The pairwise distances of the collinear family are natural numbers, hence
integers: `dist (Q d i) (Q d j) = |i - j|` as a cast natural number. -/
theorem Q_dist_natCast (d i j : ℕ) :
    dist (Q d i) (Q d j) = ((max i j - min i j : ℕ) : ℝ) := by
  rw [Q_dist]
  rcases le_total i j with h | h
  · rw [max_eq_right h, min_eq_left h, Nat.cast_sub h, abs_of_nonpos]
    · ring
    · have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast h
      linarith
  · rw [max_eq_left h, min_eq_right h, Nat.cast_sub h, abs_of_nonneg]
    have : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast h
    linarith

/-- The collinear family realises diameter exactly `n − 1`: the extreme points
`Q 0` and `Q (n-1)` are at distance `n − 1` in every dimension. -/
theorem Q_diameter (d n : ℕ) : dist (Q d 0) (Q d (n - 1)) = ((n - 1 : ℕ) : ℝ) := by
  rw [Q_dist]
  simp

end Erdos100OQ05
