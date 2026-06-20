import Mathlib

/-
# The equality case of the triangle inequality in strictly convex spaces

The triangle inequality `‖x + y‖ ≤ ‖x‖ + ‖y‖` is an equality in a general normed
space for many "degenerate" reasons.  In a *strictly convex* normed space the
equality case is completely rigid: it holds **iff** the two vectors point along a
common ray (`SameRay ℝ x y`), i.e. one is a non-negative scalar multiple of the
other.  Metrically this is the statement that the triangle through three points
`a`, `b`, `c` degenerates (`dist a b + dist b c = dist a c`) exactly when the middle
point `b` lies on the segment `[a, c]`.

This file packages the strictly-convex equality case in both its vectorial
(`SameRay`) and metric (`Wbtw` / `segment`) forms, records the rigidity corollary
for equal-norm vectors, and specialises everything to the real line and the
Euclidean plane, which are strictly convex because they carry an inner product.

The vehicles are Mathlib's
`sameRay_iff_norm_add`, `not_sameRay_iff_norm_add_lt`,
`eq_of_norm_eq_of_norm_add_eq` (`Mathlib/Analysis/Convex/StrictConvexSpace.lean`)
and `dist_add_dist_eq_iff` (`Mathlib/Analysis/Convex/StrictConvexBetween.lean`),
glued to `mem_segment_iff_wbtw`.  Everything is `0`-axiom.

This is distinct from the inner-product equality case `norm_add_eq_iff_proportional`
(gallery `cauchy-schwarz-integral-oq-02`): the results below hold in *any* strictly
convex space, with no inner product, and add the betweenness / segment form
(meta open question #3 for `triangle-inequality`).
-/

namespace TriangleInequalityOQ05

open scoped Convex

/-! ## Vectorial form: equality ⇔ same ray -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]

/-- **Equality case of the triangle inequality.**  In a strictly convex space the
norm of a sum reaches the bound `‖x‖ + ‖y‖` exactly when `x` and `y` point along a
common ray. -/
theorem norm_add_eq_iff_sameRay (x y : E) :
    ‖x + y‖ = ‖x‖ + ‖y‖ ↔ SameRay ℝ x y :=
  sameRay_iff_norm_add.symm

/-- **Strict triangle inequality.**  Off the diagonal (when `x`, `y` are not on a
common ray) the inequality is strict. -/
theorem norm_add_lt_iff_not_sameRay (x y : E) :
    ‖x + y‖ < ‖x‖ + ‖y‖ ↔ ¬ SameRay ℝ x y :=
  not_sameRay_iff_norm_add_lt.symm

/-- **Rigidity.**  Two vectors of equal norm that saturate the triangle inequality
must be equal: the only way `‖x + y‖ = 2‖x‖` is `x = y`. -/
theorem eq_of_norm_eq_of_norm_add_eq {x y : E} (h₁ : ‖x‖ = ‖y‖)
    (h₂ : ‖x + y‖ = ‖x‖ + ‖y‖) : x = y :=
  _root_.eq_of_norm_eq_of_norm_add_eq h₁ h₂

/-! ## Metric form: equality ⇔ betweenness -/

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [StrictConvexSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- **Metric characterisation of betweenness.**  In a strictly convex space the
triangle inequality `dist a b + dist b c ≥ dist a c` collapses to an equality
exactly when the middle point `b` lies (weakly) between `a` and `c`. -/
theorem dist_add_dist_eq_iff_wbtw (a b c : P) :
    dist a b + dist b c = dist a c ↔ Wbtw ℝ a b c :=
  dist_add_dist_eq_iff

/-- **Segment form.**  Inside the vector space itself, the degenerate triangle
equality holds iff `b` is a convex combination of `a` and `c`. -/
theorem dist_add_dist_eq_iff_mem_segment (a b c : V) :
    dist a b + dist b c = dist a c ↔ b ∈ segment ℝ a c := by
  rw [dist_add_dist_eq_iff, mem_segment_iff_wbtw]

/-! ## Concrete instances

The real line and the Euclidean plane are strictly convex because they carry an
inner product (inner-product spaces are uniformly, hence strictly, convex), so the
abstract results apply verbatim. -/

/-- On the real line, `|x + y| = |x| + |y|` iff `x` and `y` have the same sign
(`SameRay ℝ x y`). -/
example (x y : ℝ) : ‖x + y‖ = ‖x‖ + ‖y‖ ↔ SameRay ℝ x y :=
  norm_add_eq_iff_sameRay x y

/-- In the Euclidean plane, the triangle through `a`, `b`, `c` is degenerate iff
`b` is between `a` and `c`. -/
example (a b c : EuclideanSpace ℝ (Fin 2)) :
    dist a b + dist b c = dist a c ↔ Wbtw ℝ a b c :=
  dist_add_dist_eq_iff_wbtw a b c

/-- In the Euclidean plane, two distinct unit vectors never saturate the triangle
inequality: `‖x + y‖ < 2` whenever `‖x‖ = ‖y‖ = 1` and `x ≠ y`. -/
example {x y : EuclideanSpace ℝ (Fin 2)} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y) :
    ‖x + y‖ < ‖x‖ + ‖y‖ := by
  rw [norm_add_lt_iff_not_sameRay]
  intro h
  exact hxy (eq_of_norm_eq_of_norm_add_eq (hx.trans hy.symm) (sameRay_iff_norm_add.mp h))

end TriangleInequalityOQ05
