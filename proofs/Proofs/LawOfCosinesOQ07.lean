import Mathlib

/-
# Law of Cosines — OQ-07: Apollonius's Theorem (metric / median form) and the Parallelogram Law

## Research Problem: law-of-cosines-oq-07

OQ: State and prove **Apollonius's theorem** in its coordinate-free metric form,
in an arbitrary real inner-product affine space, and derive the parallelogram
law from it.

Apollonius's theorem (median identity): for points `a b c` of a Euclidean
affine space,

    dist a b ² + dist a c ² = 2 · (dist a (midpoint ℝ b c) ² + (dist b c / 2)²)

i.e. the sum of the squares of two sides of a triangle equals twice the square
of the median to the third side plus twice the square of half that side.

This is a *coordinate-free* statement: the objects are genuine points `a b c`
of a `NormedAddTorsor` over a real inner product space, and `midpoint ℝ b c` is
the actual midpoint of the segment `[b, c]`.

DISTINCT from `law-of-cosines-oq-04` (`median_length_formula`), which is a
**scalar** identity in ℝ-valued side lengths `a b c d : ℝ` derived from
Stewart's algebraic identity. Here nothing is parameterised by scalar side
lengths — the theorem speaks directly about points and midpoints, and the
parallelogram law drops out as a vector-space special case.

We package three results:
  1. `apollonius`         — the median identity (the metric Apollonius theorem).
  2. `median_length`      — explicit median length: 4·mₐ² = 2·b² + 2·c² − a².
  3. `parallelogram_law`  — ‖x + y‖² + ‖x − y‖² = 2(‖x‖² + ‖y‖²), derived FROM
                            Apollonius (a parallelogram's diagonals bisect each
                            other, so their crossing is the common midpoint).

Tags: geometry, apollonius, median, parallelogram-law, law-of-cosines
-/

open EuclideanGeometry

namespace LawOfCosinesOQ07

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- **Apollonius's theorem** (metric / median form).

For points `a b c` of a real inner-product affine space, the sum of the squares
of the sides `ab` and `ac` equals twice the square of the median from `a` to the
midpoint of `bc`, plus twice the square of half of `bc`.

This is a thin packaging of `EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_-
dist_midpoint_sq_add_half_dist_sq`, exposed here as a standalone gallery entry. -/
theorem apollonius (a b c : P) :
    dist a b ^ 2 + dist a c ^ 2
      = 2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) :=
  dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq a b c

/-- **Median length formula** (metric form): if `mₐ = dist a (midpoint ℝ b c)`
is the length of the median from `a`, then

    4 · mₐ² = 2 · (dist a b)² + 2 · (dist a c)² − (dist b c)².

A direct rearrangement of `apollonius`. -/
theorem median_length (a b c : P) :
    4 * dist a (midpoint ℝ b c) ^ 2
      = 2 * dist a b ^ 2 + 2 * dist a c ^ 2 - dist b c ^ 2 := by
  have h := apollonius a b c
  linear_combination -2 * h

/-- **Parallelogram law**, derived from Apollonius's theorem.

In a real inner product space, the sum of the squares of the two diagonals of a
parallelogram equals twice the sum of the squares of two adjacent sides:

    ‖x + y‖² + ‖x − y‖² = 2 · (‖x‖² + ‖y‖²).

We obtain it by applying Apollonius to the triangle with vertices `x`, `-y`, `y`
(viewing `V` as a torsor over itself). The diagonals are the sides `dist x (-y)
= ‖x + y‖` and `dist x y = ‖x − y‖`; the midpoint of `[-y, y]` is the origin, so
the median is `‖x‖`, and `dist (-y) y = 2‖y‖`. -/
theorem parallelogram_law (x y : V) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have h := apollonius (P := V) x (-y) y
  have hmid : midpoint ℝ (-y) y = (0 : V) := midpoint_neg_self ℝ y
  rw [hmid] at h
  rw [dist_eq_norm, sub_neg_eq_add] at h          -- dist x (-y) = ‖x + y‖
  rw [dist_eq_norm] at h                           -- dist x y = ‖x - y‖
  rw [dist_eq_norm, sub_zero] at h                 -- dist x 0 = ‖x‖
  rw [dist_eq_norm] at h                           -- dist (-y) y = ‖-y - y‖
  have hy : ‖(-y) - y‖ = 2 * ‖y‖ := by
    rw [show (-y) - y = (-2 : ℝ) • y by module, norm_smul, Real.norm_eq_abs]
    norm_num
  rw [hy] at h
  linear_combination h

/-- Concrete instantiation: the median identity specialises to the Euclidean
plane `EuclideanSpace ℝ (Fin 2)`, confirming the abstract theorem applies to the
standard model of plane geometry. -/
example (a b c : EuclideanSpace ℝ (Fin 2)) :
    dist a b ^ 2 + dist a c ^ 2
      = 2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) :=
  apollonius a b c

end LawOfCosinesOQ07
