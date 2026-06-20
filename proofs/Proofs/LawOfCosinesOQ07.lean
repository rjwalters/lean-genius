/-
Law of Cosines OQ-07: Apollonius's Theorem (the Median Length Formula)

For a triangle with vertices `a, b, c` in a real inner-product (Euclidean) affine
space, **Apollonius's theorem** relates the two sides through the vertex `a` to the
median from `a` to the midpoint `m` of the opposite side `bc`:

    |ab|² + |ac|² = 2·(|am|² + (|bc|/2)²).

Equivalently, the squared median length is

    |am|² = (2|ab|² + 2|ac|² − |bc|²) / 4.

This is the affine/Euclidean-geometry counterpart of the parallelogram law and a
direct consequence of the law of cosines applied to the supplementary angles at the
midpoint (`∠ a m b + ∠ a m c = π`). Mathlib proves the identity as
`EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq`
but the gallery did not yet expose it; here it is packaged with the explicit
median-length corollary and the parallelogram-law reading.

Main results:
  • `apollonius_theorem`      — |ab|² + |ac|² = 2·(|am|² + (|bc|/2)²).
  • `median_length_sq`        — |am|² = (2|ab|² + 2|ac|² − |bc|²)/4 (classical median formula).
  • `sum_sq_sides_eq`         — |ab|² + |ac|² = 2|am|² + |bc|²/2 (cleared denominators).

All proofs are `sorry`-free and axiom-free (pure Mathlib geometry, no `native_decide`).

References:
- Apollonius of Perga; the median-length / Stewart's-theorem circle of identities.
- Mathlib `EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq`
  (Geometry/Euclidean/Triangle.lean).
- Sibling entry `law-of-cosines-oq-04` (scalar median-length identity, no points/midpoint).
-/

import Mathlib

namespace LawOfCosinesOQ07

open EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- **Apollonius's Theorem.** For vertices `a, b, c` of a triangle, the sum of the
    squares of the two sides at `a` equals twice the square of the median to the
    midpoint of `bc` plus twice the square of half the third side. -/
theorem apollonius_theorem (a b c : P) :
    dist a b ^ 2 + dist a c ^ 2 = 2 * (dist a (midpoint ℝ b c) ^ 2 + (dist b c / 2) ^ 2) :=
  dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq a b c

/-- **Median length formula.** The square of the median from `a` to the midpoint of
    `bc` is `(2|ab|² + 2|ac|² − |bc|²)/4`. Solved directly from Apollonius's theorem. -/
theorem median_length_sq (a b c : P) :
    dist a (midpoint ℝ b c) ^ 2 = (2 * dist a b ^ 2 + 2 * dist a c ^ 2 - dist b c ^ 2) / 4 := by
  have h := apollonius_theorem a b c
  have hbc : (dist b c / 2) ^ 2 = dist b c ^ 2 / 4 := by ring
  rw [hbc] at h
  linarith

/-- Cleared-denominator form: `|ab|² + |ac|² = 2|am|² + |bc|²/2`. -/
theorem sum_sq_sides_eq (a b c : P) :
    dist a b ^ 2 + dist a c ^ 2 = 2 * dist a (midpoint ℝ b c) ^ 2 + dist b c ^ 2 / 2 := by
  have h := apollonius_theorem a b c
  have hbc : (dist b c / 2) ^ 2 = dist b c ^ 2 / 4 := by ring
  rw [hbc] at h
  linarith

#check @apollonius_theorem
#check @median_length_sq
#check @sum_sq_sides_eq

end LawOfCosinesOQ07
